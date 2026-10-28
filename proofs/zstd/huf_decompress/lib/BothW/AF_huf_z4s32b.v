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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s32k AF_huf_z4s32a.

Definition C32H2at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91c60) fc None mm (seg_rom bsegs)).

Definition C32H2 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall q : Z, C32H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.

Definition K32X (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> (pt = 0 \/ Qe - q < 2) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91ec4) fc None mm (seg_rom bsegs)).

Definition K32N (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 64 < b < 2^31 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91eb8) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_M2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
    (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 -> K32N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
  0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 ->
  (x10 = Z_to_bv 64 0 /\ pt = 0 \/ x10 = Z_to_bv 64 1) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91d84) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm
    x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31
    C D6 O6 L1 OL HQe KX KN IH FS Hq Hpt HptL Hb Hx.
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
  unfold SPD in SPL. unfold BD4A in B2. unfold C32H2at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct (Z_lt_le_dec (Qe - q) 2) as [HQ2 | HQ2].
  { eapply z4s32_X2; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | left; lia |].
    eapply KX; [exact FS | lia | lia | exact HptL | lia | right; lia]. }
  destruct Hx as [[Hx0 Hp0] | Hx1].
  { subst x10.
    eapply z4s32_X2; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | right; reflexivity |].
    eapply KX; [exact FS | lia | lia | exact HptL | lia | left; exact Hp0]. }
  subst x10.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_B2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x11 x12 x13 x14 x15 x16 x17 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 y12 y13 y14 y15 y16 y17 nb Hnb Hz10 SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                 bd3
                 (BD4A c (Z_to_bv 64 (b + nb)) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply z4s32_C2; [exact SPL' | exact BD2' | exact MI' | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hbn. eapply (IH (q + bv_unsigned z10)); [lia | exact FS' | lia | exact Hpt | exact HptL | lia].
  - intros Hbn. eapply KN; [exact FS' | lia | lia].
Qed.

Section Z32RL.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s32_H2L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 -> K32N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') -> C32H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KX KN IH.
  unfold C32H2at.
  intros pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31
    FS Hq Hpt HptL Hb.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s32_H2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) x23 x24 x18
            (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
            (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hp8 z12.
    eapply (z4_rl_call2 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd1 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s32_RT with (bd3 := @nil cell); [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s32_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | lia | exact KX | exact KN | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | right; reflexivity].
  -
    intros Hp0 z10 z12 z13.
    eapply KX; [exact FS | lia | lia | exact HptL | lia | left; exact Hp0].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | lia | exact KX | exact KN | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | right; reflexivity].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. rewrite Z.add_0_r. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | lia | exact KX | exact KN | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | left; split; reflexivity].
Qed.

Lemma z4s32_L2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 -> K32N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 -> C32H2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KX KN.
  unfold C32H2. intros q.
  remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros q Hn.
  apply (z4s32_H2L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
           src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KX KN).
  intros q' Hq'.
  destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
  - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
  - unfold C32H2at. intros. lia.
Qed.

End Z32RL.

End CANSEC1.

Definition C32H5at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) mm (x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> tl < 12 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x90f24) fc None mm (seg_rom bsegs)).


Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_M5 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
  0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> tl < 12 ->
  (x10 = Z_to_bv 64 0 \/ x10 = Z_to_bv 64 1 /\ b <= 7) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91044) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm
    x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B2. unfold C32H5at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  assert (KJ0 : forall x10' x11' x12' x13' x14' x15' x16' x17' : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10' x11' x12' x13' x14' x15' x16' x17'
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs))).
  { intros. eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]]. }
  destruct (Z_lt_le_dec Qe (q + 10)) as [HQ | HQ].
  { eapply z4s32_X5; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | left; exact HQ |].
    apply KJ0. }
  destruct Hx as [Hx0 | [Hx1 Hb7]].
  { subst x10.
    eapply z4s32_X5; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | right; reflexivity |].
    apply KJ0. }
  subst x10.
  destruct BUF as (ob & OB & OBL).
  assert (HT2 : 2 <= 2^tl <= 2048).
  { split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]. }
  pose proof (z4ctx_dt_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as HDX.
  assert (FLD11 : forall i fl fh, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 11); (3, 1, 2)] = Some (fl, fh) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ fl <= bv_unsigned b <= fh)
    by (intros i fl fh Hi Hf; exact (FLD 11 i fl fh ltac:(lia) Hi Hf)).
  eapply (z4s32_B Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x25 x22 x28 x29
            (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob
            (bv_unsigned sp) DST dcap SS DT q Qe O pt b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 z12 z13 z14 z15 q' bc' Hq' Hbc SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                 bd3
                 (BD4A c (Z_to_bv 64 bc') jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply (IH q'); [lia | exact FS' | lia | exact Hpt | exact HptL | lia | exact Htl].
Qed.

Section Z32RL5.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s32_H5L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') ->
  C32H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KJ IH.
  unfold C32H5at at 1.
  intros pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s32_H5 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9)) x22 (Z_to_bv 64 (64 - tl))
            (Z_to_bv 64 (- DT + -5)) x25 (Z_to_bv 64 (2^61)) x18 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
            (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hp8 z12.
    eapply (z4_rl_call2 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd1 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s32_L5R; [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s32_M5 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  -
    intros Hp0 z10 z12 z13.
    eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_M5 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. rewrite Z.add_0_r. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_M5 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | lia | left; reflexivity].
Qed.

Lemma z4s32_L5 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32H5 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ.
  assert (H : forall q, C32H5at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q).
  { intros q.
    remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros q Hn.
    apply (z4s32_H5L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
             src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KJ).
    intros q' Hq'.
    destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
    - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
    - unfold C32H5at. intros. lia. }
  unfold C32H5. intros q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31.
  exact (H q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x31).
Qed.

End Z32RL5.

End CANSEC1.

Definition C32H4at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) mm (x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> 12 <= tl ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x916c4) fc None mm (seg_rom bsegs)).


Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_M4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
  0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> 12 <= tl ->
  (x10 = Z_to_bv 64 0 \/ x10 = Z_to_bv 64 1 /\ b <= 7) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x917e4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm
    x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B2. unfold C32H4at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  assert (KJ0 : forall x10' x11' x12' x13' x14' x15' x16' x17' : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10' x11' x12' x13' x14' x15' x16' x17'
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs))).
  { intros. eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]]. }
  destruct (Z_lt_le_dec Qe (q + 8)) as [HQ | HQ].
  { eapply z4s32_X4; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | left; exact HQ |].
    apply KJ0. }
  destruct Hx as [Hx0 | [Hx1 Hb7]].
  { subst x10.
    eapply z4s32_X4; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | right; reflexivity |].
    apply KJ0. }
  subst x10.
  destruct BUF as (ob & OB & OBL).
  assert (HT2 : 2 <= 2^tl <= 4096).
  { split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]. }
  pose proof (z4ctx_dt_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as HDX.
  assert (FLD12 : forall i fl fh, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, 12); (3, 1, 2)] = Some (fl, fh) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ fl <= bv_unsigned b <= fh)
    by (intros i fl fh Hi Hf; exact (FLD 12 i fl fh ltac:(lia) Hi Hf)).
  eapply (z4s32_B4 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x12 x27 x22 x28 x29
            (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp cbs ob
            (bv_unsigned sp) DST dcap SS DT q Qe O pt b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 z12 z13 z14 z15 q' bc' Hq' Hbc SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                 bd3
                 (BD4A c (Z_to_bv 64 bc') jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply (IH q'); [lia | exact FS' | lia | exact Hpt | exact HptL | lia | exact Htl].
Qed.

Section Z32RL4.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s32_H4L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') ->
  C32H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KJ IH.
  unfold C32H4at at 1.
  intros pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s32_H4 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -7)) x22 (Z_to_bv 64 (64 - tl))
            x27 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x18 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
            (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hp8 z12.
    eapply (z4_rl_call2 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd1 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s32_L4R; [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s32_M4 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  -
    intros Hp0 z10 z12 z13.
    eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_M4 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | lia
      | right; split; [reflexivity | Z.div_mod_to_equations; lia]].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. rewrite Z.add_0_r. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_M4 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | lia | exact KJ | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | lia | left; reflexivity].
Qed.

Lemma z4s32_L4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  forall q, C32H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ.
  assert (H : forall q, C32H4at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q).
  { intros q.
    remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros q Hn.
    apply (z4s32_H4L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
             src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KJ).
    intros q' Hq'.
    destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
    - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
    - unfold C32H4at. intros. lia. }
  exact H.
Qed.

End Z32RL4.

Section Z32RL4E.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s32_E4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32H4 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ.
  pose proof (z4s32_L4 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ) as KH.
  unfold C32H4.
  intros q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_N4 Q RNG mm FR fc gp tp x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hb64 mm' SPL' BD2' MI' MU' WM'.
    rewrite Z_to_bv_bv_unsigned in BD2'.
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (KH q); [exact FS' | lia | exact Hpt | exact HptL | lia | exact Htl].
  -
    intros Hb64 mm' SPL' BD2' MI' MU' WM'.
    rewrite Z_to_bv_bv_unsigned in BD2'.
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    match type of BD2' with rw_cells _ _ _ [_; _; _; C8 ?pv; _; _] =>
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c (Z_to_bv 64 b) jp pv (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1) end.
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply KJ; [exact FS' | lia | right; lia].
Qed.

End Z32RL4E.

End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.

Section Z32RL.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s32_RL : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32R RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ.
  unfold C32R.
  intros q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s32_RH0 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (DST + q)) x20 x23 x22 x24 x27 x25 (Z_to_bv 64 (2^61)) x18 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hb64.
    eapply (z4s32_RH Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 65) x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (DST + q)) x20 x23 x22 x24 x27 x25 (Z_to_bv 64 (2^61)) x18 x28 x29 (Z_to_bv 64 (DT + 4)) x31
              w0 w1 w4 w5 w7 w8 w9 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
              (bv_unsigned sp) DST dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
    all: try (lazymatch goal with
         | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
         end).
    all: try assumption.
    all: try lia.
    +
      intros Hp8 z12.
      eapply (z4_rl_call2 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd1 O Lk pt b c jp FR fc gp);
        [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
      intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
      rewrite ret_pc_even by first [lia | reflexivity].
      pose proof FS' as FS1.
      destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                       & FRM1 & MI1 & MU1 & WM1).
      unfold SPD in SPL1.
      eapply z4s32_LR; [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
      eapply KJ; [exact FS' | lia | left; split;
        [exists (pt - b / 8); split; [reflexivity | split; [Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia]]
        | Z.div_mod_to_equations; lia]].
    +
      intros Hp0 z10 z12 z14.
      eapply KJ; [exact FS | lia | left; split; [exists pt; split; [reflexivity | split; [lia | exact HptL]] | lia]].
    +
      intros Hp17 Hbp mm' c' z10 z11 z12 z13 z14 z15 SPL' BD2' MI' MU' WM'.
      destruct BUF as (ob & OB & OBL).
      assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                           (DST, DST + dcap)] mm mm').
      { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
      assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                     (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                          (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                     bd3 (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                           (Z_to_bv 64 (SS + O + 8))) bd1).
      { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                  cells cbs pdt SBL SBH rstk mm mm' (-184));
          [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
          | | exact B3S | | apply BD4A_size | | exact B1S].
        - exists ob. split; [| exact OBL].
          eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
        - unfold SPD. exact SPL'.
        - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
        - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
        - unfold BD4A. exact BD2'.
        - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
      eapply KJ; [exact FS' | lia | left; split;
        [exists (pt - b / 8); split; [reflexivity | split; [Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia]]
        | Z.div_mod_to_equations; lia]].
    +
      intros Hp17 Hbp mm' c' z10 z11 z12 z13 z14 z15 SPL' BD2' MI' MU' WM'.
      destruct BUF as (ob & OB & OBL).
      assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                           (DST, DST + dcap)] mm mm').
      { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
      assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                     (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                          (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                     bd3 (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                           (Z_to_bv 64 (SS + O + 8))) bd1).
      { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                  cells cbs pdt SBL SBH rstk mm mm' (-184));
          [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
          | | exact B3S | | apply BD4A_size | | exact B1S].
        - exists ob. split; [| exact OBL].
          eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
        - unfold SPD. exact SPL'.
        - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
        - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
        - unfold BD4A. rewrite Z.add_0_r. exact BD2'.
        - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
      eapply KJ; [exact FS' | lia | left; split;
        [exists 0; split; [reflexivity | split; [lia | left; reflexivity]]
        | Z.div_mod_to_equations; lia]].
  -
    intros Hb64 mm' SPL' BD2' MI' MU' WM'.
    rewrite Z_to_bv_bv_unsigned in BD2'.
    match type of BD2' with
    | context [C8 (Z_to_bv 64 ?v) :: C8 (Z_to_bv 64 (SS + O)) :: _] => set (pl := v) in *
    end.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 pl) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply KJ; [exact FS' | lia | right; lia].
Qed.

End Z32RL.

End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_top :
  (forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
     (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
     (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
     (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
     (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
   z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
   6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
   K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
   C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1) ->
  z4s32_stmtA.
Proof.
  intros HT. unfold z4s32_stmtA.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe C D6 O6 L1 OL HQe.
  unfold z4s32_goal.
  intros q pt b c jp w0 w1 w4 w5 w7 w8 w9 w11 bd4 bd3 bd1 mm
    x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS Hq Hpt HptL Hb K.
  assert (KS : K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo src cbs Q O Lk Qe
                 w1 x9 x18 bd4 bd3 bd1) by (unfold K32S3; exact K).
  pose proof (HT Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS) as KJ.
  pose proof huf_reload_int_proofA as HRL.
  pose proof (z4s32_L5 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ) as KH5.
  pose proof (z4s32_E4 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ) as KH4.
  pose proof (z4s32_RL HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KJ) as KR.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_E Q RNG mm FR fc gp tp x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x22 x24 x27 x25 x18 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 jp (bv_unsigned sp) DST dcap SSa DT q Qe O Lk pt b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       end).
  all: try assumption.
  all: try lia.
  1: intros HC mm' SPL' BD2' MI' MU' WM'.
  2: intros HC HC2 mm' SPL' BD2' MI' MU' WM'.
  3, 4: intros HC HC2 HC3 mm' SPL' BD2' MI' MU' WM'.
  all: rewrite ?Z_to_bv_bv_unsigned in BD2'.
  all: assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                            (DST, DST + dcap)] mm mm')
         by (eapply munch_weaken; [| exact MU']; intros x HX; cbn [outside] in *; repeat split; try exact I; intros ?; lia).
  all: match type of BD2' with rw_cells _ _ _ [_; _; _; C8 ?pv; C8 ?sv; C8 ?lv] =>
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SSa DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                   bd3 (BD4A c (Z_to_bv 64 b) jp pv sv lv) bd1) end.
  all: try (eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SSa DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S];
      [ exists ob; split; [| exact OBL];
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]; rewrite length_map; cbn [disjoint_from]; lia
      | unfold SPD; exact SPL'
      | eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]; rewrite B4S; cbn [disjoint_from]; lia
      | eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]; rewrite B3S; cbn [disjoint_from]; lia
      | unfold BD4A; exact BD2'
      | eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]; rewrite B1S; cbn [disjoint_from]; lia ]).
  -
    eapply KR; [exact FS' | lia | lia | exact Hpt | exact HptL | lia].
  -
    eapply KH4; [exact FS' | lia | lia | exact Hpt | exact HptL | lia | lia].
  -
    eapply (KH5 q pt b c jp w0 w4 w5 w7 w8 w9 w11 mm' _ _ _ _ _ x1 _ _ _ _ _ _ x1 _ x1 x1 _ x1 _ _ _);
      [exact FS' | lia | exact Hpt | exact HptL | lia | lia].
  -
    eapply KJ; [exact FS' | lia | right; lia].
Qed.

End CANSEC1.

Definition K32L (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q : Z) (b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> Qe < q + 2 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91ec8) fc None mm (seg_rom bsegs)).

Definition C32Bat (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z) : Prop :=
  forall (b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q -> q + 2 <= Qe -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91f8c) fc None mm (seg_rom bsegs)).

Definition C32B (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall q : Z, C32Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.

Definition C32T (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q : Z) (b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91ec4) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_NLs : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  (forall q', q < q' -> C32Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q') ->
  C32Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KL IH.
  unfold C32Bat.
  intros b c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 FS Hq Hq2 Hb.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  unfold C32Bat in IH.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_NB Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 y11 y12 y13 y14 y15 y16 y17 b' Hz10 SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  apply z4s32_c4mod in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                 bd3 (BD4A c (Z_to_bv 64 (b' mod 2^32)) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  pose proof (Z.mod_pos_bound b' (2^32) ltac:(lia)) as HBM.
  eapply (z4s32_BR2 Q RNG mm' FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 z10 y11 y12 y13 y14 y15 y16 y17 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 (bv_unsigned sp) DST dcap DT (q + bv_unsigned z10) Qe tl mtl);
    [exact SPL' | exact MI' | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hc. eapply (IH (q + bv_unsigned z10)); [lia | exact FS' | lia | lia | exact HBM].
  - intros Hc. eapply KL; [exact FS' | lia | lia | exact HBM].
Qed.

Lemma z4s32_NL : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32B RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL.
  unfold C32B. intros q.
  remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros q Hn.
  apply (z4s32_NLs Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 q C D6 O6 L1 OL HQe KL).
  intros q' Hq'.
  destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
  - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
  - unfold C32Bat. intros. lia.
Qed.

Lemma z4s32_T : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32T RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL.
  pose proof (z4s32_NL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL) as NL.
  unfold C32B, C32Bat in NL.
  unfold C32T.
  intros q b c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 FS Hq Hb.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s32_BR1 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 (bv_unsigned sp) DST dcap DT q Qe tl mtl);
    [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hc. eapply NL; [exact FS | lia | lia | exact Hb].
  - intros Hc. eapply KL; [exact FS | lia | lia | exact Hb].
Qed.

Lemma z4s32_KX : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL.
  pose proof (z4s32_T Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL) as T.
  unfold C32T in T.
  unfold K32X. intros.
  eapply T; [eassumption | lia | lia].
Qed.

Lemma z4s32_KN : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL.
  pose proof (z4s32_T Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL) as T.
  unfold C32T in T.
  unfold K32N.
  intros q b c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x27 x28 x29 x31 FS Hq Hb.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s32_TN Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 c p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp (bv_unsigned sp) DST dcap DT q Qe b tl mtl);
    [exact SPL | exact B2 | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia |].
  intros mm' SPL' BD2' MI' MU' WM'.
  destruct BUF as (ob & OB & OBL).
  assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -184, bv_unsigned sp + -184 + 40);
                       (DST, DST + dcap)] mm mm').
  { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
                 bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 0x20e00) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' |  | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - exists ob. split; [| exact OBL].
      eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply T; [exact FS' | lia | lia].
Qed.

End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_LSd : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  forall (q b v : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q -> q + 1 = Qe -> 0 <= v < 128 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 v) (Z_to_bv 64 64) x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x920c4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS q b v c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS Hq HQ1 HV Hb.
  unfold K32S3 in KS.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_LD Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x1 x1 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap v).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  intros mm' y10 y11 y12 y13 b' SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b') jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply KS. exact FS'.
Qed.

Lemma z4s32_LSc : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  forall (q b i len : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> 1 <= len <= 2 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 len) (Z_to_bv 64 1) x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91f5c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS q b i len c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS Hq HQ1 HI HLN Hb.
  unfold K32S3 in KS.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_LC Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x1 x1 x1 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap i len).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  - intros mm' y10 y11 y12 y13 b' SPL' BD2' MI' MU' WM' BUF'.
    rewrite Z_to_bv_bv_unsigned in BD2'.
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
             (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
             bd3 (BD4A c (Z_to_bv 64 b') jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply KS. exact FS'.
  - intros mm' y12 y13 v HV SPL' BD2' MI' MU' WM' BUF'.
    rewrite Z_to_bv_bv_unsigned in BD2'.
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
             (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
             bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-184));
        [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
        | | exact B3S | | apply BD4A_size | | exact B1S].
      - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s32_LSd Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS q b v c p jp w0 w4 w5 w7 w8 w9 w11 mm' x1 x5 x7 x8 y12 y13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS'); lia.
Qed.

Lemma z4s32_LSb : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  forall (q b i : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 i) x12 x13 x14 x15 x16 x17
        x18 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x91ee8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS q b i c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS Hq HQ1 HI Hb.
  unfold K32S3 in KS.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_LB Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x1 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap i).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  intros mm' y10 y11 y13 HY10 HY11 SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4
           bd3 (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-184));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | apply BD4A_size | | exact B1S].
    - replace (bv_unsigned sp + -184 + 40) with (bv_unsigned sp + -144) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  rewrite <- (Z_to_bv_bv_unsigned y10), HY10. rewrite <- (Z_to_bv_bv_unsigned y11).
  eapply (z4s32_LSc Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS q b i (bv_unsigned y11) c p jp w0 w4 w5 w7 w8 w9 w11 mm' x1 x5 x7 x8 y13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS'); lia.
Qed.

Lemma z4s32_LS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS.
  unfold K32L.
  intros q b c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS Hq Hq2 Hb.
  unfold K32S3 in KS.
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
  unfold SPD in SPL. unfold BD4A in B2.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s32_LA Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B2
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  - intros E. eapply KS. exact FS.
  - intros E i y10 y12 HI.
    eapply (z4s32_LSb Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS q b i c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 y10 y12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x27 x28 x29 x31 FS); lia.
Qed.

Lemma z4s32_KXS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS.
  exact (z4s32_KX Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe (z4s32_LS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS)).
Qed.

Lemma z4s32_KNS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS.
  exact (z4s32_KN Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe (z4s32_LS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS)).
Qed.

End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.
Section Z32RLJ.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s32_JC : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  K32L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KX KN KL.
  pose proof (z4s32_L2 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KX KN) as KH2.
  unfold C32J.
  intros q b c p jp w0 w4 w5 w7 w8 w9 w11 mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31
    FS Hq Hd.
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
  unfold SPD in SPL. unfold BD4A in B2.
  assert (HB31 : 0 <= b < 2^31) by (destruct Hd as [[_ Hb] | Hb]; lia).
  eapply (z4s32_J Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x20 x23 x22 x24 x25 x18 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w11 c p (Z_to_bv 64 (SSa + O)) (Z_to_bv 64 (SSa + O + 8)) jp
            (bv_unsigned sp) DST dcap DT q Qe b tl mtl).
  all: try assumption.
  all: try lia.
  -
    intros HQ2.
    eapply KL; [exact FS | lia | lia | lia].
  -
    intros HQ2 Hb64 z10.
    destruct Hd as [[(pt & Hp & Hpt & HptL) Hb] | Hb]; [| lia].
    subst p.
    eapply (KH2 q); [exact FS | lia | exact Hpt | exact HptL | lia].
  -
    intros HQ2 Hb64 z10.
    eapply KN; [exact FS | lia | lia].
Qed.

End Z32RLJ.
End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s32_HT : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K32S3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1 ->
  C32J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 x9 x18 bd4 bd3 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS.
  pose proof (z4s32_LS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KS) as KL.
  exact (z4s32_JC huf_reload_int_proofA Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
           DST dcap SSa DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe
           (z4s32_KX Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL)
           (z4s32_KN Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 x9 x18 bd4 bd3 bd1 C D6 O6 L1 OL HQe KL)
           KL).
Qed.

End CANSEC1.

Theorem z4s32_proof {rc : runConstT} : z4s32_stmtA.
Proof. exact (z4s32_top z4s32_HT). Qed.

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
  (* [comment removed for export] *)
