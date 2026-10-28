(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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


From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s34k.

Definition C34H2at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1 ->
    0 <= q <= dcap -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x9405c) fc None mm (seg_rom bsegs)).

Definition C34H2 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell) : Prop :=
  forall q : Z, C34H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 q.

Definition K34X (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1 ->
    0 <= q <= dcap -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> (pt = 0 \/ dcap - q < 2) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x942a0) fc None mm (seg_rom bsegs)).

Definition K34N (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell) : Prop :=
  forall (q b : Z) (c p : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1 ->
    0 <= q <= dcap -> 64 < b < 2^31 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x94294) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s34_M2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
    (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src ->
  K34X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 -> K34N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 ->
  (forall q', q < q' -> C34H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1 ->
  0 <= q <= dcap -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 ->
  (x10 = Z_to_bv 64 0 /\ pt = 0 \/ x10 = Z_to_bv 64 1) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x9416c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 q pt b c jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm
    x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    C D6 O6 L1 OL KX KN IH FS Hq Hpt HptL Hb Hx.
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
  unfold SPD in SPL. unfold BD4A in B4. unfold C34H2at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct (Z_lt_le_dec (dcap - q) 2) as [HQ2 | HQ2].
  { eapply z4s34_X2; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | left; lia |].
    eapply KX; [exact FS | lia | lia | exact HptL | lia | right; lia]. }
  destruct Hx as [[Hx0 Hp0] | Hx1].
  { subst x10.
    eapply z4s34_X2; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | right; reflexivity |].
    eapply KX; [exact FS | lia | lia | exact HptL | lia | left; exact Hp0]. }
  subst x10.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s34_B2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 y12 y13 y14 y15 y16 y17 nb Hnb Hz10 SPL' BD4' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD4'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
                 (BD4A c (Z_to_bv 64 (b + nb)) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))
                 bd3 bd2 bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-264));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | apply BD4A_size
      | | exact B3S | | exact B2S | | exact B1S].
    - replace (bv_unsigned sp + -264 + 40) with (bv_unsigned sp + -224) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - unfold BD4A. exact BD4'.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply z4s34_C2; [exact SPL' | exact BD4' | exact MI' | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hbn. eapply (IH (q + bv_unsigned z10)); [lia | exact FS' | lia | exact Hpt | exact HptL | lia].
  - intros Hbn. eapply KN; [exact FS' | lia | lia].
Qed.

Section Z34RL.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s34_H2L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src ->
  K34X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 -> K34N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 ->
  (forall q', q < q' -> C34H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 q') -> C34H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 q C D6 O6 L1 OL KX KN IH.
  unfold C34H2at.
  intros pt b c jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s34_H2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) x22 x23 x24 x25
            (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))
            (bv_unsigned sp) DST dcap SS DT q O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hp8 z12.
    eapply (z4_rl_call4 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd3 bd2 bd1 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s34_RT with (bd4 := @nil cell); [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s34_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | exact KX | exact KN | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | right; reflexivity].
  -
    intros Hp0 z10 z12 z13.
    eapply KX; [exact FS | lia | lia | exact HptL | lia | left; exact Hp0].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD4' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -264, bv_unsigned sp + -264 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
                   (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-264));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | apply BD4A_size
        | | exact B3S | | exact B2S | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - unfold BD4A. exact BD4'.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s34_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | exact KX | exact KN | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | right; reflexivity].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z16 z17 SPL' BD4' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -264, bv_unsigned sp + -264 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
                   (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-264));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | apply BD4A_size
        | | exact B3S | | exact B2S | | exact B1S].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - unfold BD4A. rewrite Z.add_0_r. exact BD4'.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s34_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | exact KX | exact KN | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | left; split; reflexivity].
Qed.

Lemma z4s34_L2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src ->
  K34X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 -> K34N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1 -> C34H2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 C D6 O6 L1 OL KX KN.
  unfold C34H2. intros q.
  remember (Z.to_nat (dcap - q)) as n eqn:Hn. revert q Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros q Hn.
  apply (z4s34_H2L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
           src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 q C D6 O6 L1 OL KX KN).
  intros q' Hq'.
  destruct (Z_le_gt_dec q' dcap) as [Hle | Hgt].
  - apply (IHn (Z.to_nat (dcap - q'))); [lia | reflexivity].
  - unfold C34H2at. intros. lia.
Qed.

End Z34RL.

End CANSEC1.

Lemma z4s34_NB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q b c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 2 <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (z10 y11 y12 y13 y14 y15 y16 y17 : word) (b' : Z), 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + (q + bv_unsigned z10))) z10 y11 y12 y13
              y14 y15 y16 y17 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x94400) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13
           x14 x15 x16 x17 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9434c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob SP DST dcap DT q b c tl mtl A2 L2 A3 L3
    SPL BD4 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 2 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x94400] 200%nat [false; false]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 2 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brtf.
  all: try first [z4shd | z4shd].
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: let R42 := fresh "R42" in kx_range (EVar 42) R42.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s34_BR1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word)
    (SP DST dcap DT q tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q + 2 <= dcap ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x9434c) fc None mm (seg_rom bsegs))) ->
  (dcap < q + 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x942a4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x942a0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 SP DST dcap DT q tl mtl SPL MI RS HD HDE HDC HQ HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec (q + 2) dcap) as [C|C].
  - kx_runFmd [0x9434c; 0x942a4] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (dcap - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact (K1 C).
  - kx_runFmd [0x9434c; 0x942a4] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (q + 2 - dcap) 1 2;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K2; lia.
Qed.

Lemma z4s34_BR2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word)
    (SP DST dcap DT q tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q + 2 <= dcap ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x9434c) fc None mm (seg_rom bsegs))) ->
  (dcap < q + 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x942a4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x94400) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 SP DST dcap DT q tl mtl SPL MI RS HD HDE HDC HQ HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec (q + 2) dcap) as [C|C].
  - kx_runFmd [0x9434c; 0x942a4] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (dcap - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact (K1 C).
  - kx_runFmd [0x9434c; 0x942a4] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (q + 2 - dcap) 1 2;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K2; lia.
Qed.

Lemma z4s34_TN : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap -> 0 <= b < 2^32 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (forall mm' : amem,
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00); C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 0x20e00) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x942a0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x94294) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 c p s l jp SP DST dcap DT q b tl mtl SPL BD4 MI RS HD HDE HDC HQ HB HTL HMT HDT HSP K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x942a0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange b 0 (2^32 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge ].
Qed.

Lemma z4s34_LA : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l : word) (jp : list byte)
    (SP DST dcap DT q b c tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap -> dcap <= q + 1 ->
  0 <= b < 2^32 -> 0 <= c < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q = dcap ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x9448c) fc None mm (seg_rom bsegs))) ->
  (q + 1 = dcap -> forall (i : Z) (y10 y12 : word), 0 <= i < 2^tl ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) y10 (Z_to_bv 64 i) y12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x942c0) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x942a4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp SP DST dcap DT q b c tl mtl
    SPL BD4 MI RS HD HDE HDC HQ HQ1 HB HC HTL HMT HDT HSP K0 K1.
  unfold AZ4_SB in *.
  destruct (Z.eq_dec q dcap) as [E|E].
  - kx_runFmd [0x9448c] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (dcap - q) 0 0;
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b; KZWord (SP + -368) 8 (tl + 256 * mtl);
      KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K0; lia.
  - kx_runFmd [0x942c0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (dcap - q) 1 1;
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b; KZWord (SP + -368) 8 (tl + 256 * mtl);
      KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: kx_post_regs_keep.
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20 ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) _ _ _ _ _ _) =>
      rewrite <- (Z_to_bv_bv_unsigned r11); eapply (K1 ltac:(lia) (bv_unsigned r11) r10 r12) end.
    all: lazymatch goal with
         | |- evtF _ _ _ _ => z4post_ez
         | |- 0 <= bv_unsigned (edenot ?E (EAlu ALU_SRL ?x ?s)) < 2^?t => apply (z4_srl_ltt E x s t); [lia | z4uzm]
         end.
Qed.

Lemma z4s34_br_shif : forall E X K,
  bv_unsigned (edenot E K) = 2^61 -> bv_unsigned (edenot E X) < 2^61 ->
  branch_taken BC_NE (edenot E (EAlu ALU_SRL (EAlu ALU_ADD X K) (ELit 62))) (edenot E (ELit 0)) = false.
Proof.
  intros E X K HK HX.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [HX0 _].
  cbn [edenot branch_taken] in *.
  rewrite bv_eqb_Z, u_srl64, u_add64, HK.
  change (bv_unsigned (Z_to_bv 64 62)) with 62. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (62 mod 64) with 62.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma z4s34_LB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q b c tl mtl A2 L2 A3 L3 i : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = dcap -> 0 <= i < 2^tl ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y13 : word), bv_unsigned y10 = DT + 4 + 4 * i -> 1 <= bv_unsigned y11 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q)) y10 y11 (Z_to_bv 64 1) y13
              x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x94320) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 i) x12 x13
           x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x942c0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob SP DST dcap DT q b c tl mtl A2 L2 A3 L3 i
    SPL BD4 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HI HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x94320] 200%nat [false; false]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 1 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brtf.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot ?E (EAlu ALU_SRL (EAlu ALU_ADD ?X ?K) (ELit 62))) _ = false => apply (z4s34_br_shif E X K); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: let R42 := fresh "R42" in kx_range (EVar 42) R42.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s34_br_sx63 : forall E X, 64 <= bv_unsigned (edenot E X) < 2^32 ->
  branch_taken BC_LTU (edenot E (ELit 63)) (edenot E (EExt true 0 4 X)) = true.
Proof.
  intros E X HX. cbn [edenot branch_taken] in *.
  rewrite bv_ltu_Z. change (bv_unsigned (Z_to_bv 64 63)) with 63.
  destruct (Z_lt_le_dec (bv_unsigned (edenot E X)) (2^31)) as [HS|HS].
  - rewrite u_ext_sx0_small by (cbn; lia). apply Z.ltb_lt. lia.
  - rewrite u_ext_sx0_high by (cbn; lia). apply Z.ltb_lt. lia.
Qed.

Lemma z4s34_LC : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q b c tl mtl A2 L2 A3 L3 i len : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = dcap -> 0 <= i < 2^tl -> 1 <= len <= 2 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y12 y13 : word) (b' : Z), 
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q + 1)) y10 y11 y12 y13
             x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
             x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x9448c) fc None mm' (seg_rom bsegs))) ->
  (forall (mm' : amem) (y12 y13 : word) (v : Z), 0 <= v < 128 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 v) (Z_to_bv 64 64) y12 y13
             x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
             x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x94474) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 len) (Z_to_bv 64 1) x13
           x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x94320) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob SP DST dcap DT q b c tl mtl A2 L2 A3 L3 i len
    SPL BD4 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HI HLN HTL HMT HDT HSP HB HC HTE HT2 K K2.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  destruct (Z.eq_dec len 1) as [LN1 | LN2]; [| assert (LN2' : len = 2) by lia; destruct (Z_le_gt_dec b 63) as [B63 | B64]].
  3: kx_runFmd [0x9448c; 0x94474] 200%nat [true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 1 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 64 (2^32 - 1); KZRange len 2 2; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  2: kx_runFmd [0x9448c; 0x94474] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 1 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 63; KZRange len 2 2; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  1: kx_runFmd [0x9448c; 0x94474] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 1 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange len 1 1; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try (lazymatch goal with |- branch_taken BC_LTU (edenot ?E (ELit 63)) (edenot ?E (EExt true 0 4 ?X)) = true => apply (z4s34_br_sx63 E X); z4uz end).
  all: try z4brx.
  all: try z4brtf.
  all: try z4br.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: kx_post_regs_keep.
  2: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + bv_unsigned (ev _ ?n))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => let R := fresh "R" in kx_range (EVar n) R end.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: first [eapply K | eapply K2].
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s34_LD : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q b c tl mtl A2 L2 A3 L3 v : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = dcap -> 0 <= v < 128 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y12 y13 : word) (b' : Z), 
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q + 1)) y10 y11 y12 y13
             x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
             x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x9448c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 v) (Z_to_bv 64 64) x12 x13
           x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x94474) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob SP DST dcap DT q b c tl mtl A2 L2 A3 L3 v
    SPL BD4 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HV HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  destruct (Z_lt_le_dec v 64) as [V64 | V64].
  2: kx_runFmd [0x9448c] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 1 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange v 64 127; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  1: kx_runFmd [0x9448c] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 1 1; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange v 0 63; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try (lazymatch goal with |- branch_taken BC_LTU (edenot ?E (ELit 63)) (edenot ?E (EExt true 0 4 ?X)) = true => apply (z4s34_br_sx63 E X); z4uz end).
  all: try z4brx.
  all: try z4brtf.
  all: try z4br.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s34_c4mod : forall m A (c : word) (V : Z) (jp : list byte) (p s l : word),
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 V); CB 4 jp; C8 p; C8 s; C8 l] ->
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 (V mod 2^32)); CB 4 jp; C8 p; C8 s; C8 l].
Proof.
  intros m A c V jp p s l RW.
  assert (E : le4 (Z_to_bv 64 V) = le4 (Z_to_bv 64 (V mod 2^32))).
  { unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite !Z_to_le_bytes_mod by (cbn; lia). reflexivity. }
  unfold rw_cells, cells_at in *. destruct RW as [[WF BA] WR].
  split; [split|].
  - exact WF.
  - cbn [cells_bytes cbytes] in BA |- *. rewrite <- E. exact BA.
  - exact WR.
Qed.

Definition K34L (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (x22 s l : word) (bd3 bd2 bd1 : list cell) : Prop :=
  forall (q : Z) (b : Z) (c p : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1 ->
    0 <= q <= dcap -> dcap < q + 2 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
        x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x942a4) fc None mm (seg_rom bsegs)).

Definition C34Bat (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (x22 s l : word) (bd3 bd2 bd1 : list cell) (q : Z) : Prop :=
  forall (b : Z) (c p : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1 ->
    0 <= q -> q + 2 <= dcap -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x9434c) fc None mm (seg_rom bsegs)).

Definition C34B (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (x22 s l : word) (bd3 bd2 bd1 : list cell) : Prop :=
  forall q : Z, C34Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1 q.

Definition C34T (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (x22 s l : word) (bd3 bd2 bd1 : list cell) : Prop :=
  forall (q : Z) (b : Z) (c p : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
           (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1 ->
    0 <= q <= dcap -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x942a0) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s34_NLs : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (x22 s l : word) (bd3 bd2 bd1 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src ->
  K34L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1 ->
  (forall q', q < q' -> C34Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1 q') ->
  C34Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk x22 s l bd3 bd2 bd1 q C D6 SRC0 KL IH.
  unfold C34Bat.
  intros b c p jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 FS Hq Hq2 Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  unfold C34Bat in IH.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s34_NB Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob
            (bv_unsigned sp) DST dcap DT q b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 y11 y12 y13 y14 y15 y16 y17 b' Hz10 SPL' BD4' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD4'.
  apply z4s34_c4mod in BD4'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
                 (BD4A c (Z_to_bv 64 (b' mod 2^32)) jp p s l) bd3 bd2 bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-264));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | apply BD4A_size
      | | exact B3S | | exact B2S | | exact B1S].
    - replace (bv_unsigned sp + -264 + 40) with (bv_unsigned sp + -224) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - unfold BD4A. exact BD4'.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  pose proof (Z.mod_pos_bound b' (2^32) ltac:(lia)) as HBM.
  eapply (z4s34_BR2 Q RNG mm' FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 z10 y11 y12 y13 y14 y15 y16 y17 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 (bv_unsigned sp) DST dcap DT (q + bv_unsigned z10) tl mtl);
    [exact SPL' | exact MI' | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hc. eapply (IH (q + bv_unsigned z10)); [lia | exact FS' | lia | lia | exact HBM].
  - intros Hc. eapply KL; [exact FS' | lia | lia | exact HBM].
Qed.

Lemma z4s34_NL : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (x22 s l : word) (bd3 bd2 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src ->
  K34L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1 ->
  C34B RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk x22 s l bd3 bd2 bd1 C D6 SRC0 KL.
  unfold C34B. intros q.
  remember (Z.to_nat (dcap - q)) as n eqn:Hn. revert q Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros q Hn.
  apply (z4s34_NLs Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk x22 s l bd3 bd2 bd1 q C D6 SRC0 KL).
  intros q' Hq'.
  destruct (Z_le_gt_dec q' dcap) as [Hle | Hgt].
  - apply (IHn (Z.to_nat (dcap - q'))); [lia | reflexivity].
  - unfold C34Bat. intros. lia.
Qed.

Lemma z4s34_T : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (x22 s l : word) (bd3 bd2 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src ->
  K34L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1 ->
  C34T RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk x22 s l bd3 bd2 bd1 C D6 SRC0 KL.
  pose proof (z4s34_NL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk x22 s l bd3 bd2 bd1 C D6 SRC0 KL) as NL.
  unfold C34B, C34Bat in NL.
  unfold C34T.
  intros q b c p jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 FS Hq Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s34_BR1 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 (bv_unsigned sp) DST dcap DT q tl mtl);
    [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hc. eapply NL; [exact FS | lia | lia | exact Hb].
  - intros Hc. eapply KL; [exact FS | lia | lia | exact Hb].
Qed.

Lemma z4s34_KX : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src ->
  K34L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) bd3 bd2 bd1 ->
  K34X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 C D6 SRC0 KL.
  pose proof (z4s34_T Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk x22 (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) bd3 bd2 bd1 C D6 SRC0 KL) as T.
  unfold C34T in T.
  unfold K34X. intros.
  eapply T; [eassumption | lia | lia].
Qed.

Lemma z4s34_KN : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk : Z) (x22 : word) (bd3 bd2 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src ->
  K34L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) bd3 bd2 bd1 ->
  K34N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk x22 bd3 bd2 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk x22 bd3 bd2 bd1 C D6 SRC0 KL.
  pose proof (z4s34_T Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk x22 (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) bd3 bd2 bd1 C D6 SRC0 KL) as T.
  unfold C34T in T.
  unfold K34N.
  intros q b c p jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 FS Hq Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s34_TN Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 c p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp (bv_unsigned sp) DST dcap DT q b tl mtl);
    [exact SPL | exact B4 | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia |].
  intros mm' SPL' BD4' MI' MU' WM'.
  destruct BUF as (ob & OB & OBL).
  assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -264, bv_unsigned sp + -264 + 40);
                       (DST, DST + dcap)] mm mm').
  { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
                 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 0x20e00) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-264));
      [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' |  | | apply SPD_size | | apply BD4A_size
      | | exact B3S | | exact B2S | | exact B1S].
    - exists ob. split; [| exact OBL].
      eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
    - unfold SPD. exact SPL'.
    - unfold BD4A. exact BD4'.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  eapply T; [exact FS' | lia | lia].
Qed.

End CANSEC1.

Definition E34END (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (bd3 bd2 bd1 : list cell) : Prop :=
  forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : word)
         (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
         (SPD v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 (Z_to_bv 64 dcap)) (BD4A c' b' jp' p' s' l') bd3 bd2 bd1 ->
    evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                         FR (Z_to_bv 64 AZ4_END) fc None mm' (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s34_LSD : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (bd3 bd2 bd1 : list cell)
    (q b v : Z) (c p s l : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src -> E34END RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q bd3 bd2 bd1 ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
    (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
    (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1 ->
  0 <= q -> q + 1 = dcap -> 0 <= v < 128 -> 0 <= b < 2^32 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 v) (Z_to_bv 64 64) x12 x13
      x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
    FR (Z_to_bv 64 0x94474) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 q b v c p s l jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 C D6 SRC0 KE FS Hq Hq1 Hv Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s34_LD Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob (bv_unsigned sp) DST dcap DT q b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap v).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' y10 y11 y12 y13 b' SPL' BD4' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD4'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
             (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
             (BD4A c (Z_to_bv 64 b') jp p s l) bd3 bd2 bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-264));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | apply BD4A_size
      | | exact B3S | | exact B2S | | exact B1S].
    - replace (bv_unsigned sp + -264 + 40) with (bv_unsigned sp + -224) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - unfold BD4A. exact BD4'.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  unfold E34END in KE. eapply KE. exact FS'.
Qed.

Lemma z4s34_LSC : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (bd3 bd2 bd1 : list cell)
    (q b i len : Z) (c p s l : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src -> E34END RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q bd3 bd2 bd1 ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
    (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
    (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1 ->
  0 <= q -> q + 1 = dcap -> 0 <= i < 2^tl -> 1 <= len <= 2 -> 0 <= b < 2^32 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 len) (Z_to_bv 64 1) x13
      x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
    FR (Z_to_bv 64 0x94320) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 q b i len c p s l jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 C D6 SRC0 KE FS Hq Hq1 Hi Hlen Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s34_LC Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob (bv_unsigned sp) DST dcap DT q b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap i len).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  - intros mm' y10 y11 y12 y13 b' SPL' BD4' MI' MU' WM' BUF'.
    rewrite Z_to_bv_bv_unsigned in BD4'.
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
               (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
               (BD4A c (Z_to_bv 64 b') jp p s l) bd3 bd2 bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-264));
        [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | apply BD4A_size
        | | exact B3S | | exact B2S | | exact B1S].
      - replace (bv_unsigned sp + -264 + 40) with (bv_unsigned sp + -224) by lia. exact MU'.
      - unfold SPD. exact SPL'.
      - unfold BD4A. exact BD4'.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    unfold E34END in KE. eapply KE. exact FS'.
  - intros mm' y12 y13 v Hv SPL' BD4' MI' MU' WM' BUF'.
    rewrite Z_to_bv_bv_unsigned in BD4'.
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
               (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
               (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-264));
        [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | apply BD4A_size
        | | exact B3S | | exact B2S | | exact B1S].
      - replace (bv_unsigned sp + -264 + 40) with (bv_unsigned sp + -224) by lia. exact MU'.
      - unfold SPD. exact SPL'.
      - unfold BD4A. exact BD4'.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
    eapply (z4s34_LSD Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 q b v c p s l jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm' x1 x5 x7 x8 y12 y13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31);
      [exact C | exact D6 | exact SRC0 | exact KE | exact FS' | lia | lia | exact Hv | lia].
Qed.

Lemma z4s34_LSB : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (bd3 bd2 bd1 : list cell)
    (q b i : Z) (c p s l : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (mm : amem)
    (x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src -> E34END RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q bd3 bd2 bd1 ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
    (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
    (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1 ->
  0 <= q -> q + 1 = dcap -> 0 <= i < 2^tl -> 0 <= b < 2^32 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 i) x12 x13
      x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
    FR (Z_to_bv 64 0x942c0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 q b i c p s l jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 C D6 SRC0 KE FS Hq Hq1 Hi Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s34_LB Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob (bv_unsigned sp) DST dcap DT q b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap i).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' y10 y11 y13 HY10 HY11 SPL' BD4' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD4'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
             (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap))
             (BD4A c (Z_to_bv 64 b) jp p s l) bd3 bd2 bd1).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-264));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | apply BD4A_size
      | | exact B3S | | exact B2S | | exact B1S].
    - replace (bv_unsigned sp + -264 + 40) with (bv_unsigned sp + -224) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - unfold BD4A. exact BD4'.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]. rewrite B1S. cbn [disjoint_from]. lia. }
  rewrite <- (Z_to_bv_bv_unsigned y10), HY10. rewrite <- (Z_to_bv_bv_unsigned y11).
  eapply (z4s34_LSC Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 q b i (bv_unsigned y11) c p s l jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm' x1 x5 x7 x8 y13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31);
    [exact C | exact D6 | exact SRC0 | exact KE | exact FS' | lia | lia | exact Hi | lia | lia].
Qed.

Lemma z4s34_LS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (bd3 bd2 bd1 : list cell) (x22 s l : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 0 < zlen src -> E34END RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q bd3 bd2 bd1 ->
  K34L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q x22 s l bd3 bd2 bd1.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 x22 s l C D6 SRC0 KE.
  unfold K34L.
  intros q b c p jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x27 x28 x29 x31 FS Hq Hq2 Hb.
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
  unfold SPD in SPL. unfold BD4A in B4.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s34_LA Q RNG mm FR fc gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp (bv_unsigned sp) DST dcap DT q b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B4
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  - intros E. unfold E34END in KE. eapply KE. exact FS.
  - intros E1 i y10 y12 Hi.
    eapply (z4s34_LSB Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk bd3 bd2 bd1 q b i c p s l jp w0 w1 w4 w5 w7 w8 w9 w10 w11 mm x1 x5 x7 x8 y10 y12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31);
      [exact C | exact D6 | exact SRC0 | exact KE | exact FS | lia | lia | exact Hi | exact Hb].
Qed.

End CANSEC1.



  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
