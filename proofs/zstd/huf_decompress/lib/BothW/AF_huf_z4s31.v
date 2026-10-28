(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s31k AF_huf_z4s31a AF_huf_z4s31b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi AF_huf_z4s31t.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition C31H2at (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z) : Prop :=
  forall (pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90a40) fc None mm (seg_rom bsegs)).

Definition C31H2 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall q : Z, C31H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s31_M2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell)
    (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
    (x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 -> K31N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
  0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 ->
  (x10 = Z_to_bv 64 0 /\ pt = 0 \/ x10 = Z_to_bv 64 1) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90b70) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q pt b c jp w0 w4 w5 w7 w8 w11 mm
    x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B1. unfold C31H2at in IH.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct (Z_lt_le_dec (Qe - q) 2) as [HQ2 | HQ2].
  { eapply z4s31_X2; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | left; lia |].
    eapply KX; [exact FS | lia | lia | exact HptL | lia | right; lia]. }
  destruct Hx as [[Hx0 Hp0] | Hx1].
  { subst x10.
    eapply z4s31_X2; [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | right; reflexivity |].
    eapply KX; [exact FS | lia | lia | exact HptL | lia | left; exact Hp0]. }
  subst x10.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_B2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x11 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 x24 x25 x27 x28 x29 x31 w0 w1 w4 w5 w7 w8 w10 w11 (Z_to_bv 64 (SS + O + pt))
            (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob (bv_unsigned sp) DST dcap DT q Qe b
            (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 y12 y13 y14 y15 y17 nb Hnb Hz10 SPL' BD2' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD2'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                 (BD4A c (Z_to_bv 64 (b + nb)) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS | | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD2'. }
  eapply z4s31_C2; [exact SPL' | exact BD2' | exact MI' | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hbn. eapply (IH (q + bv_unsigned z10)); [lia | exact FS' | lia | exact Hpt | exact HptL | lia].
  - intros Hbn. eapply KN; [exact FS' | lia | lia].
Qed.

Section Z31RL2.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s31_H2L : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 -> K31N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') -> C31H2at RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KX KN IH.
  unfold C31H2at.
  intros pt b c jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x10 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s31_H2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10
            (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (64 - tl))
            (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4))
            x31 w0 w1 w4 w5 w7 w8 w10 w11 jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) (bv_unsigned sp) DST
            dcap SS DT q Qe O Lk pt b (bv_unsigned c) tl mtl SBL (SBH - SBL)).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  -
    intros Hp8 z12.
    eapply (z4_rl_call1 HRL Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm _ bd4 bd3 bd2 O Lk pt b c jp FR fc gp);
      [exact C | exact D1 | lia | exact OL | exact FS | lia | lia | lia |].
    intros mm' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 FS'.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof FS' as FS1.
    destruct FS1 as (BUF1 & BSS1 & BDT41 & BDT1 & STK1 & SPL1 & SPLS1 & B41 & B4S1 & B31 & B3S1 & B21 & B2S1 & B11 & B1S1
                     & FRM1 & MI1 & MU1 & WM1).
    unfold SPD in SPL1.
    eapply z4s31_RT with (bd3 := @nil cell); [exact SPL1 | exact MI1 | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia |].
    eapply (z4s31_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q (pt - b / 8) (b mod 8));
      [exact C | lia | lia | lia | exact OL | lia | exact KX | exact KN | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | right; reflexivity].
  -
    intros Hp0 z10 z12 z13.
    eapply KX; [exact FS | lia | lia | exact HptL | lia | left; exact Hp0].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c' (Z_to_bv 64 (b - 8 * (b / 8))) jp (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD2'. }
    eapply (z4s31_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q (pt - b / 8) (b - 8 * (b / 8)));
      [exact C | lia | lia | lia | exact OL | lia | exact KX | exact KN | exact IH | exact FS' | lia
      | Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | right; reflexivity].
  -
    intros Hp17 Hbp mm' c' z11 z12 z13 z14 z15 z17 SPL' BD2' MI' MU' WM'.
    destruct BUF as (ob & OB & OBL).
    assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                         (DST, DST + dcap)] mm mm').
    { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c' (Z_to_bv 64 (b - 8 * pt)) jp (Z_to_bv 64 (SS + O + 0)) (Z_to_bv 64 (SS + O))
                         (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - exists ob. split; [| exact OBL].
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. rewrite Z.add_0_r. exact BD2'. }
    eapply (z4s31_M2 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
              src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q 0 (b - 8 * pt));
      [exact C | lia | lia | lia | exact OL | lia | exact KX | exact KN | exact IH | exact FS' | lia
      | lia | left; reflexivity | Z.div_mod_to_equations; lia | left; split; reflexivity].
Qed.

Lemma z4s31_L2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 -> K31N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 -> C31H2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KX KN.
  unfold C31H2. intros q.
  remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros q Hn.
  apply (z4s31_H2L Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
           src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KX KN).
  intros q' Hq'.
  destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
  - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
  - unfold C31H2at. intros. lia.
Qed.

End Z31RL2.

End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.
Section Z31RLJ.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4s31_JC : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KX KN KL.
  pose proof (z4s31_L2 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KX KN) as KH2.
  unfold C31J.
  intros q b c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31
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
  unfold SPD in SPL. unfold BD4A in B1.
  assert (HB31 : 0 <= b < 2^31) by (destruct Hd as [[_ Hb] | Hb]; lia).
  eapply (z4s31_J2 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22
            x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 c p (Z_to_bv 64 (SSa + O)) (Z_to_bv 64 (SSa + O + 8)) jp
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

End Z31RLJ.
End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s31_HT : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS.
  exact (z4s31_JC huf_reload_int_proofA Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe
           (z4s31_KXS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS)
           (z4s31_KNS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS)
           (z4s31_LS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS)).
Qed.

Lemma z4s31_top :
  (forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
     (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
     (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
     (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
     (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
   z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
   6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
   K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
   C31J RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2) ->
  z4s31_stmtA.
Proof.
  intros HT. unfold z4s31_stmtA.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
    src cells cbs pdt SBL SBH rstk O Lk Qe C D6 O6 L1 OL HQe.
  unfold z4s31_goal.
  intros q pt b c jp w0 w1 w4 w5 w7 w8 w10 w11 w12 bd4 bd3 bd2 mm
    x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31 FS Hq Hpt HptL Hb K.
  assert (KS : K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2) by (unfold K31S2; exact K).
  pose proof (HT Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS) as KJ.
  pose proof huf_reload_int_proofA as HRL.
  pose proof (z4s31_L5 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ) as KH5.
  pose proof (z4s31_E4 HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ) as KH4.
  pose proof (z4s31_RL HRL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SSa DT mtl tl lo
                src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KJ) as KR.
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
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_E Q RNG mm FR fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28
            x29 x31 w0 w1 w4 w5 w7 w8 w10 w11 w12 jp (bv_unsigned sp) DST dcap SSa DT q Qe O Lk pt b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       end).
  all: try assumption.
  all: try lia.
  1: intros HC mm' SPL' BD1' MI' MU' WM'.
  2: intros HC HC2 mm' SPL' BD1' MI' MU' WM'.
  3, 4: intros HC HC2 HC3 mm' SPL' BD1' MI' MU' WM'.
  all: rewrite ?Z_to_bv_bv_unsigned in BD1'.
  all: assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                            (DST, DST + dcap)] mm mm')
         by (eapply munch_weaken; [| exact MU']; intros x HX; cbn [outside] in *; repeat split; try exact I; intros ?; lia).
  all: match type of BD1' with rw_cells _ _ _ [_; _; _; C8 ?pv; C8 ?sv; C8 ?lv] =>
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SSa DT mtl tl lo src cbs mm'
                   (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                        (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                   (BD4A c (Z_to_bv 64 b) jp pv sv lv)) end.
  all: try (eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SSa DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' | | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size];
      [ exists ob; split; [| exact OBL];
        eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]; rewrite length_map; cbn [disjoint_from]; lia
      | unfold SPD; exact SPL'
      | eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]; rewrite B4S; cbn [disjoint_from]; lia
      | eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]; rewrite B3S; cbn [disjoint_from]; lia
      | eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]; rewrite B2S; cbn [disjoint_from]; lia
      | unfold BD4A; exact BD1' ]).
  -
    eapply KR; [exact FS' | lia | lia | exact Hpt | exact HptL | lia].
  -
    eapply KH4; [exact FS' | lia | lia | exact Hpt | exact HptL | lia | lia].
  -
    eapply (KH5 q pt b c jp w0 w4 w5 w7 w8 w11 mm' _ _ _ _ _ x1 _ _ _ _ x1 x1 x1 x1 _ _ _ _ _);
      [exact FS' | lia | exact Hpt | exact HptL | lia | lia].
  -
    eapply KJ; [exact FS' | lia | right; lia].
Qed.

End CANSEC1.

Theorem z4s31_proof {rc : runConstT} : z4s31_stmtA.
Proof. exact (z4s31_top z4s31_HT). Qed.
