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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import MState PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4s3b AF_huf_w4s3_iface AF_huf_w4s3_iface3.
Import ListNotations.
Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Ltac w4s34_zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

(* [comment removed for export] *)
Lemma w4s34_ck1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word) (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -376) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c5e4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c5c4) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [0x8c5e4] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -360) 8 P; KZWord (SP + -352) 8 A; KZWord (SP + -368) 4 B; KZWr (SP + -376) 40] [] [(SP + -480, 480)] []
  | kx_runFmd [0x8c5e4] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -360) 8 P; KZWord (SP + -352) 8 A; KZWord (SP + -368) 4 B; KZWr (SP + -376) 40] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.


Lemma w4s34_ck2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e w0 w8 w16 w40 w48 w56 : word) (pad : list byte) (SP P A B DST dcap seg : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 -> 0 <= dcap < 2^64 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c608) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c5e4) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [0x8c608] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -128) 8 P; KZWord (SP + -120) 8 A; KZWord (SP + -136) 4 B; KZWr (SP + -144) 40; KZRange dcap 0 (2^64 - 1); KZWord (SP + -408) 8 dcap; KZWr (SP + -480) 104] [] [(SP + -480, 480)] []
  | kx_runFmd [0x8c608] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -128) 8 P; KZWord (SP + -120) 8 A; KZWord (SP + -136) 4 B; KZWr (SP + -144) 40; KZRange dcap 0 (2^64 - 1); KZWord (SP + -408) 8 dcap; KZWr (SP + -480) 104] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.


Lemma w4s34_ck3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word) (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -184) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c62c) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c608) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [0x8c62c] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -168) 8 P; KZWord (SP + -160) 8 A; KZWord (SP + -176) 4 B; KZWr (SP + -184) 40] [] [(SP + -480, 480)] []
  | kx_runFmd [0x8c62c] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -168) 8 P; KZWord (SP + -160) 8 A; KZWord (SP + -176) 4 B; KZWr (SP + -184) 40] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.


Lemma w4s34_ck4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word) (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -224) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c654) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c62c) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [0x8c654] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -208) 8 P; KZWord (SP + -200) 8 A; KZWord (SP + -216) 4 B; KZWr (SP + -224) 40] [] [(SP + -480, 480)] []
  | kx_runFmd [0x8c654] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1); KZRange B 0 (2^32 - 1); KZWord (SP + -208) 8 P; KZWord (SP + -200) 8 A; KZWord (SP + -216) 4 B; KZWr (SP + -224) 40] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.


Lemma w4s34_ck5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (SP V : Z),
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 -> 2^20 <= SP <= 2^47 -> 0 <= V < 2^64 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c660) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 V) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c654) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec V 0) as [HE|HE];
  [ kx_runFmd [0x8c660] 12%nat [false] [KZRange SP (2^20) (2^47); KZRange V 0 (2^64 - 1)] [] [(SP + -480, 480)] []
  | kx_runFmd [0x8c660] 12%nat [true] [KZRange SP (2^20) (2^47); KZRange V 0 (2^64 - 1)] [] [(SP + -480, 480)] [] ].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.

Lemma w4ck_rg : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range _ x). unfold bv_modulus in *. lia. Qed.

Lemma w4ck_cells : forall m A (c bw p a e : word) pad,
  rw_cells bsegs m A [C8 c; C4 bw; CB 4 pad; C8 p; C8 a; C8 e] ->
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 (bv_unsigned bw mod 2^32)); CB 4 pad; C8 (Z_to_bv 64 (bv_unsigned p));
                      C8 (Z_to_bv 64 (bv_unsigned a)); C8 e].
Proof.
  intros m A c bw p a e pad H. rewrite !Z_to_bv_bv_unsigned.
  apply (rw_cells_C4_eq bsegs m A [C8 c] bw (Z_to_bv 64 (bv_unsigned bw mod 2^32)) [CB 4 pad; C8 p; C8 a; C8 e]); [|exact H].
  pose proof (bv_unsigned_in_range _ bw) as R. pose proof (Z.mod_pos_bound (bv_unsigned bw) (2^32) ltac:(lia)) as B.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small (bv_unsigned bw mod 2^32) (2^64)) by lia. rewrite Zmod_mod. reflexivity.
Qed.

Section W4CK.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT (DTABLE_BYTES mtl)) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= bv_unsigned sp - HUF_DEC_STACK_A.
  Hypothesis SPT : bv_unsigned sp + 16 < al_top L.
  Hypothesis WSK : rng RNG lo (al_top L - lo).

  Lemma w4ck_rel : forall m A B cs sz, stk bsegs m lo A -> rw_cells bsegs m A cs -> cells_size cs = sz -> lo <= A ->
    B = A + Z.of_nat sz -> stk bsegs m lo B.
  Proof. intros m A B cs sz ST RW HS HL ->. subst sz. exact (stk_release bsegs m lo A cs ST RW HL). Qed.

  Lemma w4s34_ck_proof : w4s34_ck_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
                           DST dcap SS DT mtl tl lo src cbs.
  Proof using AH HDT HDB LOA LOS SPT WSK.
    intros c1 bw1 p1 a1 e1 c2 bw2 p2 a2 e2 c3 bw3 p3 a3 e3 c4 bw4 p4 a4 e4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HW.
    pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
    pose proof (AI_block_bounds AI L RNG st LB m0 _ AH HDB) as HB1. cbn [ab_addr ab_size] in HB1.
    unfold HUF_DEC_STACK_A, AIMG_HI in *.
    unfold W4F in HW.
    destruct HW as (_ & _ & _ & _ & ST & F0 & S0 & F1 & S1 & F2 & S2 & F3 & S3 & F4 & S4 & FRC & MI & MU & WM).
    assert (STK : stk bsegs mm lo (bv_unsigned sp + -104)).
    { pose proof (w4ck_rel mm _ (bv_unsigned sp + -480 + 104) _ _ ST F0 S0 ltac:(lia) ltac:(lia)) as T1.
      pose proof (w4ck_rel mm _ (bv_unsigned sp + -480 + 256) _ _ T1 F1 S1 ltac:(lia) ltac:(lia)) as T2.
      pose proof (w4ck_rel mm _ (bv_unsigned sp + -480 + 296) _ _ T2 F2 S2 ltac:(lia) ltac:(lia)) as T3.
      pose proof (w4ck_rel mm _ (bv_unsigned sp + -480 + 336) _ _ T3 F3 S3 ltac:(lia) ltac:(lia)) as T4.
      exact (w4ck_rel mm _ (bv_unsigned sp + -104) _ _ T4 F4 S4 ltac:(lia) ltac:(lia)). }
    assert (HR : rng RNG (bv_unsigned sp + -480) 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (HSP : 2^20 <= bv_unsigned sp <= 2^47) by lia.
    assert (HDC : 0 <= dcap < 2^64) by lia.
    unfold W4FRW in F0. cbv zeta in F0. unfold W4DX in F1, F2, F3, F4.
    apply kx_rw_cells_app in F1 as [F1 _].
    replace (bv_unsigned sp + -480 + 104) with (bv_unsigned sp + -376) in F1 by lia.
    replace (bv_unsigned sp + -480 + 256) with (bv_unsigned sp + -224) in F2 by lia.
    replace (bv_unsigned sp + -480 + 296) with (bv_unsigned sp + -184) in F3 by lia.
    replace (bv_unsigned sp + -480 + 336) with (bv_unsigned sp + -144) in F4 by lia.
    apply w4ck_cells in F1, F2, F3, F4.
    pose proof (w4ck_rg p1) as R1. pose proof (w4ck_rg a1) as R2. pose proof (w4ck_rg p2) as R3. pose proof (w4ck_rg a2) as R4.
    pose proof (w4ck_rg p3) as R5. pose proof (w4ck_rg a3) as R6. pose proof (w4ck_rg p4) as R7. pose proof (w4ck_rg a4) as R8.
    pose proof (Z.mod_pos_bound (bv_unsigned bw1) (2^32) ltac:(lia)) as B1.
    pose proof (Z.mod_pos_bound (bv_unsigned bw2) (2^32) ltac:(lia)) as B2.
    pose proof (Z.mod_pos_bound (bv_unsigned bw3) (2^32) ltac:(lia)) as B3.
    pose proof (Z.mod_pos_bound (bv_unsigned bw4) (2^32) ltac:(lia)) as B4.
    unfold AW4_CK.
    eapply w4s34_ck1 with (P := bv_unsigned p1) (A := bv_unsigned a1) (B := bv_unsigned bw1 mod 2^32) (pad := pad1) (c := c1) (e := e1);
      [exact F1 | exact MI | exact HR | lia .. | intros y10 y11 y12 y13 y14].
    eapply w4s34_ck2 with (P := bv_unsigned p2) (A := bv_unsigned a2) (B := bv_unsigned bw2 mod 2^32) (pad := pad2) (c := c2) (e := e2)
      (DST := DST) (dcap := dcap) (seg := (dcap + 3) / 4);
      [exact F0 | exact F4 | exact MI | exact HR | lia .. | intros z10 z11 z12 z13 z14].
    eapply w4s34_ck3 with (P := bv_unsigned p3) (A := bv_unsigned a3) (B := bv_unsigned bw3 mod 2^32) (pad := pad3) (c := c3) (e := e3);
      [exact F3 | exact MI | exact HR | lia .. | intros u10 u11 u12 u13 u14].
    eapply w4s34_ck4 with (P := bv_unsigned p4) (A := bv_unsigned a4) (B := bv_unsigned bw4 mod 2^32) (pad := pad4) (c := c4) (e := e4);
      [exact F2 | exact MI | exact HR | lia .. | intros v10 v11 v12 v13 v14].
    rewrite <- (Z_to_bv_bv_unsigned v10).
    eapply w4s34_ck5 with (V := bv_unsigned v10); [exact MI | exact HR | lia | apply w4ck_rg | intros t10 t11 t12 t13 t14].
    eapply w4_err; eassumption.
  Qed.
End W4CK.

End CANSEC1.
