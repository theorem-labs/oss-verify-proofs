(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 1310 of its 1364 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacMasterOnlyCadenceNs.v, with its module paths and module names changed; 225 of its 250 lines of code are new or changed and 1339 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_L1 : Z := 0x304.
Definition RBN_L1X : Z := 0x370.
Definition RBN_L2 : Z := 0x3f4.
Definition RBN_L2X : Z := 0x460.
Definition RBN_L3 : Z := 0x4d8.
Definition RBN_L3X : Z := 0x568.
Definition RBN_L4 : Z := 0x5dc.
Definition RBN_L4X : Z := 0x648.
Definition RBN_L5 : Z := 0x670.
Definition RBN_L5X : Z := 0x6dc.
Definition RBN_L6 : Z := 0x718.
Definition RBN_L6X : Z := 0x788.
Definition RBN_L7 : Z := 0x7c0.
Definition RBN_L7X : Z := 0x830.
Definition rbn_lit5 : list Z := [32; 40].
Definition rbn_lit6 : list Z := [32; 105; 110; 32; 47; 32].
Definition rbn_lit7 : list Z := [32; 111; 117; 116; 41].
Definition rbn_keep_regs (regs regs2 : bvmap 5 word) (cl : list Z) : Prop :=
  forall r, 0 <= r < 32 -> ~ In r cl -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition rbn_lsrc (W : world SEGS) (memc : word -> option byte) (P : Z) (l : list Z) : Prop :=
  garr8 SEGS (mrestrict (w_H W) memc) P l /\ 0 <= P /\ P + Z.of_nat (length l) <= 2 ^ 63 /\
  P + Z.of_nat (length l) <= 2 ^ 47 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF P (Z.of_nat (length l)).
Section h.
Variable B : asyms.
Definition rbn_lbuf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (D n : Z) : Prop :=
  0 <= D /\ D + n <= 2 ^ 63 /\ in_app D n /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D n /\
  (forall a, D <= a < D + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a).
Definition rbn_lpost (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (ex : Z) (cl : list Z)
  (D n0 : Z) (wr : list Z) (outs : list (Z * Z)) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + ex) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    rbn_keep_regs regs regs2 cl /\
    Forall (fun p => getr regs2 (Z_to_bv 5 (fst p)) = w64 (snd p)) outs /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + Z.of_nat (length wr)) ->
       aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
    garr8 SEGS (mrestrict (w_H W) mem2) (D + n0) wr.
Definition rbn_L1_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (P + Z.of_nat (length s) + 1 <= D \/ D + 24 <= P) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 24 = w64 n0 -> getr regs 30 = w64 ov0 -> getr regs 15 = w64 (hd 0 s) ->
  getr regs 13 = w64 (P + 1) -> getr regs 10 = w64 (P + 1) -> getr regs 14 = w64 23 ->
  getr regs 27 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L1) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L1X [5; 10; 11; 13; 15; 16; 17; 24; 30]
       D n0 wr [(24, nF); (30, ovF)]).
Definition rbn_L1_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  n0 + Z.of_nat (length s) <= 23 ->
  rbn_L1_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (n0 + Z.of_nat (length s)) ov0 s.
Definition rbn_L1_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  23 < n0 + Z.of_nat (length s) ->
  rbn_L1_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    23 1 (firstn (Z.to_nat (23 - n0)) s).
Definition rbn_L2_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (P + Z.of_nat (length s) + 1 <= D \/ D + 24 <= P) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 24 = w64 n0 -> getr regs 30 = w64 ov0 -> getr regs 13 = w64 (hd 0 s) ->
  getr regs 21 = w64 (P + 1) -> getr regs 10 = w64 (P + 1) -> getr regs 12 = w64 23 ->
  getr regs 27 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L2) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L2X [10; 11; 13; 14; 15; 16; 21; 24; 30]
       D n0 wr [(24, nF); (30, ovF)]).
Definition rbn_L2_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  n0 + Z.of_nat (length s) <= 23 ->
  rbn_L2_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (n0 + Z.of_nat (length s)) ov0 s.
Definition rbn_L2_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  23 < n0 + Z.of_nat (length s) ->
  rbn_L2_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    23 1 (firstn (Z.to_nat (23 - n0)) s).
Definition rbn_L3_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (N D : Z) (l : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (1 <= length l)%nat -> Forall (fun c => 0 <= c < 256) l -> rbn_lsrc W memc N l ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (N + Z.of_nat (length l) <= D \/ D + 24 <= N) ->
  getr regs 12 = w64 0 -> getr regs 26 = w64 0 -> getr regs 13 = w64 0 -> getr regs 14 = w64 45 ->
  getr regs 15 = w64 23 -> getr regs 16 = w64 N -> getr regs 10 = w64 N ->
  getr regs 17 = w64 (Z.of_nat (length l)) -> getr regs 29 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L3) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X [5; 6; 7; 10; 11; 12; 13; 16; 17; 26; 28]
       D 0 wr [(26, nF); (13, ovF)]).
Definition rbn_L3_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l,
  Z.of_nat (length (bn_TK l)) <= 23 ->
  rbn_L3_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l
    (Z.of_nat (length (bn_TK l))) 0 (bn_TK l).
Definition rbn_L3_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l,
  23 < Z.of_nat (length (bn_TK l)) ->
  rbn_L3_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l
    23 1 (firstn 23 (bn_TK l)).
Definition rbn_L4_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (P + Z.of_nat (length s) + 1 <= D \/ D + 48 <= P) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 11 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 15 = w64 (hd 0 s) ->
  getr regs 13 = w64 (P + 1) -> getr regs 10 = w64 (P + 1) -> getr regs 14 = w64 47 ->
  getr regs 20 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L4) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L4X [5; 10; 11; 12; 13; 15; 16; 17]
       D n0 wr [(11, nF); (12, ovF)]).
Definition rbn_L4_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  n0 + Z.of_nat (length s) <= 47 ->
  rbn_L4_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (n0 + Z.of_nat (length s)) ov0 s.
Definition rbn_L4_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  47 < n0 + Z.of_nat (length s) ->
  rbn_L4_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    47 1 (firstn (Z.to_nat (47 - n0)) s).
Definition rbn_L5_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]) ->
  VAL (A_OBJ 28) mod 8 = 0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 28) + 3 <= D \/ D + 48 <= VAL (A_OBJ 28)) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 16 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 17 = w64 32 -> getr regs 11 = w64 1 ->
  getr regs 15 = w64 3 -> getr regs 13 = w64 47 -> getr regs 14 = w64 (VAL (A_OBJ 28)) ->
  getr regs 20 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L5) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L5X [5; 6; 10; 11; 12; 16; 17]
       D n0 wr [(16, nF); (12, ovF)]).
Definition rbn_L5_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  n0 + 2 <= 47 ->
  rbn_L5_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 (n0 + 2) ov0 rbn_lit5.
Definition rbn_L5_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  47 < n0 + 2 ->
  rbn_L5_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit5).
Definition rbn_L6_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (A1 D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 29)) (rbn_lit6 ++ [0]) ->
  VAL (A_OBJ 29) mod 8 = 0 -> alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 29) \/ VAL (A_OBJ 29) + 7 <= A1 + 120) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 29) + 7 <= D \/ D + 48 <= VAL (A_OBJ 29)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 15 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 16 = w64 32 -> getr regs 23 = w64 1 ->
  getr regs 14 = w64 7 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 29)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L6) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X [5; 10; 12; 15; 16; 17; 23]
       D n0 wr [(15, nF); (12, ovF)]).
Definition rbn_L6_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  n0 + 6 <= 47 ->
  rbn_L6_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 (n0 + 6) ov0 rbn_lit6.
Definition rbn_L6_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  47 < n0 + 6 ->
  rbn_L6_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit6).
Definition rbn_L7_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (A1 D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 30)) (rbn_lit7 ++ [0]) ->
  VAL (A_OBJ 30) mod 8 = 0 -> alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 6 <= A1 + 120) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 30) + 6 <= D \/ D + 48 <= VAL (A_OBJ 30)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 23 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 15 = w64 32 -> getr regs 21 = w64 1 ->
  getr regs 14 = w64 6 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 30)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L7) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X [5; 10; 12; 15; 16; 17; 21; 23]
       D n0 wr [(23, nF); (12, ovF)]).
Definition rbn_L7_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  n0 + 5 <= 47 ->
  rbn_L7_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 (n0 + 5) ov0 rbn_lit7.
Definition rbn_L7_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  47 < n0 + 5 ->
  rbn_L7_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit7).
End h.
End f.
End d.
