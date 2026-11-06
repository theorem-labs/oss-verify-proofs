(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_cuts.v, with its module paths, module names, addresses and numbers changed; 169 of its 287 lines of code are new or changed and 517 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_L1 : Z := 0x314.
Definition RBN_L1X : Z := 0x358.
Definition RBN_L2 : Z := 0x3b4.
Definition RBN_L2X : Z := 0x3f8.
Definition RBN_L3 : Z := 0x454.
Definition RBN_L3X : Z := 0x4bc.
Definition RBN_L4 : Z := 0x524.
Definition RBN_L4X : Z := 0x568.
Definition RBN_L5 : Z := 0x578.
Definition RBN_L5X : Z := 0x5b4.
Definition RBN_L6 : Z := 0x5d4.
Definition RBN_L6X : Z := 0x610.
Definition RBN_L7 : Z := 0x630.
Definition RBN_L7X : Z := 0x66c.
Definition rbn_lit5 : list Z := [32; 40].
Definition rbn_lit6 : list Z := [32; 105; 110; 32; 47; 32].
Definition rbn_lit7 : list Z := [32; 111; 117; 116; 41].
Definition rbn_keep_regs (regs regs2 : bvmap 5 word) (cl : list Z) : Prop :=
  forall r, 0 <= r < 32 -> ~ In r cl -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition rbn_clc : list Z := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].
Definition rbn_cl1 : list Z := rbn_clc ++ [21; 26].
Definition rbn_cl2 : list Z := rbn_clc ++ [20; 21].
Definition rbn_cl3 : list Z := rbn_clc ++ [21; 26].
Definition rbn_cl4 : list Z := rbn_clc ++ [20; 24].
Definition rbn_cl5 : list Z := rbn_clc ++ [20].
Definition rbn_lsep (sp R D cap P n : Z) : Prop :=
  (P + n <= D \/ D + cap <= P) /\ (P + n <= R \/ R + 28 <= P) /\
  (sp <= P \/ P + n <= sp - TSB_CH_STK).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition rbn_lsrc (W : world SEGS) (memc : word -> option byte) (P : Z) (l : list Z) : Prop :=
  garr8 SEGS (mrestrict (w_H W) memc) P l /\ 0 <= P /\ P + Z.of_nat (length l) <= 2 ^ 63 /\
  P + Z.of_nat (length l) <= 2 ^ 47 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF P (Z.of_nat (length l)).
Section h.
Variable B : asyms.
Definition rbn_lcx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 9 = getr regs 2 /\ getr regs 22 = w64 SHADOW_OFF /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - TSB_CH_STK /\ spZ regs <= sp0.
Definition rbn_lrec (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (sp R D cap n ov : Z) : Prop :=
  0 < R /\ R mod 8 = 0 /\ R + 28 <= 2 ^ 63 /\ amem_range R 28 /\ off_img R 28 /\
  (sp <= R \/ R + 28 <= sp - TSB_CH_STK) /\
  0 <= D < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\ 0 <= n /\ n + 1 < 2 ^ 64 - 3 /\ 0 <= ov < 2 ^ 32 /\
  val_mem SEGS (mrestrict (w_H W) memc) R 8 D /\
  val_mem SEGS (mrestrict (w_H W) memc) (R + 8) 8 cap /\
  val_mem SEGS (mrestrict (w_H W) memc) (R + 16) 8 n /\
  val_mem SEGS (mrestrict (w_H W) memc) (R + 24) 4 ov /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF R 28 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) R 28 /\
  (forall a, R + 16 <= a < R + 28 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a).
Definition rbn_lbuf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (sp R D cap : Z) : Prop :=
  0 < D /\ D + cap <= 2 ^ 63 /\ in_app D cap /\ amem_range D cap /\ off_img D cap /\
  (sp <= D \/ D + cap <= sp - TSB_CH_STK) /\ (D + cap <= R \/ R + 28 <= D) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D cap /\
  shadow_hull_vis (aview SEGS (w_H W) memc) D cap /\
  (forall a, D <= a < D + cap ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a).
Definition rbn_lpost (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (ex : Z) (cl : list Z)
  (R D n0 nF ovF : Z) (wr : list Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists lyc2 Sc2 regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + ex) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc2 Sc2 W2 mem2 md2 k /\
    frames Sc2 = frames Sc /\ ablocks B lyc2 Sc2 = ablocks B lyc Sc /\
    arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) /\
    rbn_keep_regs regs regs2 cl /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (R + 16) 8 nF /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (R + 24) 4 ovF /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (D + n0) wr /\
    tsb_ch_kept B lyc Sc W memc W2 mem2 (spZ regs)
      (fun a => R + 16 <= a < R + 28 \/ D + n0 <= a < D + n0 + Z.of_nat (length wr)).
Definition rbn_L1_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 n0 ov0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lsep (spZ regs) (spZ regs + 152) D 24 P (Z.of_nat (length s) + 1) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 10 = w64 (hd 0 s) -> getr regs 21 = w64 P -> getr regs 26 = w64 (P + 1) ->
  getr regs 24 = w64 (-1) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L1) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L1X rbn_cl1
       (spZ regs + 152) D n0 nF ovF wr).
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
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 n0 ov0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lsep (spZ regs) (spZ regs + 152) D 24 P (Z.of_nat (length s) + 1) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 10 = w64 (hd 0 s) -> getr regs 20 = w64 P -> getr regs 21 = w64 (P + 1) ->
  getr regs 24 = w64 (-1) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L2) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L2X rbn_cl2
       (spZ regs + 152) D n0 nF ovF wr).
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
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 120) D 24 0 0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 120) D 24 ->
  (1 <= length l)%nat -> Z.of_nat (length l) <= 23 -> Forall (fun c => 0 <= c < 256) l ->
  rbn_lsrc W memc N l ->
  rbn_lsep (spZ regs) (spZ regs + 120) D 24 N (Z.of_nat (length l)) ->
  (N + Z.of_nat (length l) <= spZ regs + 152 \/ spZ regs + 180 <= N) ->
  (D + 24 <= spZ regs + 152 \/ spZ regs + 180 <= D) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 168) 8 (Z.of_nat (length l)) ->
  getr regs 20 = w64 24 -> getr regs 21 = w64 0 -> getr regs 24 = w64 45 -> getr regs 26 = w64 0 ->
  getr regs 27 = w64 N ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L3) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X rbn_cl3
       (spZ regs + 120) D 0 nF ovF wr).
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
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 P (Z.of_nat (length s) + 1) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 10 = w64 (hd 0 s) -> getr regs 24 = w64 P -> getr regs 20 = w64 (P + 1) ->
  getr regs 21 = w64 (-1) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L4) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L4X rbn_cl4
       (spZ regs + 88) D n0 nF ovF wr).
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
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]) -> VAL (A_OBJ 28) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 28)) 3 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 28)) -> getr regs 24 = w64 2 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L5) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L5X rbn_cl5
       (spZ regs + 88) D n0 nF ovF wr).
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
  (D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 29)) (rbn_lit6 ++ [0]) -> VAL (A_OBJ 29) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 29)) 7 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 29)) -> getr regs 24 = w64 6 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L6) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X rbn_cl5
       (spZ regs + 88) D n0 nF ovF wr).
Definition rbn_L6_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  n0 + 6 <= 47 ->
  rbn_L6_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 (n0 + 6) ov0 rbn_lit6.
Definition rbn_L6_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  47 < n0 + 6 ->
  rbn_L6_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit6).
Definition rbn_L7_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  rbn_lcx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 30)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 30) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 30)) 6 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 30)) -> getr regs 24 = w64 5 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L7) regs memc mdc)
    (rbn_lpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X rbn_cl5
       (spZ regs + 88) D n0 nF ovF wr).
Definition rbn_L7_fits : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  n0 + 5 <= 47 ->
  rbn_L7_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 (n0 + 5) ov0 rbn_lit7.
Definition rbn_L7_ovf : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  47 < n0 + 5 ->
  rbn_L7_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit7).
End h.
End f.
End d.
