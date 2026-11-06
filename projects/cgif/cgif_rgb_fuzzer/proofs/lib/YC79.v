(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YP15 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7c YC77 YC78.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition HL_RA1R : Z := 0x82af8.
Definition HL_RA2R : Z := 0x82b20.
Definition HL_MA1R : Z := 0x82b2c.
Definition HL_MA2R : Z := 0x82b3c.
Definition HL_MA3R : Z := 0x82b48.
Definition HL_FAIL : Z := 0x83a90.
Definition HL_MSR : Z := 0x82bb0.
Definition A_realloc_tra : Z := 0x53108.
Definition A_malloc_tra : Z := 0x53104.
Definition A_free_tra : Z := 0x53100.
Definition ac_Tn (C : acht) : Z := getNextPrimePower2 (ac_T C).
Definition rz_BL (C : acht) (p1 x1 : Z) : list (Z * Z) :=
[(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C); rbk (ac_p C, 3 * ac_T C) p1 (3 * ac_Tn C); rbk (ac_x C, 4 * ac_T C) x1 (4 * ac_Tn C)].
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Local Notation rcore := (rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hspill := (hspill s1v).
Definition rz_old (W : world trasegs) (mem : word -> option byte) (C : acht) : Prop :=
arr32 trasegs (mrestrict (w_H W) mem) (ac_f C) (ht_frequ (ac_H C)) /\ arr8 trasegs (mrestrict (w_H W) mem) (ac_h C) (ht_keys (ac_H C)) /\
arr8 trasegs (mrestrict (w_H W) mem) (ac_u C) (ht_used (ac_H C)).
Definition rz_facts (C : acht) (i ha : Z) : Prop :=
ht_inv (ac_H C) (ac_ent C) /\ In (ac_T C) ts_chain /\ ac_T C < MAX_TABLE_SIZE /\
0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ zsum (map snd (ac_ent C)) <= i + 1.
Definition slot_is (W : world trasegs) (mem : word -> option byte) (off v : Z) : Prop :=
val_mem trasegs (mrestrict (w_H W) mem) (s1v + off) 8 v.
Definition rz_common (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha d : Z) (BL : list (Z * Z)) : Prop :=
rcore lyc Sc W regs mem md k (ac_cells C) BL /\ rz_old W mem C /\ rz_facts C i ha /\
(k <= 8 + 12 * ts_rank (ac_T C) + d /\ gbud S Sc k) /\ hspill W mem i ha /\
getr regs 20 = Z_to_bv 64 (3 * ac_Tn C) /\ getr regs 21 = Z_to_bv 64 (tb + 24) /\ getr regs 22 = Z_to_bv 64 (ac_Tn C) /\
getr regs 26 = Z_to_bv 64 hv26  .
Definition at_RA1C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 0 (ac_arrs C) /\
getr regs 10 = Z_to_bv 64 (ac_p C) /\ getr regs 11 = Z_to_bv 64 (3 * ac_Tn C) /\ getr regs 1 = Z_to_bv 64 HL_RA1R.
Definition rz_ok1 (v : Z) : Prop := v = 0 \/ 4096 <= v < 2 ^ 47.
Definition at_RA1R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 3 (rz_BL C p1 0) /\ rz_ok1 p1 /\ getr regs 10 = Z_to_bv 64 p1.
Definition at_RA2C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 3 (rz_BL C p1 0) /\ rz_ok1 p1 /\
getr regs 23 = Z_to_bv 64 p1 /\ getr regs 24 = Z_to_bv 64 (4 * ac_Tn C) /\
getr regs 10 = Z_to_bv 64 (ac_x C) /\ getr regs 11 = Z_to_bv 64 (4 * ac_Tn C) /\ getr regs 1 = Z_to_bv 64 HL_RA2R.
Definition rz_res (regs : bvmap 5 word) (C : acht) (p1 x1 : Z) : Prop :=
rz_ok1 p1 /\ rz_ok1 x1 /\ getr regs 23 = Z_to_bv 64 p1 /\ getr regs 24 = Z_to_bv 64 (4 * ac_Tn C) /\ getr regs 27 = Z_to_bv 64 x1.
Definition at_RA2R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 6 (rz_BL C p1 x1) /\ rz_ok1 p1 /\ rz_ok1 x1 /\
getr regs 23 = Z_to_bv 64 p1 /\ getr regs 24 = Z_to_bv 64 (4 * ac_Tn C) /\ getr regs 10 = Z_to_bv 64 x1.
Definition at_MA1C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 6 (rz_BL C p1 x1) /\ rz_res regs C p1 x1 /\
getr regs 10 = Z_to_bv 64 (3 * ac_Tn C) /\ getr regs 1 = Z_to_bv 64 HL_MA1R.
Definition at_MA1R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 7 (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) /\ rz_res regs C p1 x1 /\ rz_ok1 h1 /\
getr regs 10 = Z_to_bv 64 h1.
Definition at_MA2C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 7 (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) /\ rz_res regs C p1 x1 /\ rz_ok1 h1 /\
slot_is W mem 176 h1 /\ slot_is W mem 160 (ac_Tn C) /\
getr regs 10 = Z_to_bv 64 (ac_Tn C) /\ getr regs 1 = Z_to_bv 64 HL_MA2R.
Definition at_MA2R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 8 ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) /\ rz_res regs C p1 x1 /\ rz_ok1 h1 /\ rz_ok1 u1 /\
slot_is W mem 176 h1 /\ slot_is W mem 160 (ac_Tn C) /\
getr regs 10 = Z_to_bv 64 u1.
Definition at_MA3C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 8 ((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) /\ rz_res regs C p1 x1 /\ rz_ok1 h1 /\ rz_ok1 u1 /\
slot_is W mem 176 h1 /\ slot_is W mem 160 (ac_Tn C) /\ slot_is W mem 296 u1 /\
getr regs 10 = Z_to_bv 64 (4 * ac_Tn C) /\ getr regs 1 = Z_to_bv 64 HL_MA3R.
Definition at_MA3R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) /\
rz_res regs C p1 x1 /\ rz_ok1 h1 /\ rz_ok1 u1 /\ rz_ok1 f1 /\
slot_is W mem 176 h1 /\ slot_is W mem 160 (ac_Tn C) /\ slot_is W mem 296 u1 /\
getr regs 10 = Z_to_bv 64 f1.
Definition at_FAIL (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) : Prop :=
rz_common lyc Sc W regs mem md k C i ha 9 (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C)) /\
rz_res regs C p1 x1 /\ rz_ok1 h1 /\ rz_ok1 u1 /\ rz_ok1 f1 /\
slot_is W mem 176 h1 /\ slot_is W mem 296 u1 /\ slot_is W mem 168 f1 /\
(p1 = 0 \/ x1 = 0 \/ h1 = 0 \/ u1 = 0 \/ f1 = 0).
Definition rh_cells (C : acht) (p1 x1 cnt : Z) : list Z := [ac_f C; ac_h C; ac_u C; p1; x1; cnt; ac_T C].
Definition rh_BL (C : acht) (p1 x1 h1 u1 f1 : Z) : list (Z * Z) :=
[(ac_f C, 4 * ac_T C); (ac_h C, 3 * ac_T C); (ac_u C, ac_T C);
(p1, 3 * ac_Tn C); (x1, 4 * ac_Tn C); (h1, 3 * ac_Tn C); (u1, ac_Tn C); (f1, 4 * ac_Tn C)].
Definition rh_slots (W : world trasegs) (mem : word -> option byte) (C : acht) (h1 u1 f1 : Z) : Prop :=
slot_is W mem 160 (ac_Tn C) /\ slot_is W mem 168 f1 /\ slot_is W mem 176 h1 /\ slot_is W mem 296 u1.
Definition rh_ptr (v : Z) : Prop := 4096 <= v < 2 ^ 47.
Definition rh_pre (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 cnt : Z) : Prop :=
rcore lyc Sc W regs mem md k (rh_cells C p1 x1 cnt) (rh_BL C p1 x1 h1 u1 f1) /\ rz_old W mem C /\ rz_facts C i ha /\
(k <= 8 + 12 * ts_rank (ac_T C) + 9 /\ gbud S Sc k) /\ hspill W mem i ha /\ rh_slots W mem C h1 u1 f1 /\
rh_ptr p1 /\ rh_ptr x1 /\ rh_ptr h1 /\ rh_ptr u1 /\ rh_ptr f1.
Definition at_MSC (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) : Prop :=
rh_pre lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (ht_cnt (ac_H C)) /\
getr regs 10 = Z_to_bv 64 u1 /\ getr regs 11 = Z_to_bv 64 0 /\ getr regs 12 = Z_to_bv 64 (ac_Tn C) /\ getr regs 1 = Z_to_bv 64 HL_MSR /\
getr regs 20 = Z_to_bv 64 tb /\ getr regs 21 = Z_to_bv 64 (tb + 40).
Definition rh_innew (C : acht) (p1 x1 h1 u1 f1 a : Z) : Prop :=
p1 <= a < p1 + req_size (3 * ac_Tn C) \/ x1 <= a < x1 + req_size (4 * ac_Tn C) \/ h1 <= a < h1 + req_size (3 * ac_Tn C) \/
u1 <= a < u1 + req_size (ac_Tn C) \/ f1 <= a < f1 + req_size (4 * ac_Tn C).
Definition at_MSR (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) : Prop :=
rh_pre lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (ht_cnt (ac_H C)) /\
(forall j, 0 <= j < ac_Tn C -> aview trasegs (w_H W) mem (u1 + j) = Some 0) /\
getr regs 20 = Z_to_bv 64 tb /\ getr regs 21 = Z_to_bv 64 (tb + 40).
Definition rh_new (W : world trasegs) (mem : word -> option byte) (C : acht) (p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
cht_arrays trasegs (mrestrict (w_H W) mem) f1 h1 u1 p1 x1 K /\ ht_lens K /\ ht_T K = ac_Tn C.
Definition rh_common (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rh_pre lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (ht_cnt K) /\ rh_new W mem C p1 x1 h1 u1 f1 K.
Definition rh_loop_regs (regs : bvmap 5 word) (j : Z) : Prop :=
getr regs 21 = Z_to_bv 64 j /\ getr regs 26 = Z_to_bv 64 (4 * j) /\ getr regs 27 = Z_to_bv 64 (3 * j) /\ getr regs 5 = Z_to_bv 64 1 /\
getr regs 15 = Z_to_bv 64 (tb + 44) /\ getr regs 16 = Z_to_bv 64 (tb + 8) /\ getr regs 17 = Z_to_bv 64 (tb + 16) /\ getr regs 20 = Z_to_bv 64 tb.
Definition HL_LH : Z := 0x82bf0.
Definition at_LH (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K /\ ht_inv K (ents_below (ac_H C) j) /\ 0 <= j < ac_T C /\ rh_loop_regs regs j.
Definition HL_LN : Z := 0x82da4.
Definition HL_CHR : Z := 0x82c5c.
Definition HL_RM1R : Z := 0x82c80.
Definition HL_RM2R : Z := 0x82ce4.
Definition HL_DONE : Z := 0x82e2c.
Definition at_LN (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K /\ ht_inv K (ents_below (ac_H C) (j + 1)) /\ 0 <= j < ac_T C /\ rh_loop_regs regs j.
Definition rh_used_regs (regs : bvmap 5 word) (C : acht) (h1 j : Z) : Prop :=
getr regs 20 = Z_to_bv 64 (3 * j) /\ getr regs 21 = Z_to_bv 64 j /\ getr regs 22 = Z_to_bv 64 h1 /\
getr regs 26 = Z_to_bv 64 (4 * j) /\ getr regs 27 = Z_to_bv 64 (3 * j).
Definition rh_used_ghost (C : acht) (K : htab) (j h2 : Z) : Prop :=
ht_inv K (ents_below (ac_H C) j) /\ 0 <= j < ac_T C /\ usedz (ac_H C) j = 1 /\
find_slot K (key (ac_H C) j) = Some h2 /\ 0 <= h2 < ht_T K /\ usedz K h2 = 0 /\ ht_cnt K + 1 <= ht_cnt (ac_H C) /\
ht_inv (ht_ins K h2 (key (ac_H C) j) (freq (ac_H C) j)) (ents_below (ac_H C) (j + 1)).
Definition at_CHC (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j h2 : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K /\ rh_used_ghost C K j h2 /\ rh_used_regs regs C h1 j /\
getr regs 24 = Z_to_bv 64 (ac_h C + 3 * j) /\
getr regs 10 = Z_to_bv 64 (ac_h C + 3 * j) /\ getr regs 11 = Z_to_bv 64 h1 /\ getr regs 12 = Z_to_bv 64 u1 /\ getr regs 13 = Z_to_bv 64 (ac_Tn C) /\
getr regs 14 = Z_to_bv 64 3 /\ getr regs 1 = Z_to_bv 64 HL_CHR.
Definition at_CHR (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j h2 : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K /\ rh_used_ghost C K j h2 /\ rh_used_regs regs C h1 j /\
getr regs 24 = Z_to_bv 64 (ac_h C + 3 * j) /\ getr regs 10 = Z_to_bv 64 h2.
Definition K_m1 (K : htab) (h2 : Z) (c : colour) : htab :=
mkHT (ht_frequ K) (set_col (ht_keys K) h2 c) (ht_used K) (ht_pal K) (ht_colidx K) (ht_cnt K) (ht_T K).
Definition K_m2 (K : htab) (h2 : Z) (c : colour) : htab :=
mkHT (ht_frequ K) (set_col (ht_keys K) h2 c) (ht_used K) (set_col (ht_pal K) (ht_cnt K) c) (ht_colidx K) (ht_cnt K) (ht_T K).
Definition at_RM1C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j h2 : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K /\ rh_used_ghost C K j h2 /\ rh_used_regs regs C h1 j /\
getr regs 23 = Z_to_bv 64 h2 /\ getr regs 24 = Z_to_bv 64 (ac_h C + 3 * j) /\
getr regs 10 = Z_to_bv 64 (h1 + 3 * h2) /\ getr regs 11 = Z_to_bv 64 (ac_h C + 3 * j) /\ getr regs 12 = Z_to_bv 64 3 /\ getr regs 1 = Z_to_bv 64 HL_RM1R.
Definition at_RM1R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j h2 : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (K_m1 K h2 (key (ac_H C) j)) /\ rh_used_ghost C K j h2 /\ rh_used_regs regs C h1 j /\
getr regs 23 = Z_to_bv 64 h2.
Definition at_RM2C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j h2 : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (K_m1 K h2 (key (ac_H C) j)) /\ rh_used_ghost C K j h2 /\ rh_used_regs regs C h1 j /\
getr regs 23 = Z_to_bv 64 h2 /\ getr regs 24 = Z_to_bv 64 (tb + 40) /\
getr regs 10 = Z_to_bv 64 (p1 + 3 * ht_cnt K) /\ getr regs 11 = Z_to_bv 64 (ac_h C + 3 * j) /\ getr regs 12 = Z_to_bv 64 3 /\ getr regs 1 = Z_to_bv 64 HL_RM2R.
Definition at_RM2R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (j h2 : Z) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (K_m2 K h2 (key (ac_H C) j)) /\ rh_used_ghost C K j h2 /\ rh_used_regs regs C h1 j /\
getr regs 23 = Z_to_bv 64 h2 /\ getr regs 24 = Z_to_bv 64 (tb + 40).
End b.
