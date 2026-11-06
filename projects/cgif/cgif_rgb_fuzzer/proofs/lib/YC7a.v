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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7c YC77 YC78 YC79.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition HL_F1R : Z := 0x82e5c.
Definition HL_F2R : Z := 0x82e74.
Definition HL_F3R : Z := 0x82e8c.
Definition ac_new (C : acht) (p1 x1 h1 u1 f1 : Z) (K : htab) : acht := mkACHT f1 h1 u1 p1 x1 K (ents_below (ac_H C) (ac_T C)).
Section a.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Local Notation rcore := (rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rh_common := (rh_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hspill := (hspill s1v).
Local Notation rh_slots := (rh_slots s1v).
Local Notation rz_facts := (rz_facts fmt N).
Definition at_DONE (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K /\ ht_inv K (ents_below (ac_H C) (ac_T C)) /\
getr regs 15 = Z_to_bv 64 (tb + 44) /\ getr regs 16 = Z_to_bv 64 (tb + 8) /\ getr regs 20 = Z_to_bv 64 tb.
Definition rf_common (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) (BL : list (Z * Z)) (d : Z) : Prop :=
rcore lyc Sc W regs mem md k [ac_f C; ac_h C; ac_u C; p1; x1; ht_cnt K; ac_Tn C] BL /\
rh_new W mem C p1 x1 h1 u1 f1 K /\ ht_inv K (ents_below (ac_H C) (ac_T C)) /\ rz_facts C i ha /\
(k <= 8 + 12 * ts_rank (ac_T C) + 9 + d /\ gbud S Sc k) /\ hspill W mem i ha /\ rh_slots W mem C h1 u1 f1 /\
rh_ptr p1 /\ rh_ptr x1 /\ rh_ptr h1 /\ rh_ptr u1 /\ rh_ptr f1 /\
getr regs 20 = Z_to_bv 64 tb /\ getr regs 27 = Z_to_bv 64 hv27.
Definition rf_new5 (C : acht) (p1 x1 h1 u1 f1 : Z) : list (Z * Z) :=
[(p1, 3 * ac_Tn C); (x1, 4 * ac_Tn C); (h1, 3 * ac_Tn C); (u1, ac_Tn C); (f1, 4 * ac_Tn C)].
Definition at_F1C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K (rh_BL C p1 x1 h1 u1 f1) 0 /\
getr regs 10 = Z_to_bv 64 (ac_h C) /\ getr regs 1 = Z_to_bv 64 HL_F1R.
Definition at_F1R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: (ac_u C, ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 1.
Definition at_F2C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: (ac_u C, ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 1 /\
getr regs 10 = Z_to_bv 64 (ac_u C) /\ getr regs 1 = Z_to_bv 64 HL_F2R.
Definition at_F2R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 2.
Definition at_F3C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 2 /\
getr regs 10 = Z_to_bv 64 (ac_f C) /\ getr regs 1 = Z_to_bv 64 HL_F3R.
Definition at_F3R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K (rf_new5 C p1 x1 h1 u1 f1) 3.
End a.
