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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7c YC77 YC78 YC79 YC7a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition HL_FF1R : Z := 0x83ad4.
Definition HL_FF2R : Z := 0x83adc.
Definition HL_FF3R : Z := 0x83ae4.
Definition HL_XF : Z := 0x83ae8.
Definition rsel (old new : Z) : Z := if new =? 0 then old else new.
Definition xf_cells (C : acht) (p1 x1 : Z) : list Z := [ac_f C; ac_h C; ac_u C; rsel (ac_p C) p1; rsel (ac_x C) x1; ht_cnt (ac_H C); ac_T C].
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
Local Notation hspill := (hspill s1v).
Local Notation slot_is := (slot_is s1v).
Local Notation rz_facts := (rz_facts fmt N).
Definition xf_common (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 : Z) (BL : list (Z * Z)) (d : Z) : Prop :=
rcore lyc Sc W regs mem md k (xf_cells C p1 x1) BL /\ rz_facts C i ha /\ k <= 8 + 12 * ts_rank (ac_T C) + 9 + d /\ hspill W mem i ha /\
rz_ok1 p1 /\ rz_ok1 x1 /\ getr regs 20 = Z_to_bv 64 tb /\ getr regs 24 = Z_to_bv 64 hv24 /\ getr regs 26 = Z_to_bv 64 hv26.
Definition at_FF1C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 h1 u1 f1 : Z) : Prop :=
xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C) ++ optb u1 (ac_Tn C) ++ optb f1 (4 * ac_Tn C)) 0 /\
rz_ok1 h1 /\ rz_ok1 u1 /\ rz_ok1 f1 /\ slot_is W mem 296 u1 /\ slot_is W mem 168 f1 /\
getr regs 10 = Z_to_bv 64 h1 /\ getr regs 1 = Z_to_bv 64 HL_FF1R.
Definition at_FF1R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 u1 f1 : Z) : Prop :=
xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb u1 (ac_Tn C) ++ optb f1 (4 * ac_Tn C)) 1 /\
rz_ok1 u1 /\ rz_ok1 f1 /\ slot_is W mem 296 u1 /\ slot_is W mem 168 f1.
Definition at_FF2C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 u1 f1 : Z) : Prop :=
at_FF1R lyc Sc W regs mem md k C i ha p1 x1 u1 f1 /\ getr regs 10 = Z_to_bv 64 u1 /\ getr regs 1 = Z_to_bv 64 HL_FF2R.
Definition at_FF2R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 f1 : Z) : Prop :=
xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb f1 (4 * ac_Tn C)) 2 /\ rz_ok1 f1 /\ slot_is W mem 168 f1.
Definition at_FF3C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 f1 : Z) : Prop :=
at_FF2R lyc Sc W regs mem md k C i ha p1 x1 f1 /\ getr regs 10 = Z_to_bv 64 f1 /\ getr regs 1 = Z_to_bv 64 HL_FF3R.
Definition at_FF3R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 : Z) : Prop :=
xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1) 3.
Definition at_XF (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha p1 x1 : Z) : Prop :=
xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1) 3 /\ getr regs 27 = Z_to_bv 64 hv27.
End a.
