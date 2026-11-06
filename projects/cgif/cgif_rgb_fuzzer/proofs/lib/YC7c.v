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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition HL_BR : Z := 0x827dc.
Definition HL_PA : Z := 0x8286c.
Definition HL_M1R : Z := 0x828fc.
Definition HL_M2R : Z := 0x82948.
Definition HL_RT : Z := 0x82a1c.
Definition H_m1 (H : htab) (h : Z) (c : colour) : htab :=
mkHT (ht_frequ H) (set_col (ht_keys H) h c) (ht_used H) (ht_pal H) (ht_colidx H) (ht_cnt H) (ht_T H).
Definition H_m2 (H : htab) (h : Z) (c : colour) : htab :=
mkHT (ht_frequ H) (set_col (ht_keys H) h c) (ht_used H) (set_col (ht_pal H) (ht_cnt H) c) (ht_colidx H) (ht_cnt H) (ht_T H).
Definition ac_with (C : acht) (H' : htab) (ent' : list (colour * Z)) : acht := mkACHT (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) H' ent'.
Definition C_m1 (C : acht) (h : Z) (c : colour) : acht := ac_with C (H_m1 (ac_H C) h c) (ac_ent C).
Definition C_m2 (C : acht) (h : Z) (c : colour) : acht := ac_with C (H_m2 (ac_H C) h c) (ac_ent C).
Definition C_ins (C : acht) (h : Z) (c : colour) : acht := ac_with C (ht_ins (ac_H C) h c 1) (ac_ent C ++ [(c, 1)]).
Definition C_hit (C : acht) (h : Z) : acht :=
ac_with C (ht_hit (ac_H C) h) (lset (ac_ent C) (Z.to_nat (cidx (ac_H C) h)) (key (ac_H C) h, freq (ac_H C) h + 1)).
Section a.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Definition pxc (i : Z) : colour := mkcol (getz imgl (fmt * i)) (getz imgl (fmt * i + 1)) (getz imgl (fmt * i + 2)).
Definition opaque_px (i : Z) : Prop := fmt = 4 -> 128 <= getz imgl (fmt * i + 3).
Definition hspill (W : world trasegs) (mem : word -> option byte) (i ha : Z) : Prop :=
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 72) 8 i /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 56) 8 ha.
Definition hpixf (regs : bvmap 5 word) (i ha : Z) : Prop :=
0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ opaque_px i /\ getr regs 27 = Z_to_bv 64 hv27.
Definition hprobe_regs (regs : bvmap 5 word) (C : acht) (i j : Z) : Prop :=
getr regs 20 = Z_to_bv 64 (img + fmt * i) /\ getr regs 21 = Z_to_bv 64 (ac_T C) /\ getr regs 22 = Z_to_bv 64 (ac_h C) /\
getr regs 23 = Z_to_bv 64 (ac_u C) /\ getr regs 24 = Z_to_bv 64 j /\
getr regs 26 = Z_to_bv 64 (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j).
Definition at_BC (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha j : Z) : Prop :=
hcore lyc Sc W regs mem md k C /\ hpixf regs i ha /\ zsum (map snd (ac_ent C)) <= i /\ hspill W mem i ha /\ hprobe_regs regs C i j /\
(exists js, find_off (ac_H C) (pxc i) = Some js /\ 0 <= j <= js) /\
usedz (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j) <> 0 /\
getr regs 10 = Z_to_bv 64 (img + fmt * i) /\ getr regs 11 = Z_to_bv 64 (ac_h C + 3 * cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j) /\
getr regs 12 = Z_to_bv 64 3 /\ getr regs 1 = Z_to_bv 64 HL_BR.
Definition at_BR (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha j : Z) (v : word) : Prop :=
hcore lyc Sc W regs mem md k C /\ hpixf regs i ha /\ zsum (map snd (ac_ent C)) <= i /\ hspill W mem i ha /\ hprobe_regs regs C i j /\
(exists js, find_off (ac_H C) (pxc i) = Some js /\ 0 <= j <= js) /\
usedz (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j) <> 0 /\
getr regs 10 = v /\ (v = Z_to_bv 64 0 <-> key (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j) = pxc i).
Definition at_PA (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha h cf : Z) : Prop :=
hcore lyc Sc W regs mem md k C /\ hpixf regs i ha /\ zsum (map snd (ac_ent C)) <= i /\ hspill W mem i ha /\
(exists js, find_off (ac_H C) (pxc i) = Some js /\ h = cyc (ac_T C) (hash0 (ac_T C) (pxc i)) js /\ cf = (if js <? 31 then 0 else 1)) /\
getr regs 20 = Z_to_bv 64 (img + fmt * i) /\ getr regs 22 = Z_to_bv 64 (ac_h C) /\ getr regs 23 = Z_to_bv 64 (ac_u C) /\
getr regs 24 = Z_to_bv 64 h /\ getr regs 26 = Z_to_bv 64 h /\ getr regs 13 = Z_to_bv 64 cf /\
getr regs 28 = Z_to_bv 64 i /\ getr regs 29 = Z_to_bv 64 ha /\
(getr regs 5 = Z_to_bv 64 (tb + 8) /\ getr regs 6 = Z_to_bv 64 (tb + 16) /\ getr regs 7 = Z_to_bv 64 fmt /\
getr regs 16 = Z_to_bv 64 hv16 /\ getr regs 17 = Z_to_bv 64 hv17).
Definition hins_regs (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (i ha h cf : Z) : Prop :=
getr regs 20 = Z_to_bv 64 (img + fmt * i) /\ getr regs 21 = Z_to_bv 64 i /\ getr regs 23 = Z_to_bv 64 ha /\
getr regs 24 = Z_to_bv 64 h /\ getr regs 26 = Z_to_bv 64 h /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 cf.
Definition hins_ghost (C : acht) (i h cf : Z) : Prop :=
ht_inv (ac_H C) (ac_ent C) /\ zsum (map snd (ac_ent C)) <= i /\ find_slot (ac_H C) (pxc i) = Some h /\ usedz (ac_H C) h = 0 /\ (cf = 0 \/ cf = 1).
Definition at_M1C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha h cf : Z) : Prop :=
hcore_raw lyc Sc W regs mem md k C /\ hpixf regs i ha /\ hspill W mem i ha /\ hins_ghost C i h cf /\ hins_regs W regs mem i ha h cf /\
getr regs 10 = Z_to_bv 64 (ac_h C + 3 * h) /\ getr regs 11 = Z_to_bv 64 (img + fmt * i) /\ getr regs 12 = Z_to_bv 64 3 /\
getr regs 1 = Z_to_bv 64 HL_M1R.
Definition at_M1R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha h cf : Z) : Prop :=
hcore_raw lyc Sc W regs mem md k (C_m1 C h (pxc i)) /\ hpixf regs i ha /\ hspill W mem i ha /\ hins_ghost C i h cf /\ hins_regs W regs mem i ha h cf.
Definition at_M2C (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha h cf : Z) : Prop :=
hcore_raw lyc Sc W regs mem md k (C_m1 C h (pxc i)) /\ hpixf regs i ha /\ hspill W mem i ha /\ hins_ghost C i h cf /\ hins_regs W regs mem i ha h cf /\
getr regs 10 = Z_to_bv 64 (ac_p C + 3 * ht_cnt (ac_H C)) /\ getr regs 11 = Z_to_bv 64 (img + fmt * i) /\ getr regs 12 = Z_to_bv 64 3 /\
getr regs 1 = Z_to_bv 64 HL_M2R.
Definition at_M2R (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha h cf : Z) : Prop :=
hcore_raw lyc Sc W regs mem md k (C_m2 C h (pxc i)) /\ hpixf regs i ha /\ hspill W mem i ha /\ hins_ghost C i h cf /\ hins_regs W regs mem i ha h cf.
Definition at_RT (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C' : acht) (i ha cf : Z) : Prop :=
hcore lyc Sc W regs mem md k C' /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ zsum (map snd (ac_ent C')) <= i + 1 /\ hspill W mem i ha /\
(cf = 0 \/ cf = 1) /\
(getr regs 5 = Z_to_bv 64 (tb + 8) /\ getr regs 6 = Z_to_bv 64 (tb + 16) /\ getr regs 7 = Z_to_bv 64 fmt /\
getr regs 16 = Z_to_bv 64 hv16 /\ getr regs 17 = Z_to_bv 64 hv17 /\ getr regs 27 = Z_to_bv 64 hv27) /\
getr regs 10 = Z_to_bv 64 (tb + 40) /\ getr regs 13 = Z_to_bv 64 cf /\ getr regs 14 = Z_to_bv 64 (tb + 44) /\
getr regs 28 = Z_to_bv 64 i /\ getr regs 29 = Z_to_bv 64 ha.
End a.
