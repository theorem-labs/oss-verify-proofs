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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section H8.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BR := (at_BR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_PA := (at_PA B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation FRAMEF := (hk_frame_facts B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK Hsp32).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation at_M1C := (at_M1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RT := (at_RT B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HSTEP := (hcore_raw_step B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation OTHERK := (hk_tbl_other_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M1R := (at_M1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2C := (at_M2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2R := (at_M2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRRS := (hcore_raw_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation APARTN := (hk_tbl_apart_nth B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Local Notation at_TL := (at_TL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_HL := (at_HL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_HX := (at_HX B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_tra.
Hypothesis HSTKE : 512 + 2 * ESTACK <= STK.
Local Notation cfgat regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs)) md).
Ltac hl_use L := (eapply L; eassumption).
Lemma hl_insert : forall lyc Sc W regs mem md k C i ha h cf,
at_PA lyc Sc W regs mem md k C i ha h cf -> usedz (ac_H C) h = 0 ->
SRr trasegs W (cfgat regs HL_PA mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_RT mem2 md2 /\ at_RT lyc Sc W regs2 mem2 md2 k (C_ins C h (pxc i)) i ha cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf HPA Hfree.
eapply SRr_bind; [hl_use hl_pa_ins|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & H1).
eapply SRr_bind; [hl_use hl_m1|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & H2).
eapply SRr_bind; [hl_use hl_m1r|].
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & H3).
eapply SRr_bind; [hl_use hl_m2|].
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & H4).
hl_use hl_m2r.
Qed.
Lemma hl_pa : forall lyc Sc W regs mem md k C i ha h cf,
at_PA lyc Sc W regs mem md k C i ha h cf ->
SRr trasegs W (cfgat regs HL_PA mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 C', c2 = cfgat regs2 HL_RT mem2 md2 /\ at_RT lyc Sc W regs2 mem2 md2 k C' i ha cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf HPA.
destruct (Z.eq_dec (usedz (ac_H C) h) 0) as [Hfree | Hused].
- eapply SRr_mono; [exact (hl_insert lyc Sc W regs mem md k C i ha h cf HPA Hfree)|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & H2). split; [reflexivity|]. exists regs2, mem2, md2, (C_ins C h (pxc i)). split; [reflexivity | exact H2].
- eapply SRr_mono; [hl_use hl_pa_hit|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & H2). split; [reflexivity|]. exists regs2, mem2, md2, (C_hit C h). split; [reflexivity | exact H2].
Qed.
Lemma hl_probe : forall (n : nat) lyc Sc W regs mem md k C i ha j,
at_BC lyc Sc W regs mem md k C i ha j ->
(forall js, find_off (ac_H C) (pxc i) = Some js -> js - j <= Z.of_nat n) ->
SRr trasegs W (cfgat regs A_bcmp_tra mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 C' cf, c2 = cfgat regs2 HL_RT mem2 md2 /\ at_RT lyc Sc W regs2 mem2 md2 k C' i ha cf).
Proof.
induction n as [|n IH]; intros lyc Sc W regs mem md k C i ha j HBC Hn.
all: (eapply SRr_bind; [hl_use hl_bcmp|]);
intros W1 c1 _ (-> & regs1 & mem1 & md1 & v & -> & HBR);
pose proof HBR as (_ & _ & _ & _ & _ & _ & _ & _ & Hv);
(destruct (colour_eq_dec (key (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j)) (pxc i)) as [Hkey | Hkey];
[ apply (proj2 Hv) in Hkey; subst v;
(eapply SRr_bind; [hl_use hl_br_match|]);
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HPA);
(eapply SRr_mono; [exact (hl_pa lyc Sc W regs2 mem2 md2 k C i ha _ _ HPA)|]);
intros W3 c3 _ (-> & regs3 & mem3 & md3 & C' & -> & HRT); split; [reflexivity|]; eexists regs3, mem3, md3, C', _; split; [reflexivity | exact HRT]
| assert (Hvne : v <> Z_to_bv 64 0) by (intros X; apply Hkey; apply (proj1 Hv); exact X);
destruct (Z.eq_dec (usedz (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1))) 0) as [Hfree | Hused];
[ (eapply SRr_bind; [hl_use hl_br_free|]);
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HPA);
(eapply SRr_mono; [exact (hl_pa lyc Sc W regs2 mem2 md2 k C i ha _ _ HPA)|]);
intros W3 c3 _ (-> & regs3 & mem3 & md3 & C' & -> & HRT); split; [reflexivity|]; eexists regs3, mem3, md3, C', _; split; [reflexivity | exact HRT]
| (eapply SRr_bind; [hl_use hl_br_next|]);
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HBC2);
pose proof HBC2 as (_ & _ & _ & _ & _ & (js & Hjs & Hjj) & _) ]]).
- exfalso. pose proof (Hn js Hjs) as X. clear - X Hjj. lia.
- apply (IH lyc Sc W regs2 mem2 md2 k C i ha (j + 1) HBC2). intros js' Hjs'. pose proof (Hn js' Hjs') as X. clear - X. lia.
Qed.
Lemma hl_pixel_rt : forall lyc Sc W regs mem md k C i ha,
at_HL lyc Sc W regs mem md k C i ha ->
SRr trasegs W (cfgat regs HL_HEAD mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
(c2 = cfgat regs2 HL_TAIL mem2 md2 /\ at_TL lyc Sc W regs2 mem2 md2 k C i 1) \/
(exists C' cf, c2 = cfgat regs2 HL_RT mem2 md2 /\ at_RT lyc Sc W regs2 mem2 md2 k C' i ha cf)).
Proof.
intros lyc Sc W regs mem md k C i ha HHL.
assert (Hdec : (fmt = 4 /\ getz imgl (4 * i + 3) <= 127) \/ opaque_px fmt imgl i).
{ unfold opaque_px. destruct (Z.eq_dec fmt 4) as [E4 | N4]; [|right; intros X; contradiction].
destruct (Z_le_gt_dec (getz imgl (4 * i + 3)) 127) as [Hle | Hgt]; [left; split; assumption|]. right. intros _. rewrite E4. clear - Hgt. lia. }
destruct Hdec as [[E4 Htr] | Hop].
- eapply SRr_mono; [hl_use hl_head_transparent|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HTL). split; [reflexivity|]. exists regs2, mem2, md2. left. split; [reflexivity | exact HTL].
- destruct (Z.eq_dec (usedz (ac_H C) (hash0 (ac_T C) (pxc i))) 0) as [Hfree | Hused].
+ eapply SRr_bind; [hl_use hl_head_free|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HPA).
eapply SRr_mono; [exact (hl_pa lyc Sc W regs1 mem1 md1 k C i ha _ _ HPA)|].
intros W3 c3 _ (-> & regs3 & mem3 & md3 & C' & -> & HRT). split; [reflexivity|]. exists regs3, mem3, md3. right. eexists C', _. split; [reflexivity | exact HRT].
+ eapply SRr_bind; [hl_use hl_head_used|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HBC).
pose proof HBC as (_ & _ & _ & _ & _ & (js & Hjs & Hjj) & _).
eapply SRr_mono; [apply (hl_probe (Z.to_nat js) lyc Sc W regs1 mem1 md1 k C i ha 0 HBC); intros js' Hjs'; rewrite Hjs' in Hjs; injection Hjs as ->; clear - Hjj; lia|].
intros W3 c3 _ (-> & regs3 & mem3 & md3 & C' & cf & -> & HRT). split; [reflexivity|]. exists regs3, mem3, md3. right. exists C', cf. split; [reflexivity | exact HRT].
Qed.
Variable XF : world trasegs -> config -> Prop.
Hypothesis RESIZE : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C < MAX_TABLE_SIZE ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => XF W2 c2 \/ exists lyc2 Sc2 regs2 mem2 md2 k2 C2, c2 = cfgat regs2 HL_TAIL mem2 md2 /\ at_TL lyc2 Sc2 W2 regs2 mem2 md2 k2 C2 i ha).
Lemma hl_rt : forall lyc Sc W regs mem md k C i ha cf,
at_RT lyc Sc W regs mem md k C i ha cf ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => XF W2 c2 \/ exists lyc2 Sc2 regs2 mem2 md2 k2 C2, c2 = cfgat regs2 HL_TAIL mem2 md2 /\ at_TL lyc2 Sc2 W2 regs2 mem2 md2 k2 C2 i ha).
Proof.
intros lyc Sc W regs mem md k C i ha cf HRT.
pose proof HRT as (((_ & _ & _ & _ & _ & _ & _ & HTc & _) & _) & _ & _ & _ & _ & Rcf & _).
assert (HTle : ac_T C <= MAX_TABLE_SIZE) by (clear - HTc; cbv [ts_chain In] in HTc; unfold MAX_TABLE_SIZE; lia).
destruct (Z.eq_dec (ac_T C) MAX_TABLE_SIZE) as [Hmax | Hnmax].
- eapply SRr_mono; [hl_use hl_rt_stay_max|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HTL). right. exists lyc, Sc, regs2, mem2, md2, k, C. split; [reflexivity | exact HTL].
- destruct Rcf as [-> | ->].
+ assert (Hsm : 0 = 0 /\ ac_T C < MAX_TABLE_SIZE) by (split; [reflexivity | clear - HTle Hnmax; lia]).
eapply SRr_mono; [hl_use hl_rt_stay_small|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HTL). right. exists lyc, Sc, regs2, mem2, md2, k, C. split; [reflexivity | exact HTL].
+ exact (RESIZE lyc Sc W regs mem md k C i ha HRT ltac:(clear - HTle Hnmax; lia)).
Qed.
Lemma hl_pixel : forall lyc Sc W regs mem md k C i ha,
at_HL lyc Sc W regs mem md k C i ha ->
SRr trasegs W (cfgat regs HL_HEAD mem md)
(fun W2 c2 => XF W2 c2 \/ exists lyc2 Sc2 regs2 mem2 md2 k2 C2 ha2, c2 = cfgat regs2 HL_TAIL mem2 md2 /\ at_TL lyc2 Sc2 W2 regs2 mem2 md2 k2 C2 i ha2).
Proof.
intros lyc Sc W regs mem md k C i ha HHL.
eapply SRr_bind; [exact (hl_pixel_rt lyc Sc W regs mem md k C i ha HHL)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & [[-> HTL] | (C' & cf & -> & HRT)]).
- apply SRr_ret. right. exists lyc, Sc, regs1, mem1, md1, k, C, 1. split; [reflexivity | exact HTL].
- eapply SRr_mono; [exact (hl_rt lyc Sc W regs1 mem1 md1 k C' i ha cf HRT)|].
intros W2 c2 _ [HX | (lyc2 & Sc2 & regs2 & mem2 & md2 & k2 & C2 & -> & HTL)]; [left; exact HX|].
right. exists lyc2, Sc2, regs2, mem2, md2, k2, C2, ha. split; [reflexivity | exact HTL].
Qed.
Theorem hl_loop : forall lyc Sc W regs mem md k C i ha,
at_HL lyc Sc W regs mem md k C i ha ->
SRr trasegs W (cfgat regs HL_HEAD mem md)
(fun W2 c2 => XF W2 c2 \/ exists lyc2 Sc2 regs2 mem2 md2 k2 C2 ha2, c2 = cfgat regs2 HL_EXIT mem2 md2 /\ at_HX lyc2 Sc2 W2 regs2 mem2 md2 k2 C2 ha2).
Proof.
intros lyc Sc W regs mem md k C i ha HHL.
pose (X := (alayout * astate * bvmap 5 word * (word -> option byte) * Model * Z * acht * Z * Z)%type).
pose (P := fun (x : X) (Wx : world trasegs) (c : config) =>
let '(lyx, Sx, rx, mx, mdx, kx, Cx, ix, hax) := x in c = cfgat rx HL_HEAD mx mdx /\ at_HL lyx Sx Wx rx mx mdx kx Cx ix hax).
pose (m := fun (x : X) => let '(_, _, _, _, _, _, _, ix, _) := x in N - ix).
apply (SRr_loopZ trasegs X m P _) with (x := (lyc, Sc, regs, mem, md, k, C, i, ha)); [|split; [reflexivity | exact HHL]].
clear HHL. clear lyc Sc W regs mem md k C i ha. intros [[[[[[[[lyx Sx] rx] mx] mdx] kx] Cx] ix] hax] Wx c [-> HHL]. cbn [m].
eapply SRr_bind; [exact (hl_pixel lyx Sx Wx rx mx mdx kx Cx ix hax HHL)|].
intros W1 c1 _ [HX | (ly1 & S1 & regs1 & mem1 & md1 & k1 & C1 & ha1 & -> & HTL)]; [apply SRr_ret; left; left; exact HX|].
eapply SRr_mono; [hl_use hl_tail|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & [(Hlt & -> & HHL2) | (Heq & -> & HHX)]).
- right. exists (ly1, S1, regs2, mem2, md2, k1, C1, ix + 1, ha1). cbn [m P]. pose proof HHL as (_ & _ & _ & _ & Hi & _).
split; [clear - Hlt Hi; lia|]. split; [reflexivity | exact HHL2].
- left. right. exists ly1, S1, regs2, mem2, md2, k1, C1, ha1. split; [reflexivity | exact HHX].
Qed.
End H8.
