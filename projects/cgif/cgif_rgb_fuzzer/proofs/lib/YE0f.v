(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF63 YE04 YE0v YE0a YE0g YE0h YE0i YE0j YE0b YE0c YE0d YE0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfxsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfxsegs B ly S W regs mem d n.
Hypothesis HAM : amem_range d n.
Hypothesis HRA : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) d n.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis HSRC : src_ok tfxsegs W regs mem x n.
Hypothesis HDISJ : d + n <= x \/ x + n <= d.
Hypothesis HAMX : amem_range x n.
Hypothesis HRAX : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis HHULLX : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0s : Z := x / 8.
Let g1s : Z := (x + n - 1) / 8.
Let dus : Z := (x + 7) / 8 * 8.
Let des : Z := (x + n) / 8 * 8.
Let gus : Z := (x + 7) / 8.
Let ges : Z := (x + n) / 8.
Let g0d : Z := d / 8.
Let g1d : Z := (d + n - 1) / 8.
Let dud : Z := (d + 7) / 8 * 8.
Let ded : Z := (d + n) / 8 * 8.
Let gud : Z := (d + 7) / 8.
Let ged : Z := (d + n) / 8.
Local Notation Env := (YE0v.Env regs).
Local Notation POSTc := (YE0a.POSTc B ly S W regs mem md d x n).
Local Notation SV := (YE0a.SV regs).
Local Notation MIDP := (YE0a.MIDP W regs mem d x n).
Local Notation MIDQ := (YE0a.MIDQ W regs mem md d x n).
Local Notation basics := (YE0a.basics B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (YE0a.finish0 B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (YE0a.finishD B LAWS ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (YE0a.midS B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (YE0a.EnvS_reg regs).
Local Notation EnvS_x := (YE0a.EnvS_x regs).
Local Notation EnvS2 := (YE0a.EnvS2 regs).
Local Notation EnvS10 := (YE0a.EnvS10 regs d G10).
Local Notation EnvS11 := (YE0a.EnvS11 regs x G11).
Local Notation EnvS12 := (YE0a.EnvS12 regs n G12).
Local Notation entS_stk := (YE0a.entS_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (YE0a.entS_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (YE0a.EnvD regs).
Local Notation EnvD_reg := (YE0a.EnvD_reg regs).
Local Notation EnvD_sv := (YE0a.EnvD_sv regs d x).
Local Notation EnvD_x := (YE0a.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (YE0a.EnvD2 B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (YE0a.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (YE0a.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (YE0a.EnvD12 W regs mem d x n).
Local Notation entD_stk := (YE0a.entD_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (YE0a.entD_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (YE0a.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathS1_0 := (YE0g.pathS1_0 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_1 := (YE0g.pathS1_1 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_2 := (YE0g.pathS1_2 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_3 := (YE0h.pathS1_3 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_4 := (YE0h.pathS1_4 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_5 := (YE0h.pathS1_5 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_6 := (YE0i.pathS1_6 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_7 := (YE0i.pathS1_7 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_8 := (YE0i.pathS1_8 B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS2L := (YE0j.pathS2L B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX).
Local Notation pathS2H := (YE0j.pathS2H B TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX).
Local Notation pathD1_0 := (YE0b.pathD1_0 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_1 := (YE0b.pathD1_1 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_2 := (YE0b.pathD1_2 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_3 := (YE0c.pathD1_3 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_4 := (YE0c.pathD1_4 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_5 := (YE0c.pathD1_5 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_6 := (YE0d.pathD1_6 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_7 := (YE0d.pathD1_7 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_8 := (YE0d.pathD1_8 B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD2L := (YE0e.pathD2L B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD2H := (YE0e.pathD2H B LAWS TB ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA Hx0 Hxn HSRC HDISJ HAMX).
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. img_lia. Qed.
Lemma pathD : forall ms0 mat0, MIDP ms0 -> 0 < n -> SRr tfxsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn0. destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by img_lia.
assert (Hg0 : 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
destruct (t_cases (g1d - g0d) ltac:(img_lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[img_try (img_apply pathD1_0) | img_try (img_apply pathD1_1) | img_try (img_apply pathD1_2) | img_try (img_apply pathD1_3) | img_try (img_apply pathD1_4) | img_try (img_apply pathD1_5) | img_try (img_apply pathD1_6) | img_try (img_apply pathD1_7) | img_try (img_apply pathD1_8)]; assumption.
- destruct HAM as [HL|HH]; [img_try (img_apply pathD2L; [img_exact HM | img_lia | img_exact HL]) | img_try (img_apply pathD2H; [img_exact HM | img_lia | img_exact HH])].
Qed.
Lemma pathS : 0 < n -> SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn0. destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by img_lia.
assert (Hg0 : 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
destruct (t_cases (g1s - g0s) ltac:(img_lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[img_try (img_apply pathS1_0) | img_try (img_apply pathS1_1) | img_try (img_apply pathS1_2) | img_try (img_apply pathS1_3) | img_try (img_apply pathS1_4) | img_try (img_apply pathS1_5) | img_try (img_apply pathS1_6) | img_try (img_apply pathS1_7) | img_try (img_apply pathS1_8)]; assumption.
- destruct HAMX as [HL|HH]; [img_try (img_apply pathS2L; [img_lia | img_exact HL]) | img_try (img_apply pathS2H; [img_lia | img_exact HH])].
Qed.
Theorem asan_memcpy_srr : SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) POSTc.
Proof.
destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [img_try (img_apply pathS0; img_exact Hn0)|].
eapply SRr_bind; [img_try (img_apply pathS; img_lia)|].
cbv beta. intros W1 c1 _ (-> & ms & mat & -> & HM). img_apply (pathD ms mat HM). img_lia.
Qed.
End c.
Theorem asan_memcpy_realizes {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B ->
forall ly S (W : world tfxsegs) regs mem md d x n,
ecall_pre tfxsegs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfxsegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) d n) ->
(0 <= x /\ x + n <= 2 ^ 63 /\ src_ok tfxsegs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n)) ->
SRr tfxsegs W (cfg_at tfxsegs (0x51db0 + D_2c4) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem' (d + i) = aview tfxsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL (Hx0 & Hxn & HSRC & HDISJ & HAMX & HRAX & HHULLX).
img_exact (asan_memcpy_srr B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX HRAX HHULLX).
Qed.
End b.
