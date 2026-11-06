(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfMc31.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ARU form (Poison's FMupoison.v): ecall_preU over any U for ecall_pre; imports the ARU copies FMsnprintfMc30, FMsnprintfMc71-78 in place of A/AE30.v, A/AE71-78.v; the theorem is stated as aintrin_realizesU (lib/A/FMsnprintfI.v), and ocpy_of_icptU (A/AD1o.v ocpy_of_icpt with ARU) is added. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE3c YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfMc30 FMsnprintfMc75 FMsnprintfMc76 FMsnprintfMc77 FMsnprintfMc78 FMsnprintfMc71 FMsnprintfMc72 FMsnprintfMc73 FMsnprintfMc74.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_preU tfibsegs B ly S UP W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfibsegs B ly S W regs mem d n.
Hypothesis HAM : amem_range d n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis HSRC : src_ok tfibsegs W regs mem x n.
Hypothesis HDISJ : d + n <= x \/ x + n <= d.
Hypothesis HAMX : amem_range x n.
Hypothesis HRAX : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis HHULLX : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
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
Local Notation Env := (YE2y.Env regs).
Local Notation POSTc := (FMsnprintfMc30.POSTc B ly S UP W regs mem md d x n).
Local Notation SV := (FMsnprintfMc30.SV regs).
Local Notation MIDP := (FMsnprintfMc30.MIDP W regs mem d x n).
Local Notation MIDQ := (FMsnprintfMc30.MIDQ W regs mem md d x n).
Local Notation basics := (FMsnprintfMc30.basics B ly S UP W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (FMsnprintfMc30.finish0 B LAWS ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (FMsnprintfMc30.finishD B LAWS ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (FMsnprintfMc30.midS B ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (FMsnprintfMc30.EnvS_reg regs).
Local Notation EnvS_x := (FMsnprintfMc30.EnvS_x regs).
Local Notation EnvS2 := (FMsnprintfMc30.EnvS2 regs).
Local Notation EnvS10 := (FMsnprintfMc30.EnvS10 regs d G10).
Local Notation EnvS11 := (FMsnprintfMc30.EnvS11 regs x G11).
Local Notation EnvS12 := (FMsnprintfMc30.EnvS12 regs n G12).
Local Notation entS_stk := (FMsnprintfMc30.entS_stk B ly S UP W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (FMsnprintfMc30.entS_ro B TB ly S UP W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (FMsnprintfMc30.EnvD regs).
Local Notation EnvD_reg := (FMsnprintfMc30.EnvD_reg regs).
Local Notation EnvD_sv := (FMsnprintfMc30.EnvD_sv regs d x).
Local Notation EnvD_x := (FMsnprintfMc30.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (FMsnprintfMc30.EnvD2 B ly S UP W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (FMsnprintfMc30.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (FMsnprintfMc30.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (FMsnprintfMc30.EnvD12 W regs mem d x n).
Local Notation entD_stk := (FMsnprintfMc30.entD_stk B ly S UP W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (FMsnprintfMc30.entD_ro B TB ly S UP W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (FMsnprintfMc30.pathS0 B LAWS TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathS1_0 := (FMsnprintfMc75.pathS1_0 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_1 := (FMsnprintfMc75.pathS1_1 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_2 := (FMsnprintfMc75.pathS1_2 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_3 := (FMsnprintfMc76.pathS1_3 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_4 := (FMsnprintfMc76.pathS1_4 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_5 := (FMsnprintfMc76.pathS1_5 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_6 := (FMsnprintfMc77.pathS1_6 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_7 := (FMsnprintfMc77.pathS1_7 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_8 := (FMsnprintfMc77.pathS1_8 B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS2L := (FMsnprintfMc78.pathS2L B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX).
Local Notation pathS2H := (FMsnprintfMc78.pathS2H B TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX).
Local Notation pathD1_0 := (FMsnprintfMc71.pathD1_0 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_1 := (FMsnprintfMc71.pathD1_1 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_2 := (FMsnprintfMc71.pathD1_2 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_3 := (FMsnprintfMc72.pathD1_3 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_4 := (FMsnprintfMc72.pathD1_4 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_5 := (FMsnprintfMc72.pathD1_5 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_6 := (FMsnprintfMc73.pathD1_6 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_7 := (FMsnprintfMc73.pathD1_7 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_8 := (FMsnprintfMc73.pathD1_8 B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD2L := (FMsnprintfMc74.pathD2L B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD2H := (FMsnprintfMc74.pathD2H B LAWS TB ly S UP W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA Hx0 Hxn HSRC HDISJ HAMX).
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. lia. Qed.
Lemma pathD : forall ms0 mat0, MIDP ms0 -> 0 < n -> SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn0. destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by lia.
assert (Hg0 : 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
destruct (t_cases (g1d - g0d) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply pathD1_0 | apply pathD1_1 | apply pathD1_2 | apply pathD1_3 | apply pathD1_4 | apply pathD1_5 | apply pathD1_6 | apply pathD1_7 | apply pathD1_8]; assumption.
- destruct HAM as [HL|HH]; [apply pathD2L; [exact HM | lia | exact HL] | apply pathD2H; [exact HM | lia | exact HH]].
Qed.
Lemma pathS : 0 < n -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn0. destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by lia.
assert (Hg0 : 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
destruct (t_cases (g1s - g0s) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply pathS1_0 | apply pathS1_1 | apply pathS1_2 | apply pathS1_3 | apply pathS1_4 | apply pathS1_5 | apply pathS1_6 | apply pathS1_7 | apply pathS1_8]; assumption.
- destruct HAMX as [HL|HH]; [apply pathS2L; [lia | exact HL] | apply pathS2H; [lia | exact HH]].
Qed.
Theorem memcpy_icpt_srr : SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) POSTc.
Proof.
destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [apply pathS0; exact Hn0|].
eapply SRr_bind; [apply pathS; lia|].
cbv beta. intros W1 c1 _ (-> & ms & mat & -> & HM). apply (pathD ms mat HM). lia.
Qed.
End c.
Theorem memcpy_icpt_realizesU : forall B, AR_laws tfibsegs B -> TfibSyms B -> aintrin_realizesU B OCpy W_MEMCPY.
Proof.
intros B LAWS TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL (Hx0 & Hxn & HSRC & HDISJ & HAMX & HRAX & HHULLX).
exact (memcpy_icpt_srr B LAWS TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX HRAX HHULLX).
Qed.
Section w.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
(* A/AD1o.v ocpy_of_icpt (A/AD2m.v tfib_AICPY) with ARU: the contract at the symbol's address. *)
Lemma ocpy_of_icptU : aintrin_realizesU B OCpy (pc_wrap_memcpy (as_code B)).
Proof. rewrite (ts_code B TB). exact (memcpy_icpt_realizesU B LAWS TB). Qed.
End w.
End b.
