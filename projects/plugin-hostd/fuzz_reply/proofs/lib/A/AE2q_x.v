(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to plugin-hostd/fuzz_reply's ASan build. *)
(* Modified by Theorem Labs, 2026-10: ARx port of lib/A/AE2q.v (that file is unchanged) over AE2y.icpt_laws_x, following SitesCf's conversion of AE31.v (12f0abbb2be): AR_laws -> ARx with WL : icpt_laws_x, the ghost set Hpx after S, ecall_pre -> ecall_pre_ix, AR -> ARx, the cited chain modules -> their _x files; proof steps unchanged except the law names. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3c AE20 AE2y AE6k_x AE6p_x AE6q_x AE6r_x AE6s_x AE6l_x AE6m_x AE6n_x AE6o_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
(* __asan_memcpy over any allocator invariant ARx (AE2y.v); asan_memcpy_realizes below is its cgif AR instance *)
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis WL : icpt_laws_x B ARx.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hpx : list Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre_ix B ARx ly S Hpx W regs mem md.
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
Local Notation Env := (AE2y.Env regs).
Local Notation POSTc := (AE6k_x.POSTc ARx ly S Hpx W regs mem md d x n).
Local Notation SV := (AE6k_x.SV regs).
Local Notation MIDP := (AE6k_x.MIDP W regs mem d x n).
Local Notation MIDQ := (AE6k_x.MIDQ W regs mem md d x n).
Local Notation basics := (AE6k_x.basics B ARx WL ly S Hpx W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (AE6k_x.finish0 B ARx WL ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (AE6k_x.finishD B ARx WL ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (AE6k_x.midS B ARx WL ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (AE6k_x.EnvS_reg regs).
Local Notation EnvS_x := (AE6k_x.EnvS_x regs).
Local Notation EnvS2 := (AE6k_x.EnvS2 regs).
Local Notation EnvS10 := (AE6k_x.EnvS10 regs d G10).
Local Notation EnvS11 := (AE6k_x.EnvS11 regs x G11).
Local Notation EnvS12 := (AE6k_x.EnvS12 regs n G12).
Local Notation entS_stk := (AE6k_x.entS_stk B ARx WL ly S Hpx W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (AE6k_x.entS_ro B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (AE6k_x.EnvD regs).
Local Notation EnvD_reg := (AE6k_x.EnvD_reg regs).
Local Notation EnvD_sv := (AE6k_x.EnvD_sv regs d x).
Local Notation EnvD_x := (AE6k_x.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (AE6k_x.EnvD2 B ARx WL ly S Hpx W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (AE6k_x.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (AE6k_x.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (AE6k_x.EnvD12 W regs mem d x n).
Local Notation entD_stk := (AE6k_x.entD_stk B ARx WL ly S Hpx W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (AE6k_x.entD_ro B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (AE6k_x.pathS0 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathS1_0 := (AE6p_x.pathS1_0 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_1 := (AE6p_x.pathS1_1 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_2 := (AE6p_x.pathS1_2 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_3 := (AE6q_x.pathS1_3 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_4 := (AE6q_x.pathS1_4 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_5 := (AE6q_x.pathS1_5 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_6 := (AE6r_x.pathS1_6 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_7 := (AE6r_x.pathS1_7 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS1_8 := (AE6r_x.pathS1_8 B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX HHULLX).
Local Notation pathS2L := (AE6s_x.pathS2L B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX).
Local Notation pathS2H := (AE6s_x.pathS2H B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 Hxn HDISJ HAMX HRAX).
Local Notation pathD1_0 := (AE6l_x.pathD1_0 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_1 := (AE6l_x.pathD1_1 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_2 := (AE6l_x.pathD1_2 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_3 := (AE6m_x.pathD1_3 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_4 := (AE6m_x.pathD1_4 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_5 := (AE6m_x.pathD1_5 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_6 := (AE6n_x.pathD1_6 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_7 := (AE6n_x.pathD1_7 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD1_8 := (AE6n_x.pathD1_8 B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD2L := (AE6o_x.pathD2L B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA Hx0 Hxn HSRC HDISJ HAMX).
Local Notation pathD2H := (AE6o_x.pathD2H B ARx WL TB ly S Hpx W regs mem md d x n HPRE Hn Hd Hdn HDST HAM HRA Hx0 Hxn HSRC HDISJ HAMX).
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
Theorem asan_memcpy_srr : SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) POSTc.
Proof.
destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [apply pathS0; exact Hn0|].
eapply SRr_bind; [apply pathS; lia|].
cbv beta. intros W1 c1 _ (-> & ms & mat & -> & HM). apply (pathD ms mat HM). lia.
Qed.
End c.
(* the same over any ARx; asan_memcpy_realizes is its cgif AR instance, with AE2q.v's statement text *)
Theorem asan_memcpy_realizes_x : forall B ARx, icpt_laws_x B ARx -> TfibSyms B ->
forall ly S Hpx (W : world tfibsegs) regs mem md d x n,
ecall_pre_ix B ARx ly S Hpx W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
(0 <= x /\ x + n <= 2 ^ 63 /\ src_ok tfibsegs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n)) ->
SRr tfibsegs W (cfg_at tfibsegs 0x52728 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hpx W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL (Hx0 & Hxn & HSRC & HDISJ & HAMX & HRAX & HHULLX).
exact (asan_memcpy_srr B ARx WL TB ly S Hpx W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HDISJ HAMX HRAX HHULLX).
Qed.
Theorem asan_memcpy_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B ->
forall ly S (W : world tfibsegs) regs mem md d x n,
ecall_pre tfibsegs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
(0 <= x /\ x + n <= 2 ^ 63 /\ src_ok tfibsegs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n)) ->
SRr tfibsegs W (cfg_at tfibsegs 0x52728 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S.
exact (asan_memcpy_realizes_x B (AR_x B) (icpt_laws_x_AR B LAWS) TB ly S []).
Qed.
End b.
