(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0v YK02 YP0n YM06 YK1j YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO14 YO0v YO0q YO0u YO15 YO10 YO12 YO11 YO0r YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02
YN2b YN2e YN0g YN0d YN0c YN25 YN0a YN0p
YN2j YN2h YN2n YN2m YN2d YN2i
YN2k YN0j YN0h YN2l YN0i YN1k YN1l YN1m
YN2w YN1d YN31 YN0z YN13 YN14 YN15 YN16 YN17 YN18.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_SEG_mm : SEG_mm.
Proof.
intros X U L A regs mem md sc n stk g j1 j2 HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB.
intros m s1 L1 mem1 md1 c AF G4 Harm.
destruct AF as ([Q [RX1 AK1]] & LE1 & MID1 & AMA1 & BND1 & VM1 & FR1 & ERRW1).
destruct Q as (AFR & UBS & HI1 & NXm & Km & Mm & US1). cbn [fst snd] in AFR, UBS, HI1, NXm, Km, Mm, US1.
destruct AFR as (ACT1 & USG1 & RG1 & LEN1 & MC1).
pose proof G4 as (E & ms & Ec & HS & HA & E40 & E56 & E61 & E62 & HF).
rewrite mm_body_eq. subst c. cbn [ibind mreal].
eapply SR_bind.
{ eapply (reach_M0 X U L A regs mem md sc stk HI Hsc MID PRE Hstk R10 g j1 j2 m s1 L1 mem1 md1 HI1 MID1 E HA _ G4).
exists E, ms. split; [reflexivity|]. split; [exact HS|]. split; [reflexivity | exact HF]. }
intros c1 H1. eapply SR_bind.
{ exact (reach_M1 X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk R10 g j1 j2 m s1 L1 mem1 md1 HI1 RX1 Mm MID1 AMA1 BND1 E HA E56 E61 E62 c1 H1). }
intros c2 (E3 & ms2 & -> & HS2 & AG3 & E3_67 & HM2 & HF2).
destruct AG3 as [Y3 D3].
assert (E3E : forall k, (k < 64)%nat -> ew E3 k = ew E k) by (intros k Hk; rewrite (Y3 k) by lia; rewrite !ew_ewset_other by lia; reflexivity).
assert (HA3 : env_agree 40 (E0 regs (cs L A sc g j1 j2)) E3).
{ split; [intros k Hk; rewrite (E3E k) by lia; apply (proj1 HA); exact Hk | rewrite D3; cbn [ed ewset]; exact (proj2 HA)]. }
assert (E3_40 : ew E3 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite E3E by lia; exact E40).
assert (E3_56 : ew E3 56 = Z_to_bv 64 (usage_of s1 sc)) by (rewrite E3E by lia; exact E56).
assert (E3_61 : ew E3 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc))) by (rewrite E3E by lia; exact E61).
assert (E3_62 : ew E3 62 = Z_to_bv 64 (16 * cs L A sc g j1 j2 35 * initial_cnt sc (usage_of s1 sc))) by (rewrite E3E by lia; exact E62).
eapply SR_bind.
{ exact (reach_MM X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk R10 R11 g j1 j2 m s1 L1 mem1 md1 HI1 RX1 Mm MID1 AMA1 BND1 E3 HA3 E3_56 E3_61 E3_62 E3_67 ms2 HS2 HM2 HF2). }
intros c3 (E6 & ms3 & -> & HS3 & AG6 & E6_81 & E6_82 & HM3 & HF3).
assert (AG6' : env_agree 40 (E0 regs (cs L A sc g j1 j2)) E6).
{ eapply env_agree_trans; [exact HA3 | split; [intros k Hk; apply (proj1 AG6); lia | exact (proj2 AG6)]]. }
assert (E6_40 : ew E6 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite (proj1 AG6 40%nat) by lia; exact E3_40).
assert (E6_56 : ew E6 56 = Z_to_bv 64 (usage_of s1 sc)) by (rewrite (proj1 AG6 56%nat) by lia; exact E3_56).
apply (step_MM X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk R10 g j1 j2 m s1 L1 mem1 md1 HI1 RX1 Mm Km MID1 AMA1 BND1 ERRW1 E3 HA3 E3_40 E6 AG6 E6_81 _ _ ms3 HS3 HM3 HF3).
- intros c4 KF. cbn [Z.eqb negb]. exact (leaf_free X U L A regs mem md sc n stk HI RX RSV SPOK Hsc Hn MID PRE Hstk R10 g j1 j2 m s1 L1 mem1 md1 HI1 RX1 Mm Km NXm US1 LE1 AK1 MID1 AMA1 BND1 VM1 FR1 E6 AG6' E6_40 c4 KF).
- intros a c4 (ms4 & mem3 & -> & HS4 & Hmem4 & HM4 & HF4 & GR). cbn [Z.eqb negb].
exact (leaf_inst X U L A regs mem md sc n stk HI RX RSV SPOK Hsc Hn MID PRE Hstk R10 g j1 j2 HU m s1 L1 mem1 md1 HI1 RX1 Mm Km NXm US1 ACT1 LEN1 LE1 AK1 MID1 AMA1 BND1 VM1 FR1 ERRW1 E6 AG6' E6_40 E6_56 E6_81 E6_82 a mem3 GR HM4 HF4 ms4 HS4 Hmem4).
Qed.
Corollary src0_alloc_slot_partial3 : alloc_meta_hyp B -> (forall fuel, SEG_group_at fuel -> SEG_head_at fuel) -> SEG_nest -> alloc_slot_hyp B.
Proof. intros AMH SH SN. exact (src0_alloc_slot_of_parts AMH SH src0_SEG_mm SN). Qed.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
