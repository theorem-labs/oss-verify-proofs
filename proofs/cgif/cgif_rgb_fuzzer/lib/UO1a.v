(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0s YK0i YK0j YK14 YK1b YK1a YK15 YK0v YK02 YQ0k YN06 YK1j YN00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0i YP0q YP0m YP0r YP0t YP0z YP0p YP0k YP0o YP10 YP0v YP0x YP0w YP0l YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0b YP0a YO01 YO04 YO02
YO2f YO2i UO0g UO0e UO0d YO29 UO0b UO0p
YO2n YO2l YO2r YO2q YO2h YO2m
YO2o UO0j UO0h YO2p UO0i UO1s UO1t UO1u
YO32 UO1l YO37 UO18 UO1b UO1c UO1d UO1e UO1f UO1g.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := ubs2_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, ubs2_D_malloc_lock, ubs2_D_malloc_context, ubs2_D_libc, ubs2_tp,
ubs2_D_got_stack_chk_guard, ubs2_D_stack_chk_guard, ubs2_D_size_classes, ubs2_D_small_cnt_tab, ubs2_D_med_cnt_tab in *.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem ubs2_SEG_mm : SEG_mm.
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
Corollary ubs2_alloc_slot_partial3 : alloc_meta_hyp B -> (forall fuel, SEG_group_at fuel -> SEG_head_at fuel) -> SEG_nest -> alloc_slot_hyp B.
Proof. intros AMH SH SN. exact (ubs2_alloc_slot_of_parts AMH SH ubs2_SEG_mm SN). Qed.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
