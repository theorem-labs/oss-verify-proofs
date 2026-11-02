(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN12.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN17.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN18.
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
