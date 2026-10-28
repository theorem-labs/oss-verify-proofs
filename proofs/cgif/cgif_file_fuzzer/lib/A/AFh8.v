(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFgt.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition xRA : nat := 32.  Definition xS0 : nat := 33.  Definition xS1 : nat := 34.  Definition xS2 : nat := 35.  Definition xS3 : nat := 36.  Definition xS4 : nat := 37.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (vra vs0 vs1 vs2 vs3 vs4 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x3323c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W regs0 mem0 vra vs0 vs1 vs2 vs3 vs4.
Local Notation XW := (AFgt.XW vra vs0 vs1 vs2 vs3 vs4).
Local Notation E0 := (AFgt.E0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation Er := (AFgt.Er regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation E2 := (AFgt.E2 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqRA := (AFgt.EqRA regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS0 := (AFgt.EqS0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS1 := (AFgt.EqS1 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS2 := (AFgt.EqS2 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS3 := (AFgt.EqS3 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS4 := (AFgt.EqS4 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation R_STK := AFgt.R_STK.
Local Notation REG0 := AFgt.REG0.
Local Notation FFX := AFgt.FFX.
Local Notation SR0 := AFgt.SR0.
Local Notation SS0 := AFgt.SS0.
Local Notation WIN := AFgt.WIN.
Local Notation win_sub := AFgt.win_sub.
Local Notation WSK0 := AFgt.WSK0.
Local Notation sk_ok := AFgt.sk_ok.
Local Notation WSK0_ok := AFgt.WSK0_ok.
Local Notation windows_WIN := (AFgt.windows_WIN regs0).
Local Notation MEQ := (AFgt.MEQ mem0).
Local Notation MEQ_frame := (AFgt.MEQ_frame regs0 mem0).
Local Notation MEQ_0 := (AFgt.MEQ_0 mem0).
Local Notation MEQ_all := (AFgt.MEQ_all mem0).
Local Notation SREGS := AFgt.SREGS.
Local Notation at_RETX := (AFgt.at_RETX W regs0 mem0 md0 vra vs0 vs1 vs2 vs3 vs4).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Htp Hra Hsp Hsp_al Hvals SEED].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_atom HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ reflexivity | f_equal; lia ].
Lemma segX : SRr tfibsegs W cfg0 at_RETX.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ. pose proof (WSK0_ok E0) as SK0.
srr_run_sh tfibtbl_rtG_ok HS.
match goal with HFx : frame_of ?E ?rs ?ma ?mb |- _ => pose proof (MEQ_frame E _ rs ma mb SK0 ltac:(vm_compute; reflexivity) HFx MQ) as MQ1 end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtG tfibtbl_rtG_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), mat'.
rreg HS (1%bv : bv 5) Q1.
assert (MM : ms_mem msR = mem0).
{ apply functional_extensionality. intros x. exact (MEQ_all _ MQ1 x). }
assert (RA : getr (ms_regs msR) 1 = w64 vra) by (rewrite Q1; first [exact EqRA | cbn [sv_denot]; rewrite EqRA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]).
split. { rewrite RA, MM. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; numconst; lia. }
split. { exact RA. }
split. { reg_atom HS (8%bv : bv 5) constr:(EqS0). }
split. { reg_atom HS (9%bv : bv 5) constr:(EqS1). }
split. { reg_atom HS (18%bv : bv 5) constr:(EqS2). }
split. { reg_atom HS (19%bv : bv 5) constr:(EqS3). }
split. { reg_atom HS (20%bv : bv 5) constr:(EqS4). }
intros r Hr. cbn [AFgt.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (10%bv : bv 5) 10%nat | reg_entry HS (11%bv : bv 5) 11%nat | reg_entry HS (12%bv : bv 5) 12%nat | reg_entry HS (13%bv : bv 5) 13%nat
| reg_entry HS (21%bv : bv 5) 21%nat | reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Qed.
End WK.
End a.
