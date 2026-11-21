(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFh8.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFh8.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0s_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AB1t AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFl1_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFeq_w AFew_w AFeu_w AFgt_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
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
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33918) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W regs0 mem0 vra vs0 vs1 vs2 vs3 vs4.
Local Notation XW := (AFgt_w.XW vra vs0 vs1 vs2 vs3 vs4).
Local Notation E0 := (AFgt_w.E0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation Er := (AFgt_w.Er regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation E2 := (AFgt_w.E2 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqRA := (AFgt_w.EqRA regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS0 := (AFgt_w.EqS0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS1 := (AFgt_w.EqS1 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS2 := (AFgt_w.EqS2 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS3 := (AFgt_w.EqS3 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS4 := (AFgt_w.EqS4 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation R_STK := AFgt_w.R_STK.
Local Notation REG0 := AFgt_w.REG0.
Local Notation FFX := AFgt_w.FFX.
Local Notation SR0 := AFgt_w.SR0.
Local Notation SS0 := AFgt_w.SS0.
Local Notation WIN := AFgt_w.WIN.
Local Notation win_sub := AFgt_w.win_sub.
Local Notation WSK0 := AFgt_w.WSK0.
Local Notation sk_ok := AFgt_w.sk_ok.
Local Notation WSK0_ok := AFgt_w.WSK0_ok.
Local Notation windows_WIN := (AFgt_w.windows_WIN regs0).
Local Notation MEQ := (AFgt_w.MEQ mem0).
Local Notation MEQ_frame := (AFgt_w.MEQ_frame regs0 mem0).
Local Notation MEQ_0 := (AFgt_w.MEQ_0 mem0).
Local Notation MEQ_all := (AFgt_w.MEQ_all mem0).
Local Notation SREGS := AFgt_w.SREGS.
Local Notation at_RETX := (AFgt_w.at_RETX W regs0 mem0 md0 vra vs0 vs1 vs2 vs3 vs4).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Htp Hra Hsp Hsp_al Hvals SEED].
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
intros r Hr. cbn [AFgt_w.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (10%bv : bv 5) 10%nat | reg_entry HS (11%bv : bv 5) 11%nat | reg_entry HS (12%bv : bv 5) 12%nat | reg_entry HS (13%bv : bv 5) 13%nat
| reg_entry HS (21%bv : bv 5) 21%nat | reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Qed.
End WK.
End a.
