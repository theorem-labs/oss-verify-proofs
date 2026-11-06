(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF2o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition xRA : nat := 32.  Definition xS0 : nat := 33.  Definition xS1 : nat := 34.  Definition xS2 : nat := 35.  Definition xS3 : nat := 36.  Definition xS4 : nat := 37.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (vra vs0 vs1 vs2 vs3 vs4 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33844 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W regs0 mem0 vra vs0 vs1 vs2 vs3 vs4.
Local Notation XW := (YF2o.XW vra vs0 vs1 vs2 vs3 vs4).
Local Notation E0 := (YF2o.E0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation Er := (YF2o.Er regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation E2 := (YF2o.E2 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqRA := (YF2o.EqRA regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS0 := (YF2o.EqS0 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS1 := (YF2o.EqS1 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS2 := (YF2o.EqS2 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS3 := (YF2o.EqS3 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS4 := (YF2o.EqS4 regs0 vra vs0 vs1 vs2 vs3 vs4).
Local Notation R_STK := YF2o.R_STK.
Local Notation REG0 := YF2o.REG0.
Local Notation FFX := YF2o.FFX.
Local Notation SR0 := YF2o.SR0.
Local Notation SS0 := YF2o.SS0.
Local Notation WIN := YF2o.WIN.
Local Notation win_sub := YF2o.win_sub.
Local Notation WSK0 := YF2o.WSK0.
Local Notation sk_ok := YF2o.sk_ok.
Local Notation WSK0_ok := YF2o.WSK0_ok.
Local Notation windows_WIN := (YF2o.windows_WIN regs0).
Local Notation MEQ := (YF2o.MEQ mem0).
Local Notation MEQ_frame := (YF2o.MEQ_frame regs0 mem0).
Local Notation MEQ_0 := (YF2o.MEQ_0 mem0).
Local Notation MEQ_all := (YF2o.MEQ_all mem0).
Local Notation SREGS := YF2o.SREGS.
Local Notation at_RETX := (YF2o.at_RETX W regs0 mem0 md0 vra vs0 vs1 vs2 vs3 vs4).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Htp Hra Hsp Hsp_al Hvals SEED].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; img_refl.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac reg_atom HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ img_refl | f_equal; img_lia ].
Lemma segX : SRr tfxsegs W cfg0 at_RETX.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ. pose proof (WSK0_ok E0) as SK0.
srr_run_sh tfxtbl_rtG_ok HS.
match goal with HFx : frame_of ?E ?rs ?ma ?mb |- _ => pose proof (MEQ_frame E _ rs ma mb SK0 ltac:(img_try ((img_case; vm_compute); img_refl)) HFx MQ) as MQ1 end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfxsegs tfxtbl_rtG tfxtbl_rtG_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|]. exists (ms_regs msR), mat'.
rreg HS (1%bv : bv 5) Q1.
assert (MM : ms_mem msR = mem0).
{ img_apply functional_extensionality. intros x. img_exact (MEQ_all _ MQ1 x). }
assert (RA : getr (ms_regs msR) 1 = w64 vra) by (img_try (rewrite Q1; first [img_exact EqRA | cbn [sv_denot]; rewrite EqRA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl])).
split. { rewrite RA, MM. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; numconst; img_lia. }
split. { img_exact RA. }
split. { reg_atom HS (8%bv : bv 5) constr:(EqS0). }
split. { reg_atom HS (9%bv : bv 5) constr:(EqS1). }
split. { reg_atom HS (18%bv : bv 5) constr:(EqS2). }
split. { reg_atom HS (19%bv : bv 5) constr:(EqS3). }
split. { reg_atom HS (20%bv : bv 5) constr:(EqS4). }
intros r Hr. cbn [YF2o.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; img_refl
| reg_entry HS (10%bv : bv 5) 10%nat | reg_entry HS (11%bv : bv 5) 11%nat | reg_entry HS (12%bv : bv 5) 12%nat | reg_entry HS (13%bv : bv 5) 13%nat
| reg_entry HS (21%bv : bv 5) 21%nat | reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Qed.
End WK.
End a.
