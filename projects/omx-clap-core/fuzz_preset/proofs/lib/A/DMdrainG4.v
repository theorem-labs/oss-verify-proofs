(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainG4.v (commit 67deba317dfb, blob a78c51669885) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdrainE DMdrainG1 DMdrainG2 DMdrainG3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMdrainT1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma T_app : forall ly, layout_ok ly -> in_app (ly_T ly) kThreadObjSize.
Proof.
intros ly LY. pose proof (lo_app ly LY) as HA. unfold owned_extents in HA.
apply Forall_cons_iff in HA as [_ HA]. apply Forall_cons_iff in HA as [_ HA]. apply Forall_cons_iff in HA as [HT _].
exact HT.
Qed.
Lemma T_img : forall ly, layout_ok ly -> zdisjoint (ly_T ly, kThreadObjSize) (ly_img ly).
Proof.
intros ly LY. pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & DT & _).
do 6 (apply Forall_cons_iff in DT as [_ DT]). apply Forall_cons_iff in DT as [HI _]. exact HI.
Qed.

Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Hypothesis TB : TfibSyms B.
Hypothesis QV : di_qview_t B ARX L24 QB.
Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.

Theorem entry_free_hyps : forall inst ly X W regs mem md,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md -> AFgj.free_hyps W ly regs mem (st_qglobal X) (st_qthread X).
Proof.
intros inst ly X W regs mem md PRE.
pose proof PRE as (HAR & HTB0 & HQB & HL24 & Hra & Hra4 & Hal & Hsp1 & Hsp2 & Hpres & Hgp & Htp & Ha0 & Ha1 & Ha2).
pose proof (QV inst ly X W mem md HAR (conj HTB0 (conj HQB HL24))) as QVX.
destruct QVX as [Qinst Qly Qimg Qtsd Qcells Qconst Qhpres Qbpres Qgeom Qnodup Qwf Qbytes Qinited].
assert (AQ : A_QUAR = as_inst B + o_quar) by (rewrite (ts_inst _ TB); reflexivity).
assert (IMG : img_cover ly) by exact Qimg.
pose proof (DMdrainG1.TOBJ ly Qly IMG (T_app ly Qly) (T_img ly Qly)) as (T1 & TZ & T2 & T3 & T4).
pose proof (DMdrainG1.SPACE ly Qly) as HSB. pose proof (DMdrainG1.STKR ly Qly) as [K1 K2].
destruct (QBB X HQB) as [QG QT].
assert (G0 : 0 <= qc_bytes (st_qglobal X)).
{ pose proof Qwf as (_ & W2 & _). rewrite W2.
  pose proof (bytes_ge_count (qc_list (st_qglobal X)) (DMdrainG3.nn_of X Qwf _ (DMdrainG3.in_G X))) as HB.
  unfold kBatchBytes in HB. lia. }
rewrite Qinst in Qconst.
pose proof (DMdrainG2.rootT_q B ly X W mem Qcells) as VQT.
pose proof (DMdrainG2.rootG_q B ly X W mem AQ Qcells) as VQG.
pose proof (DMdrainG2.mutex_q B ly X W mem AQ Qcells Qconst) as VQW.
pose proof (DMdrainG2.const_q B W mem AQ Qconst) as [VMAX VMIN].
assert (BP : forall b a, In b (all_batches X) -> ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> apresent (w_H W) mem a)
  by (intros b a Hb Ha; exact (Qbpres b a Hb Ha)).
pose proof (DMdrainG3.GF_range ly X Qly Qgeom) as HGF.
pose proof (DMdrainG3.GL_range ly X Qly Qgeom) as HGL.
pose proof (DMdrainG3.TF_range ly X Qly Qgeom) as HTF.
pose proof (DMdrainG3.TL_range ly X Qly Qgeom) as HTL.
pose proof (DMdrainG3.G_count X Qwf Qbytes) as HGcnt.
pose proof (DMdrainG3.T_count X Qwf Qbytes HTB0) as HTcnt.
pose proof (DMdrainG3.G_last B ly X W mem Qly Qgeom BP Qcells) as Hglast.
unfold spZ, raZ in *.
assert (U : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
apply (DMdrainE.drain_free_hyps W ly regs mem (st_qglobal X) (st_qthread X)).
all: first
  [ exact Qly | exact IMG | exact TZ | exact Hra | exact Hra4 | exact Hal | exact Hpres | exact Qhpres | exact Hglast
  | exact HGF | exact HGL | exact HTF | exact HTL | exact HGcnt | exact HTcnt | exact VQW | exact VQG | exact VMAX | exact VMIN
  | (splits; first [exact T1 | lia])
  | exact HSB
  | (rewrite Htp; rewrite (ts_tp _ TB); reflexivity)
  | (rewrite Ha0; rewrite Qinst, <- AQ; reflexivity)
  | exact Ha1 | exact Ha2
  | (split; [exact Hsp1 | exact Hsp2])
  | (split; [ (try unfold YFeuC.DSTACK in *); (try unfold DSTACK in *); lia | lia ])
  | exact T4
  | (split; [exact K1 | exact K2])
  | (unfold AFgj.GBv; lia)
  | (unfold AFgj.TBv; split; lia)
  | exact VQT ].
Qed.
End g.

Lemma QBB_of_QB_cf : forall (NMAXD : Z) (QB : astate -> Prop), NMAXD <= 2 ^ 28 ->
(forall X, QB X -> qc_bytes (st_qthread X) <= kQuarantineCacheMax + kBatchBytes + NMAXD /\ qc_bytes (st_qglobal X) <= kQuarantineMax) ->
forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.
Proof.
intros NMAXD QB HN HQ X HX. destruct (HQ X HX) as [H1 H2].
unfold kQuarantineCacheMax, kBatchBytes, kQuarantineMax in *. lia.
Qed.
End f.
