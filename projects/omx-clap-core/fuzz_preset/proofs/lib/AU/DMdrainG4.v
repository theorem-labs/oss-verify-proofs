(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainG4.v (commit ce1a656b52b7, file sha256 2c3c3d4ecb8e) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainG4.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 46d324445dcd) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainG4.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the ENTRY BRIDGE - from the drain contract's premise
   DMspec.drain_pre_cf (DMspec.v:89-98) at the cgif image, the instance's view field DMiface.di_qview_t
   (DMiface.v:174-175) and QB's two cache byte bounds, to YFgj.free_hyps, so that DMdrainT1.drain_entry_run runs
   Drain's entry walk.  This is where the drain's composition stops reading anything instance-specific: all the
   facts the released entry shell needs come out of qview (DMdrainG1 / G2 / G3) or the premise's registers.
   QB's two bounds (the global cache at most 2 ^ 30, the thread cache at most 2 ^ 29: the released shell's,
   YFgj.v:114-115) are a hypothesis [QBB]; at the shared instance QB_cf gives them (global <= kQuarantineMax =
   2 ^ 28, thread <= kQuarantineCacheMax + kBatchBytes + NMAXD with NMAXD <= 2 ^ 28; integrator 00:3xZ).
   rule 24: no function proved (kind: the premise of segments already walked, DMseg_dme.segDEm /
   DMseg_dmn.segDNm; the lane's reuse search is the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches
   Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMdrainE DMdrainG1 DMdrainG2 DMdrainG3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMdrainT1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The thread object's two layout facts DMdrainG1.TOBJ takes, from layout_ok. *)
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
drain_pre_cf B ARX L24 QB inst ly X W regs mem md -> YFgj.free_hyps W ly regs mem (st_qglobal X) (st_qthread X).
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
  | (unfold YFgj.GBv; lia)
  | (unfold YFgj.TBv; split; lia)
  | exact VQT ].
Qed.
End g.

(* QB_cf's split bounds give QBB when the quarantined block bound is at most max_size = 2 ^ 28 (Put's test at
   0x35f7c): the thread cache is then at most 2 ^ 20 + 8192 + 2 ^ 28 < 2 ^ 29 and the global cache at most
   kQuarantineMax = 2 ^ 28 < 2 ^ 30.  NMAXD's bound is the premise; nothing else of QB_cf is used. *)
Lemma QBB_of_QB_cf : forall (NMAXD : Z) (QB : astate -> Prop), NMAXD <= 2 ^ 28 ->
(forall X, QB X -> qc_bytes (st_qthread X) <= kQuarantineCacheMax + kBatchBytes + NMAXD /\ qc_bytes (st_qglobal X) <= kQuarantineMax) ->
forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.
Proof.
intros NMAXD QB HN HQ X HX. destruct (HQ X HX) as [H1 H2].
unfold kQuarantineCacheMax, kBatchBytes, kQuarantineMax in *. lia.
Qed.
End f.
