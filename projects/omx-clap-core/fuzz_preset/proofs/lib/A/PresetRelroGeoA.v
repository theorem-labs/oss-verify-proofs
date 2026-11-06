(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRelroGeoA.v (commit 96257eb45295, blob fef2fbf95335) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); AD1ycf (the driver-window file) is not Required: its one user, the driver-window lemma, is dropped; the driver-window lemma (no user in the Deallocate contract) and relro_seg / errno_relro (preset's CfAroPresetA lemmas, one text per fact) are dropped. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgi AD20 AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0x DGbase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGgm DGgi.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DGif0.
Open Scope Z_scope.

#[local] Existing Instance CfImg_A.

Lemma pf_ial_apart_preset_A : forall B, TfibSyms B -> YG0ncf.pf_ial_apart_t (ci := CfImg_A) B.
Proof.
intros B TS a Ha. rewrite (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
cbn [cf_toolname_cell cf_pfcb_cell CfImg_A] in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

Definition dzone_static_lo : Z := TFIB_STORE.
Definition dzone_static_hi : Z := AD20.RS_LO.
Lemma dzone_static_text_A : forall ly a, AFgi.DZONE ly a =
((dzone_static_lo <= a < dzone_static_hi) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
 (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)).
Proof. intros ly a. reflexivity. Qed.

Lemma pf_cells_apart_preset_A : forall B, TfibSyms B -> YG0ncf.pf_cells_apart_t (ci := CfImg_A) B.
Proof.
intros B TS a Ha. rewrite (ts_store B TS), (ts_oom B TS).
cbn [cf_toolname_cell cf_pfcb_cell cf_errbuf_obj CfImg_A] in Ha |- *. unfold TFIB_STORE, TFIB_OOM. lia.
Qed.

Lemma pf_dzone_static_preset_A : forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
~ (dzone_static_lo <= a < dzone_static_hi).
Proof.
intros a Ha [Hlo _]. destruct (pf_cells_apart_preset_A _ AD2l.TfibB_syms a Ha) as [H _]. rewrite (ts_store _ AD2l.TfibB_syms) in H. unfold dzone_static_lo in Hlo. lia.
Qed.

Section Z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem zones_miss_relro_preset_A : forall (B : asyms) W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU, DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU -> forall a, YG0dcf.aro_addr_cf (ci := CfImg_A) a -> ~ Exists (in_zr a) (as_owned_static B) -> 0 <= a < 2 ^ 64 /\ ~ DGif0.dwin_m ly (bv_unsigned (getr regs0 2)) p a /\ ~ DGgi.DZONE ly a /\ ~ DGgi.IZONE a /\ ~ DGif0.dshadow p nn a.
Proof.
intros B W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha0 _.

assert (Ha : AF0x.TFIB_IMG_LO <= a < @cf_relro_hi CfImg_A).
{ unfold YG0dcf.aro_addr_cf in Ha0. unfold AF0x.TFIB_IMG_LO. cbn [cf_relro_lo cf_relro_hi cf_ro_reads CfImg_A] in Ha0 |- *.
  destruct Ha0 as [Ha0|Ha0]; [lia|].
  apply Exists_exists in Ha0 as (r & Hr & Hin). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hin; cbn [fst snd] in Hin; lia. }
clear Ha0. unfold AF0x.TFIB_IMG_LO in Ha. cbn [cf_relro_hi CfImg_A] in Ha.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (ZT & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _ & _ & _ & _ & _ & HSTKLO).
pose proof (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (DP & _ & DSP & _).
pose proof (DGgm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & _ & _).
pose proof (DGgm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (DGgm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as [N8a N8b].
assert (HIMG : AF0x.TFIB_IMG_LO <= a < AF0x.TFIB_IMG_END) by (unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia).
assert (NDZ : ~ DGgi.DZONE ly a).
{ unfold DGgi.DZONE. intros [Hd|[Hd|Hd]].
  - lia.
  - exact (AF0x.zone3_apart_img _ _ a ZNB HIMG Hd).
  - exact (AF0x.zone3_apart_img _ _ a ZSB HIMG Hd). }
assert (NIZ : ~ DGgi.IZONE a) by (unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG; lia).
assert (NWIN : ~ DGif0.dwin_m ly (bv_unsigned (getr regs0 2)) p a).
{ unfold DGif0.dwin_m, ImgBaseDG.DGgmC.WINT, ImgBaseDG.DGgmC.WINB, ImgBaseDG.DGbaseC.DFSTACK. cbv beta zeta.
  unfold DGbase.DFSTACK in S1. unfold kHighMemBeg in HSTKLO.
  intros [Hw|[[Hw|Hw]|[Hw|Hw]]].
  - lia.
  - exact (AF0x.zone3_apart_img _ _ a ZT HIMG ltac:(unfold t_unwinding, kThreadObjSize in *; lia)).
  - exact (AF0x.zone3_apart_img _ _ a ZT HIMG ltac:(unfold t_stats, kThreadObjSize in *; lia)).
  - exact (AF0x.zone3_apart_img _ _ a HP HIMG ltac:(lia)).
  - exact (AF0x.zone3_apart_img _ _ a HP HIMG ltac:(lia)). }
assert (NSH : ~ DGif0.dshadow p nn a)
  by (unfold DGgm.SPv in DSP; unfold DGif0.dshadow, ImgBaseDG.DGgiC.SPv, SHADOW_OFF in *; lia).
split; [lia|]. split; [exact NWIN|]. split; [exact NDZ|]. split; [exact NIZ | exact NSH].
Qed.
End Z.
