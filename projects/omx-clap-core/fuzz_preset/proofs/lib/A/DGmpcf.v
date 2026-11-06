(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGmpcf.v (commit 3cae605a900a, blob 9eb23212eca4) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG03 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DGbase DGgi DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.

Definition MPcf (B : asyms) (m : word -> option byte) : Prop :=
arodata_ok_cf tfibsegs B m.

Definition zones_miss_relro (B : asyms) : Prop :=
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU,
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
0 <= a < 2 ^ 64 /\ ~ dwin_m ly (bv_unsigned (getr regs0 2)) p a /\ ~ dg_dzone ly a /\ ~ dg_izone a /\
~ dshadow p nn a.

Theorem MP_keep_cf : forall B, zones_miss_relro B ->
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
(forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
  ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
MPcf B mem0 -> MPcf B mem'.
Proof.
intros B HZ W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU mem' FH FR HRO.
apply (arodata_frame_cf tfibsegs B
  (fun a => dwin_m ly (bv_unsigned (getr regs0 2)) p a \/ dg_dzone ly a \/ dg_izone a \/ dshadow p nn a)
  mem0 mem').
- intros x NX. apply FR; intros Y; apply NX; tauto.
- intros a Ha NO.
  destruct (HZ W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha NO) as (R & N1 & N2 & N3 & N4).
  split; [exact R|]. intros [X|[X|[X|X]]]; [exact (N1 X) | exact (N2 X) | exact (N3 X) | exact (N4 X)].
- exact HRO.
Qed.
End a.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem zones_miss_relro_preset : forall B, zones_miss_relro (ci := CfImg_A) B.
Proof.
intros B W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha0 _.

assert (Ha : 0x10000 <= a < 0xa3000).
{ unfold aro_addr_cf in Ha0. cbn [cf_relro_lo cf_relro_hi cf_ro_reads CfImg_A] in Ha0.
  destruct Ha0 as [Ha0|Ha0]; [lia|].
  apply Exists_exists in Ha0 as (r & Hr & Hin). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hin; cbn [fst snd] in Hin; lia. }
clear Ha0.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (ZT & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _ & _ & _ & _ & _ & HSTKLO).
pose proof (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (DP & _).
pose proof (DGgm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & _ & _).
pose proof (DGgm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (DGgm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as [N8a N8b].
assert (HIMG : TFIB_IMG_LO <= a < TFIB_IMG_END) by (unfold TFIB_IMG_LO, TFIB_IMG_END; lia).
assert (Hp8 : 0 <= p / 8) by (apply Z.div_pos; lia).

assert (NDZ : ~ DGgi.DZONE ly a).
{ unfold DGgi.DZONE. intros [Hd|[Hd|Hd]].
  - lia.
  - exact (AF0x.zone3_apart_img (ly_NB ly) kNodesBlockSize a ZNB HIMG Hd).
  - exact (AF0x.zone3_apart_img (ly_SB ly) kStoreBlockSize a ZSB HIMG Hd). }
assert (NIZ : ~ DGgi.IZONE a)
  by (unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG; lia).
assert (NWIN : ~ dwin_m ly (bv_unsigned (getr regs0 2)) p a).
{ unfold dwin_m, DGgmC.WINT, DGgmC.WINB, DGbaseC.DFSTACK. cbv beta zeta.
  unfold DGbase.DFSTACK in S1. unfold kHighMemBeg in HSTKLO.
  intros [Hw|[[Hw|Hw]|[Hw|Hw]]].
  - lia.
  - exact (AF0x.zone3_apart_img (ly_T ly) kThreadObjSize a ZT HIMG
      ltac:(unfold t_unwinding, kThreadObjSize in *; lia)).
  - exact (AF0x.zone3_apart_img (ly_T ly) kThreadObjSize a ZT HIMG
      ltac:(unfold t_stats, kThreadObjSize in *; lia)).
  - exact (AF0x.zone3_apart_img (p - 16) (DGgm.N8v nn + 16) a HP HIMG ltac:(lia)).
  - exact (AF0x.zone3_apart_img (p - 16) (DGgm.N8v nn + 16) a HP HIMG ltac:(lia)). }
assert (NSH : ~ dshadow p nn a)
  by (unfold dshadow, DGgiC.SPv, SHADOW_OFF; lia).
split; [lia|]. split; [exact NWIN|]. split; [exact NDZ|]. split; [exact NIZ | exact NSH].
Qed.

Theorem MP_keep_cf_preset : forall B,
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
(forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
  ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
MPcf (ci := CfImg_A) B mem0 -> MPcf (ci := CfImg_A) B mem'.
Proof. intros B. exact (MP_keep_cf (ci := CfImg_A) B (zones_miss_relro_preset B)). Qed.
End b.

Check MP_keep_cf.
Check zones_miss_relro_preset.
Print Assumptions zones_miss_relro_preset.
