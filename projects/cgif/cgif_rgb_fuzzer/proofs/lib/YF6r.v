(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF77 YF6u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition xrun_to {imgk : img} (stop : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rr FUEL stop ss).
Definition xrun {imgk : img} (ss : sstate) : sstate := fst (sym_runN_sh tfxsegs tfxtbl_rr FUEL ss).
Definition xpin (r : bv 5) (e : sv) (ss : sstate) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xadd (r : YQ0b.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xafter (k : nat) (stklo retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with r0 :: rest => trim_lo r0 stklo :: rest | [] => [] end) k retpc.
Definition xafterU (k : nat) (retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with rim :: _ :: rfr :: rest => rim :: trim_lo rfr (-64) :: rest | _ => [] end) k retpc.
Definition IFRAMER : Z := 2144.
Definition R_SCRR : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAMER) (- ASTACK) (- IFRAMER) [].
Definition R_IMR : YQ0b.region := YQ0b.mkRegion (Some 37%nat) 8 16 0 0 [YQ0b.mkChunk 8 (CZero 8)].
Definition R_OBJR : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- 2136) (- 64) 0 0
[YQ0b.mkChunk (- 2136) (CVal 8 (SOff 2 (- 2120))); YQ0b.mkChunk (- 2128) (CVal 8 (SOff 36%nat 0))].
Definition SS_L1R {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x5e984 + D_2c4) YF6u.SS0)))).
Definition SS_P1R {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun (xpin 10 (SLit TFX_IAL_LO) (xadd R_IMR (xadd R_SCRR (xafter 54 (-2144) (0x53548 + D_2c4) SS_L1R)))))))).
Definition SS_P2R {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x5355c + D_2c4) (xpin 11 (SLit 0) SS_P1R))))).
Definition SS_AR {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x5aea0 + D_2c4) (xpin 12 (SOff 37%nat 0) SS_P2R))))).
Definition SS_ER {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x323b8 + D_150) (xadd R_OBJR (xadd R_SCRR (xafterU 70 (0x5369c + D_2c4) SS_AR))))))).
Goal forall imgk : img, ss_pc SS_L1R = (0x5e984 + D_2c4) /\ ss_pc SS_P2R = (0x5355c + D_2c4) /\ ss_pc SS_AR = (0x5aea0 + D_2c4) /\ ss_pc SS_ER = (0x323b8 + D_150). Proof. intros imgk. repeat split; img_refl. Qed.
