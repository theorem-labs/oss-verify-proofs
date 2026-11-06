(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT2.v (commit 67deba317dfb, blob b846ffb0abbf) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variables (W : world tfibsegs) (ly : alayout) (X S' : astate).
Variables (regs0 : bvmap 5 word) (mem0 mem' : word -> option byte).
Variable P : list batch.
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).

Hypothesis Hinst : inst + o_quar = A_QUAR.

Hypothesis Hglast : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  AFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X).

Lemma win_in_dwin : forall a, AFgj.WIN ly regs0 (st_qglobal X) a -> dwin_q inst ly sp0 X S' P a.
Proof.
intros a Ha. unfold dwin_q, qhdr, bcellw.
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in Ha. fold sp0 in Ha.
destruct Ha as [Ha | [[Ha | [Ha | Ha]] | [Hne Ha]]].
- left. unfold YFeuC.DSTACK. lia.
- right; left. left. rewrite Hinst. lia.
- right; left. right; left. rewrite Hinst. lia.
- right; left. right; right. lia.
- right; right.
  destruct (rev (qc_list (st_qglobal X))) as [|lastb initr] eqn:ER.
  + exfalso. apply Hne. rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. reflexivity.
  + destruct (Hglast lastb initr eq_refl) as [EG HIN].
    exists lastb. split.
    * apply in_app_iff. left. exact HIN.
    * rewrite EG in Ha. assert (0 <= 8 * Z.of_nat (length (b_items lastb))) by lia. lia.
Qed.

Lemma dmem_frame :
(forall x : word, ~ AFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x) ->
forall x : word, ~ dwin_q inst ly sp0 X S' P (bv_unsigned x) -> mem' x = mem0 x.
Proof.
intros HM x Hx. apply HM. intros HW. apply Hx. exact (win_in_dwin _ HW).
Qed.
End e.
End c.
