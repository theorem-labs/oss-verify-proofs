(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT2.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 b2fdc32aeebd) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT2.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the drain's window inclusion - everything the entry walk may write
   (YFgj.WIN, YFgj.v:171-174: Drain's 80-byte frame, the quarantine's mutex word and global header, the thread
   cache's header, and the global list's last next word) lies inside the changed set DMiface.dwin_q
   (DMiface.v:114-115) of a drain cut.  It is what turns the walk's frame (YFgj.MEQ) into the cut memory relation
   DMiface.dmem_q's first clause, on EVERY arm of the drain, so it is proved once here.
   rule 24: no function proved (kind: a frame inclusion over segments already walked; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [win_in_dwin]: YFgj.WIN is inside DMiface.dwin_q;
   - [dmem_frame]: the walk's frame gives dmem_q's first clause.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
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
(* the instance object is the image's allocator (DMiface.qview's qv_inst with TfibSyms) *)
Hypothesis Hinst : inst + o_quar = A_QUAR.
(* the global cache's last batch, when there is one: its address is the walk's WINA *)
Hypothesis Hglast : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  YFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X).

Lemma win_in_dwin : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> dwin_q inst ly sp0 X S' P a.
Proof.
intros a Ha. unfold dwin_q, qhdr, bcellw.
unfold YFgj.WIN, YFgj.WINF, YFgj.WINA in Ha. fold sp0 in Ha.
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
(forall x : word, ~ YFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x) ->
forall x : word, ~ dwin_q inst ly sp0 X S' P (bv_unsigned x) -> mem' x = mem0 x.
Proof.
intros HM x Hx. apply HM. intros HW. apply Hx. exact (win_in_dwin _ HW).
Qed.
End e.
End c.
