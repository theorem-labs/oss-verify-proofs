(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT5.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 9b9cb4d1f613) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT5.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the RETURN arm's LEAF - DIfaceR.drain_leaf_g at
   MnEnq.acall_raw_em_x (the form MnDrain.de_drain_m_t takes, MnDrain.v:50) for the arm where Drain returns
   without recycling, assembled from what Drain's entry walk leaves at its return (YFgj.at_RETD, YFgj.v:295-306)
   and the instance's re-quarantine field DMiface.di_requar_x (DMiface.v:209-215).
   The leaf's three parts: DMspec.acall_post_x (DMspec.v:103-111), DIfaceR.acall_raw_x (DIfaceR.v:52-57) and the
   errno / memnorm keeps.  Everything the walk writes is either the quarantine's own state (owned at the state
   before OR after the transfer, which is what di_qowned says of the header and the batch cells) or Drain's
   frame (scratch), so the frame clauses follow from the walk's YFgj.MEQ with DMdrainT2.win_in_dwin's inclusion.
   rule 24: no function proved (kind: the leaf of a segment already walked, DMseg_dme.segDEm / DMseg_dmn.segDNm
   through DMsegD.postDm's at_RETD; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index
   MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check
   B1LookupCheck CONFIRM).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DIfaceR MnEnq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
(* a raw-memory frame lifts to the view (YD28.aview_frame_off's two lines, for a single address) *)
Lemma aview_of_raw : forall (Hd : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs Hd m' a = aview tfibsegs Hd m a.
Proof. intros Hd m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Section e.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variables (W : world tfibsegs) (ly : alayout) (X S' : astate).
Variables (regs regs' : bvmap 5 word) (mem mem' : word -> option byte) (md md' : Model).
Variable inst : Z.
Let sp0 : Z := spZ regs.

(* what di_requar_x gives at the transferred state *)
Hypothesis HARX : ARX inst ly S' W mem' md'.
Hypothesis HSHR : forall a, AOX ly S' a -> AOX ly X a.
(* the model and the machine state the walk returns (YFgj.at_RETD) *)
Hypothesis HMD : m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md /\ eager_used md' = eager_used md /\
  same_io md md'.
Hypothesis HREG : aregs_preserved regs regs'.
Hypothesis HPRES : forall a, sp0 - YFeuC.DSTACK <= a < sp0 -> apresent (w_H W) mem' a.
(* the walk's frame, already moved to the raw memory: outside the owned set and Drain's frame nothing changed *)
Hypothesis HRAW : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ AOX ly S' (bv_unsigned x) ->
  ~ ascratch B YFeuC.DSTACK regs (bv_unsigned x) -> mem' x = mem x.
(* errno and the memnorm bytes are untouched: neither is in the quarantine's state nor in Drain's frame *)
Hypothesis HERR : ErrnoG.errno_kept B mem mem'.
Hypothesis HMN : MemnormT.memnorm_keep tfibsegs mem mem'.

Lemma post_ret : acall_post_x B ARX AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly S' W regs' mem' md'.
Proof.
destruct HMD as (M1 & M2 & M3 & M4).
unfold acall_post_x. splits.
- exact HARX.
- apply layout_le_refl.
- apply wle_refl.
- exact HREG.
- exact M4.
- intros a A1 A2 A3 A4 _. apply aview_of_raw. apply HRAW.
  all: unfold w64 in *; rewrite unsigned_lit_small by lia; assumption.
- exact HPRES.
Qed.

Lemma raw_ret : acall_raw_x B AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly S' W regs' mem' md'.
Proof. intros x A1 A2 A3 _. exact (HRAW x A1 A2 A3). Qed.

Theorem leaf_ret : DIfaceR.drain_leaf_g B ARX AOX (MnEnq.acall_raw_em_x B AOX) inst ly X W regs mem md
(tt, S') W (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
exists regs', mem', md'. split; [reflexivity|]. split; [exact post_ret|].
unfold MnEnq.acall_raw_em_x. split; [exact raw_ret | split; [exact HERR | exact HMN]].
Qed.
End e.
End c.
