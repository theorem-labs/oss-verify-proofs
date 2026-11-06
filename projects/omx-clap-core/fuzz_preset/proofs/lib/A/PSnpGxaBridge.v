(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YEvtSRr.v, with its module paths changed; 22 of its 57 lines of code are new or changed and 87 lines of the source are left out. *)
(* The bridge from the GXA (ASan printf core) walks to the harness's call-site form.
   GXA ends every walk in the CJ tree's `evt img_segs Q ms`: "some step chain from ms reaches a
   state in Q" (lib/CJ/Lib/Exec.v:41, over `msteps` at Exec.v:21).  The harness continues from
   `SRr segs W (cfg_at segs pc regs mem md) POST` (lib/Reusable/YA0n.v:35).  This file is the
   generic half of the join, for the CJ tree.

   Three facts make it one short file, the same three that FMbz_bridge.v (port-fm's RtScan,
   origin/cold/port-fm-rtscan 445e498a469) uses for the Bz tree:
   - the two trees name the same image: `@img_segs N_img_asan = tfibsegs` by reflexivity, because
     RT_IImgA.v:96 builds N_img_asan on tfibsegs;
   - the two step relations are the same relation: CJ's `mstep` (Exec.v:18) is
     `ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'`, which is what each
     step of the harness's `msteps` (lib/Reusable/YK0i.v) asks;
   - the harness already lifts its own `msteps` into `SRr` (`SRr_msteps`, YA0n.v).

   `mkst` and `seg_rom` are written qualified: the CJ tree defines its own `mkst`, which empties
   the floating-point registers, while the harness's `cfg_at` uses YK11's over fx.  An import order
   that let the CJ name win here would state these lemmas about another machine state. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (L3-V2, the GXA seam over ARx; parent c-libc-stdio 14:3xZ) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxa_bridge.v at origin/cold/port-fm-rtprintf-param 3e35620c52e: module paths fuzz_manifest -> fuzz_preset; the image record RT_IImgA.A_img -> preset's rebuilt-pin lib/CJ/RL/I/IImgA.v N_img_asan (taken by path by c-libc-str, f697dea427f); gxa_segs_tfib_vsn (fm's second record A_img_vsn) is left out. @img_segs N_img_asan = tfibsegs holds by reflexivity: N_img_asan is built on Img0.rsegs, AB1v.tfibsegs is the same Asan.M.loaded_segments. The sentences above name fm's files. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YP02 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Exec Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma gxa_segs_tfib : @img_segs N_img_asan = tfibsegs.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* one step of a GXA walk is one step of the harness's walk *)
Lemma cj_msteps_tfib : forall ms ms', Exec.msteps tfibsegs ms ms' -> YK0i.msteps tfibsegs ms ms'.
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
- apply YK0i.mst_refl.
- destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

(* a GXA walk that reaches Q, read at a harness call site: the walk runs on the restricted memory,
   and what it reaches is the configuration the harness continues from.
   Hwx is the image's own W^X fact; it is a premise here so that this bridge does not wait for it. *)
Lemma srr_of_cj_evt : forall (Hwx : wx_segs_nowrap tfibsegs) (W : world tfibsegs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
Exec.evt tfibsegs Q (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom tfibsegs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
intros Hwx W pc regs mem md Q POST (ms' & Hms & HQ) HK.
unfold cfg_at.
eapply (SRr_msteps tfibsegs Hwx W (YK11.mkst regs (w64 pc) mem (YK11.seg_rom tfibsegs)) ms' md POST).
- exact (cj_msteps_tfib _ _ Hms).
- intros model' Hsame Hcl. apply SRr_ret. cbn [ms_mem YK11.mkst]. exact (HK ms' model' HQ Hsame Hcl).
Qed.

(* the same, written at the GXA image record, so a GXA theorem applies without a rewrite *)
Lemma srr_of_gxa_evt : forall (Hwx : wx_segs_nowrap tfibsegs) (W : world tfibsegs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
Exec.evt (@img_segs N_img_asan) Q (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom tfibsegs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof. intros Hwx W pc regs mem md Q POST H HK. exact (srr_of_cj_evt Hwx W pc regs mem md Q POST H HK). Qed.

(* the stack window the harness's call-site premise gives is the window a GXA walk asks for *)
Lemma stk_of_apresent : forall (H : word -> bool) (mem : word -> option byte) (lo hi : Z),
0 <= lo -> hi <= 2 ^ 64 ->
(forall a, lo <= a < hi -> apresent H mem a) ->
Frame.stk tfibsegs (mrestrict H mem) lo hi.
Proof.
intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
assert (Em : mrestrict H mem (Mem.wa a) = Some b).
{ unfold mrestrict, Mem.wa. rewrite HH. exact Hb. }
split.
- unfold wview. rewrite Em. discriminate.
- exists b. unfold Mem.mrd. rewrite Em. reflexivity.
Qed.

End b.
