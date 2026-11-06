(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new for libreac/fuzz_boxreg: the image premise of FMgxa_bridge.v (a Theorem Labs lane's
   srr_of_gxa_evt, Hwx : wx_segs_nowrap) discharged at this unit's harness image. *)
(* proves no function (kind: segment lemma).  The W^X fact of fuzz_boxreg.asan-ubsan's boxb_segs is the unit's already proved
   boxb_wx (lib/B/Prog/BoxBImg.v, a computed proof on a closed boolean goal: wx_segs_nowrap_of_b, then
   vm_compute on that goal with no evar); boxb_segs (lib/B/Prog/BoxBImg.v; = BoxTFIB.v boxsegsB0 by delta) and boxb_wx's segments are the same
   loaded_segments by delta, so it is cited, not recomputed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YP02 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Exec Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import RT_IImgA FMgxa_bridge.
Import ListNotations.
Open Scope Z_scope.

Lemma gxa_wx : wx_segs_nowrap boxb_segs.
Proof. exact BoxBImg.boxb_wx. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a Theorem Labs lane's srr_of_gxa_evt with its image premise discharged *)
Lemma srr_of_gxa_evt_wx : forall (W : world boxb_segs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world boxb_segs -> config -> Prop),
Exec.evt (@img_segs A_img) Q (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom boxb_segs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr boxb_segs W (cfg_at boxb_segs pc regs mem md) POST.
Proof. intros. eapply srr_of_gxa_evt; eassumption || exact gxa_wx. Qed.

End b.
