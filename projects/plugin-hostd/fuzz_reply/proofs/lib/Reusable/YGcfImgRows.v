(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfImgRows.v, sha256 bb51d500185fb488f92980f5fed9612f2fe126dd37b7e28a0e090b50b297c411 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch 76362ece943 (CfInstHit's class-free image rows), for field round 2: AR_frame_law_ok_cf takes EXH_OFF_t; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The CLASS-FREE cf unit IMAGE ROWS, each stated ONCE (Main, 2026-10-30): no AGImg / AImgS class, so the drain layer
   (CfF2b's YGcfInstDrain*.v) and the Allocate instance files both take them by path.
   - ERRB_QAPART: the error-message-buffer object is apart from the instance object.  CfF2b's text VERBATIM
     (YGcfInstDrainX.v:77-78 @ a working branch 8b12df2b772); it is the first clause of YGcfErrbSep.ERRB_SEP_t.
   - EXH_OFF_t: the per-class exhausted byte is RegionInfo + 68 (YGcfInstBase.exh_cell_cf's offset is the walks'
     RGv + 68); [EXH_OFF_bound] is the bound the hit and secondary posts read.
   rule 24: no function proved (statements of unit image rows and a projection). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames ImgBase.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.

Definition ERRB_QAPART : Prop :=
forall B, im_syms B -> forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> ~ (as_inst B <= a < as_inst B + 3632).

Definition EXH_OFF_t : Prop := cf_exh_off = 68.

Lemma EXH_OFF_bound : EXH_OFF_t -> 0 <= cf_exh_off < 128.
Proof. intros E. rewrite E. split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity. Qed.
End a.
