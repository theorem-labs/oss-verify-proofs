(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfImgRows.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, the cf-hit lane; integrator ReallocPrimary).
   The CLASS-FREE cf unit IMAGE ROWS, each stated ONCE (Main, 2026-10-30): no AGImg / AImgS class, so the drain layer
   (CfF2b's YGcfInstDrain*.v) and the Allocate instance files both take them by path.
   - ERRB_QAPART: the error-message-buffer object is apart from the instance object.  CfF2b's text VERBATIM
     (YGcfInstDrainX.v:77-78 @ commit 8b12df2b772); it is the first clause of YGcfErrbSep.ERRB_SEP_t.
   - EXH_OFF_t: the per-class exhausted byte is RegionInfo + 68 (YGcfInstBase.exh_cell_cf's offset is the walks'
     RGv + 68); [EXH_OFF_bound] is the bound the hit and secondary posts read.
   rule 24: no function proved (statements of unit image rows and a projection). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames ImgBase.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.

Definition ERRB_QAPART : Prop :=
forall B, im_syms B -> forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> ~ (as_inst B <= a < as_inst B + 3632).

Definition EXH_OFF_t : Prop := cf_exh_off = 68.

Lemma EXH_OFF_bound : EXH_OFF_t -> 0 <= cf_exh_off < 128.
Proof. intros E. rewrite E. split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity. Qed.
End a.
