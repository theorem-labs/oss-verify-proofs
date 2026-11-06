(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrRo, c-libc-stdio lane): image B's strcmp and strlen rows at the call-site texts
   with the narrow read-only premise (lib/Reusable/YGcfStrRo.v). rule 24: the functions are proved by the Qed rows
   this file cites (lib/AU/PSstrcmp.v ps_strcmp_realizes_cfm_B, lib/AU/PSstrlen.v ps_strlen_realizes_cfm_B_closed);
   this file only carries them to the other texts.
   2026-10-29 (pstr102): presetstr-ro cc62fb91449's file (blob 2f0940b8ff76) at the #102 pin B'; only the image
   fact's text and the pcs' values in the comments change (the statements cite CfImgB's fields by name).

   THE IMAGE FACT. `romB_check`: every owned byte in a non-writable segment of image B' (YB1v.tfibsegs =
   AsanUbsan.M.loaded_segments, the #102 asan-ubsan twin c90d4fa5, pin d663f82d) is a const cell of
   lib/Reusable/YF0m.v Tfib_const_abs holding its image byte, and errno lies outside those segments. The B' YF0m.v
   (blob f82202ebccdf, h-pre-b3 bp-startup, gen_yf0m.py from d663f82d and its collected states) makes it true;
   vm_compute decides it (first measured 2026-10-29 by a scratch copy of this check: `= true`). With it,
   `rom_view_B_cf` turns the consumers' arodata_okP into our row's rom_view at every ARcf state.

   THE ROWS, at ARcf and at ARcf /\ xs_placed_cf, at the trampoline pcs CfImgB's cf_pc_strcmp / cf_pc_strlen
   (0x42e0c / 0x42e04 on B', CfImgB 82495e01f675), over the texts of lib/Reusable/YGcallMxmn.v (a Theorem Labs lane's family 1b;
   read-only premise PresetRodata.arodata_okP, the one home):
   - ps_strcmp_xrom_B(_xs), ps_strlen_xrom_B(_xs): astrcmp_realizes_xrom / astrlen_realizes_xrom (the consumers' texts
     with the memnorm keep LAST), from the memnorm twins;
   - ps_strcmp_xro_B(_xs), ps_strlen_xro_B(_xs): astrcmp_realizes_xro / astrlen_realizes_xro (ExvB_StrcmpRo.v's /
     ExwB_StrlenRo.v's texts), the same rows by YGcallMxmn's _forget;
   - ps_strlen_xm_B(_xs): astrlen_realizes_xm (YGcallMx's astrlen_realizes_x, WITH rom_view, + the keep), from the
     same twin with no read-only bridge. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YG0d2cf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn YGcfStrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrlen PSstrcmp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma romB_check : ro_clean_check tfibsegs YF0m.Tfib_const_abs YF0m.Tfib_owned_static YF0m.TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TS : YF0m.TfibSyms B.
Variables rlo rhi : Z.

Lemma rom_view_B_cf : forall ly S Hp W mem md, ARcf tfibsegs B ly S Hp W mem md ->
  PresetRodata.arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) mem) -> rom_view tfibsegs W mem.
Proof.
  intros ly S Hp W mem md HAR HRO.
  apply (rom_view_of_cells _ _ _ _ romB_check B ly W mem rlo rhi (YF0m.ts_owned _ TS) (YF0m.ts_errno _ TS));
    [|exact HRO].
  pose proof (amc_const _ _ _ _ _ (proj1 HAR)) as HC. rewrite (YF0m.ts_const _ TS) in HC. unfold YF0m.Tfib_const in HC.
  apply Forall_app in HC as [_ HC]. apply Forall_app in HC as [HC _]. exact HC.
Qed.

Local Abbreviation ARc := (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md).
Local Abbreviation ARcx := (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md /\ xs_placed_cf ly S).

Theorem ps_strcmp_xrom_B : astrcmp_realizes_xrom tfibsegs B ARc rlo rhi (@cf_pc_strcmp CfImgB.CfImg_B).
Proof. exact (astrcmp_cfm_xrom tfibsegs B rlo rhi rom_view_B_cf _ (PSstrcmp.ps_strcmp_realizes_cfm_B B TS)). Qed.
Theorem ps_strcmp_xrom_xs_B : astrcmp_realizes_xrom tfibsegs B ARcx rlo rhi (@cf_pc_strcmp CfImgB.CfImg_B).
Proof. exact (astrcmp_cfm_xrom_xs tfibsegs B rlo rhi rom_view_B_cf _ (PSstrcmp.ps_strcmp_realizes_cfm_B B TS)). Qed.
Theorem ps_strcmp_xro_B : astrcmp_realizes_xro tfibsegs B ARc rlo rhi (@cf_pc_strcmp CfImgB.CfImg_B).
Proof. exact (astrcmp_cfm_xro tfibsegs B rlo rhi rom_view_B_cf _ (PSstrcmp.ps_strcmp_realizes_cfm_B B TS)). Qed.
Theorem ps_strcmp_xro_xs_B : astrcmp_realizes_xro tfibsegs B ARcx rlo rhi (@cf_pc_strcmp CfImgB.CfImg_B).
Proof. exact (astrcmp_cfm_xro_xs tfibsegs B rlo rhi rom_view_B_cf _ (PSstrcmp.ps_strcmp_realizes_cfm_B B TS)). Qed.

Theorem ps_strlen_xrom_B : astrlen_realizes_xrom tfibsegs B ARc rlo rhi (@cf_pc_strlen CfImgB.CfImg_B).
Proof. exact (astrlen_cfm_xrom tfibsegs B rlo rhi rom_view_B_cf _ (PSstrlen.ps_strlen_realizes_cfm_B_closed B TS)). Qed.
Theorem ps_strlen_xrom_xs_B : astrlen_realizes_xrom tfibsegs B ARcx rlo rhi (@cf_pc_strlen CfImgB.CfImg_B).
Proof.
  exact (astrlen_cfm_xrom_xs tfibsegs B rlo rhi rom_view_B_cf _ (PSstrlen.ps_strlen_realizes_cfm_B_closed B TS)).
Qed.
Theorem ps_strlen_xro_B : astrlen_realizes_xro tfibsegs B ARc rlo rhi (@cf_pc_strlen CfImgB.CfImg_B).
Proof. exact (astrlen_cfm_xro tfibsegs B rlo rhi rom_view_B_cf _ (PSstrlen.ps_strlen_realizes_cfm_B_closed B TS)). Qed.
Theorem ps_strlen_xro_xs_B : astrlen_realizes_xro tfibsegs B ARcx rlo rhi (@cf_pc_strlen CfImgB.CfImg_B).
Proof.
  exact (astrlen_cfm_xro_xs tfibsegs B rlo rhi rom_view_B_cf _ (PSstrlen.ps_strlen_realizes_cfm_B_closed B TS)).
Qed.

Theorem ps_strlen_xm_B : astrlen_realizes_xm tfibsegs B ARc (@cf_pc_strlen CfImgB.CfImg_B).
Proof. exact (astrlen_cfm_xm tfibsegs B _ (PSstrlen.ps_strlen_realizes_cfm_B_closed B TS)). Qed.
Theorem ps_strlen_xm_xs_B : astrlen_realizes_xm tfibsegs B ARcx (@cf_pc_strlen CfImgB.CfImg_B).
Proof. exact (astrlen_cfm_xm_xs tfibsegs B _ (PSstrlen.ps_strlen_realizes_cfm_B_closed B TS)). Qed.
End b.
