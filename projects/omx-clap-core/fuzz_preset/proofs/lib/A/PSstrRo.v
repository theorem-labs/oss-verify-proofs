(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrRo, c-libc-stdio lane): image A's strcmp and strlen rows at the call-site texts
   with the narrow read-only premise (lib/Reusable/YGcfStrRo.v). rule 24: the functions are proved by the Qed rows
   this file cites (lib/A/PSstrcmp.v ps_strcmp_realizes_cf(m), lib/A/PSstrlen.v ps_strlen_realizes_cf(m)_closed);
   this file only carries them to the other texts.
   2026-10-29 (pstr102): presetstr-ro cc62fb91449's file (blob 98f82a5aba85) at the #102 pin A'; only the image
   fact's text and the pcs' values in the comments change (the statements cite CfImgA's fields by name).

   THE IMAGE FACT. `romA_check`: every owned byte in a non-writable segment of image A' (AB1v.tfibsegs =
   Asan.M.loaded_segments, the #102 asan twin bff8519b, pin 1be0f53d) is a const cell of lib/A/AF0m.v Tfib_const_abs
   holding its image byte, and errno lies outside those segments. The A' AF0m.v (blob 97f423adf6eb, the internal file gen_af0m.py from
   bff8519b and its collected states) makes it true; vm_compute decides it (first measured 2026-10-29 by a scratch
   copy of this check: `= true`). With it, `rom_view_A_cf` turns the consumers' arodata_okP into our rows' rom_view
   at every ARcf state (ARmcf's amc_const gives the cells through TfibSyms' ts_const).

   THE ROWS, each at ARcf and at ARcf /\ xs_placed_cf, at the trampoline pcs CfImgA's cf_pc_strcmp / cf_pc_strlen
   (0x42d20 / 0x42d18 on A', CfImgA d76378331be3), over the texts of
   lib/Reusable/YGcallMxmn.v (a Theorem Labs lane's family 1b; read-only premise PresetRodata.arodata_okP, the one home):
   - ps_strcmp_xrom_A(_xs), ps_strlen_xrom_A(_xs): astrcmp_realizes_xrom / astrlen_realizes_xrom (the consumers'
     texts with the memnorm keep LAST), from the memnorm twins ps_strcmp_realizes_cfm / ps_strlen_realizes_cfm_closed;
   - ps_strcmp_xro_A(_xs), ps_strlen_xro_A(_xs): astrcmp_realizes_xro / astrlen_realizes_xro (the consumers' texts),
     the same rows by YGcallMxmn's _forget;
   - ps_strlen_xm_A(_xs): YGcallMxmn's astrlen_realizes_xm (YGcallMx's astrlen_realizes_x, WITH rom_view, + the keep),
     from the same twin with no read-only bridge. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m CfImgA PSstrlen PSstrcmp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma romA_check : ro_clean_check tfibsegs AF0m.Tfib_const_abs AF0m.Tfib_owned_static AF0m.TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TS : AF0m.TfibSyms B.
Variables rlo rhi : Z.

Lemma rom_view_A_cf : forall ly S Hp W mem md, ARcf tfibsegs B ly S Hp W mem md ->
  PresetRodata.arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) mem) -> rom_view tfibsegs W mem.
Proof.
  intros ly S Hp W mem md HAR HRO.
  apply (rom_view_of_cells _ _ _ _ romA_check B ly W mem rlo rhi (AF0m.ts_owned _ TS) (AF0m.ts_errno _ TS));
    [|exact HRO].
  pose proof (amc_const _ _ _ _ _ (proj1 HAR)) as HC. rewrite (AF0m.ts_const _ TS) in HC. unfold AF0m.Tfib_const in HC.
  apply Forall_app in HC as [_ HC]. apply Forall_app in HC as [HC _]. exact HC.
Qed.

Local Abbreviation ARc := (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md).
Local Abbreviation ARcx := (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md /\ xs_placed_cf ly S).

Theorem ps_strcmp_xrom_A : astrcmp_realizes_xrom tfibsegs B ARc rlo rhi (@cf_pc_strcmp CfImgA.CfImg_A).
Proof. exact (astrcmp_cfm_xrom tfibsegs B rlo rhi rom_view_A_cf _ (PSstrcmp.ps_strcmp_realizes_cfm B TS)). Qed.
Theorem ps_strcmp_xrom_xs_A : astrcmp_realizes_xrom tfibsegs B ARcx rlo rhi (@cf_pc_strcmp CfImgA.CfImg_A).
Proof. exact (astrcmp_cfm_xrom_xs tfibsegs B rlo rhi rom_view_A_cf _ (PSstrcmp.ps_strcmp_realizes_cfm B TS)). Qed.
Theorem ps_strcmp_xro_A : astrcmp_realizes_xro tfibsegs B ARc rlo rhi (@cf_pc_strcmp CfImgA.CfImg_A).
Proof. exact (astrcmp_cfm_xro tfibsegs B rlo rhi rom_view_A_cf _ (PSstrcmp.ps_strcmp_realizes_cfm B TS)). Qed.
Theorem ps_strcmp_xro_xs_A : astrcmp_realizes_xro tfibsegs B ARcx rlo rhi (@cf_pc_strcmp CfImgA.CfImg_A).
Proof. exact (astrcmp_cfm_xro_xs tfibsegs B rlo rhi rom_view_A_cf _ (PSstrcmp.ps_strcmp_realizes_cfm B TS)). Qed.

Theorem ps_strlen_xrom_A : astrlen_realizes_xrom tfibsegs B ARc rlo rhi (@cf_pc_strlen CfImgA.CfImg_A).
Proof. exact (astrlen_cfm_xrom tfibsegs B rlo rhi rom_view_A_cf _ (PSstrlen.ps_strlen_realizes_cfm_closed B TS)). Qed.
Theorem ps_strlen_xrom_xs_A : astrlen_realizes_xrom tfibsegs B ARcx rlo rhi (@cf_pc_strlen CfImgA.CfImg_A).
Proof. exact (astrlen_cfm_xrom_xs tfibsegs B rlo rhi rom_view_A_cf _ (PSstrlen.ps_strlen_realizes_cfm_closed B TS)). Qed.
Theorem ps_strlen_xro_A : astrlen_realizes_xro tfibsegs B ARc rlo rhi (@cf_pc_strlen CfImgA.CfImg_A).
Proof. exact (astrlen_cfm_xro tfibsegs B rlo rhi rom_view_A_cf _ (PSstrlen.ps_strlen_realizes_cfm_closed B TS)). Qed.
Theorem ps_strlen_xro_xs_A : astrlen_realizes_xro tfibsegs B ARcx rlo rhi (@cf_pc_strlen CfImgA.CfImg_A).
Proof. exact (astrlen_cfm_xro_xs tfibsegs B rlo rhi rom_view_A_cf _ (PSstrlen.ps_strlen_realizes_cfm_closed B TS)). Qed.

Theorem ps_strlen_xm_A : astrlen_realizes_xm tfibsegs B ARc (@cf_pc_strlen CfImgA.CfImg_A).
Proof. exact (astrlen_cfm_xm tfibsegs B _ (PSstrlen.ps_strlen_realizes_cfm_closed B TS)). Qed.
Theorem ps_strlen_xm_xs_A : astrlen_realizes_xm tfibsegs B ARcx (@cf_pc_strlen CfImgA.CfImg_A).
Proof. exact (astrlen_cfm_xm_xs tfibsegs B _ (PSstrlen.ps_strlen_realizes_cfm_closed B TS)). Qed.
End a.
