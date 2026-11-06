(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's arguments of the snprintf row (Reusable/YGcallSnp.v asnprintf_realizes_xrom,
   c-omx-alloc's restatement of port-fm's shared top) at image B (asan-ubsan), for AsanAPI_cf's aa_snprintf_cf
   (CfApiPresetB.v pa_snprintf_cf_B). The image-B twin of lib/A/CfSnprintfPreset.v (blob 29945739be86): PER-UNIT
   file, not in the shared set. Statements only; nothing is proved here.
   The two definitions of CfSnprintfPreset.v that name CfImg_A get a twin here over CfImg_B's generated fields;
   the image-free definitions are reused from CfSnprintfPreset.v, qualified:
   - FF_preset_B: FF_preset with CfImg_B's cf_img_lo and cf_got_stack_chk_guard as the format's bounds. The pieces
     are CfSnprintfPreset.pf_preset_piece: put_string's two formats "\\%c" and "\\u%04x" reach __wrap_snprintf in
     both images (CfSnprintfPreset.v's header).
   - snp_K_B: snp_K_A with CfImg_B's cf_snprintf_glue (the four frames from the wrapper's entry down to musl
     vfprintf's entry, generated from the asan-ubsan ELF) plus the same GXA depth CfSnprintfPreset.SNP_VF_DEPTH.
   - The read-only ranges are CfSnprintfPreset.snp_cr: it depends only on the segment list.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FMsnprintfPf FMsnprintfShared.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfSnprintfPreset.
(* stdpp, through the LPS modules, shadows several list names; the list functions here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* port-fm's FF_fm at preset's pieces and image B's bounds *)
Definition FF_preset_B : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall CfSnprintfPreset.pf_preset_piece ps /\
    pf_args_asan rd rs ws args /\ pf_text ps args = Some T /\ pf_prec_pos ps args /\
    @cf_img_lo CfImg_B <= f /\ f + Z.of_nat (length fmt) + 1 <= @cf_got_stack_chk_guard CfImg_B /\ fmt <> [].

(* the snprintf top's window at image B *)
Definition snp_K_B : Z := @cf_snprintf_glue CfImg_B + CfSnprintfPreset.SNP_VF_DEPTH.
