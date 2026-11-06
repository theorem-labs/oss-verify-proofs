(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's arguments of the shared snprintf top (Reusable/FMsnprintfSharedCf.v
   sh_asnprintf_realizes_cf) at image A, for AsanAPI_cf's aa_snprintf_cf (CfApiPreset.v pa_snprintf_cf).
   PER-UNIT file, not in the shared set. Statements only; nothing is proved here.
   - FF_preset: the format family. put_string (src/preset_file.c:484-512) is the one caller of __wrap_snprintf in the
     target's code; the two formats that reach it in both images are "\\%c" and "\\u%04x" (the "\\n" / "\\t" / "\\r"
     cases compile to a 3-byte copy), so the pieces are literals, %c and %04x. The family is port-fm's FF_fm
     (cold/port-fm-rtprintf-param 7e395de08f5, lib/A/FMsnprintfFmI.v:28-33) over these pieces: the format lies in the
     image from cf_img_lo up to the stack-protector GOT cell (GXA reads it as image data below that cell,
     FMgxaSeamDef.v:29-31 there) and is nonempty. FF_fm's pf_args_slack / pf_args_amem are left out: with no %s or
     %.*s piece every argument is an AInt, and both constrain only APtr arguments.
   - snp_K_A: the window, image A's cf_snprintf_glue (the four frames from the wrapper's entry down to musl
     vfprintf's entry) plus GXA's musl vfprintf depth SNP_VF_DEPTH (VF_DEPTH = VFA_DEPTH 368 + PC_DEPTH 5184:
     lib/CJ/RL/GXA/G_printf_core_common.v:142 and G_vfprintf_snf.v:55 in fuzz_manifest's tree at 7e395de08f5;
     port-fm's GXA_VF_DEPTH, FMsnprintfFm.v:30-32 there). Image A's musl vfprintf frame is 368.
   - snp_cr: the read-only ranges, every non-writable segment of segs (port-fm's fm_cr expression,
     FMsnprintfCr.v:22-23 at 7e395de08f5).
   The canary cells and the image range are CfImg_A's generated fields cf_got_stack_chk_guard, cf_stack_chk_guard,
   cf_img_lo and cf_img_top. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FMsnprintfPf FMsnprintfShared.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA.
(* stdpp, through the LPS modules, shadows several list names; the list functions here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* put_string's conversions: literal bytes, %c and %04x *)
Definition pf_preset_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Pc | Px04 => True | _ => False end.

(* port-fm's FF_fm at preset's pieces and image A's bounds *)
Definition FF_preset : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall pf_preset_piece ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    @cf_img_lo CfImg_A <= f /\ f + Z.of_nat (length fmt) + 1 <= @cf_got_stack_chk_guard CfImg_A /\ fmt <> [].

(* GXA's musl vfprintf depth (the released text's VF_DEPTH) *)
Definition SNP_VF_DEPTH : Z := 5552.

(* the snprintf top's window at image A *)
Definition snp_K_A : Z := @cf_snprintf_glue CfImg_A + SNP_VF_DEPTH.

(* the read-only ranges: every non-writable segment *)
Definition snp_cr (segs : list Segment) : list (Z * Z) :=
  List.map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s)))
    (List.filter (fun s : Segment => negb (seg_writable s)) segs).
