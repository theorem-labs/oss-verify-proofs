(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: COPY (image-generic, unchanged) of lib/A/Prog/PRW_S7bKit.v at origin/cold/h-hpreset-7-walk-S7B 7819c4b4583 (blob 267122d676a1) *)
(* fuzz_preset, program part, slice S7b (WalkS7b of h-rw-pre-5): the STATED HYPOTHESES the writer walks
   (pj_write, write_value, put_string) take that no file of record states yet. Definitions only; no proof. Each walk
   takes them as Section hypotheses; each is discharged at assembly by its owner's statement.
   (1) The harness-block shadow law is NOT here: it is AR_laws_x field 14 alx_hshadow (YCbqG 83da015952be). Here:
       ARx_cell_vis (an image cell visible under ARx), a marked stand-in.
   (2) put_string's snprintf call (A 0x8805c, `jal __wrap_snprintf`, escape buffer size 8, formats `\\%c` / `\\u%04x`)
       is NOT stated here any more: the old stand-in asnprintf_esc_realizes_x (this file at 7ffbb0405d3, :79-100) was
       too strong (it kept the caller's whole float state and lacked 17 premises; c-omx-alloc 11:56Z). A walk takes the
       FINAL snprintf ROW `asnprintf_realizes_xrom` (lib/Reusable/YGcallSnp.v blob d0d7bdd020f3 :100, from
       origin/cold/c-omx-alloc-snprow 193779166e07; call rule aj_snprintf_at_xrom :197, implication form) as its
       hypothesis and calls through `snp_esc_realizes_xrom` (YGcallSnpCk.v blob 94a1802b3e54 :177), proved from the row
       by `snp_esc_of_xrom` (:317), with fx' after the call. The double printf_common nesting is in the row's premises.
   Numerals: 8 (LENGTH: a word). No ADDRESS numeral in a statement; the addresses above are image A's, for the reader
   only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Export PutStringB_HShadow.
Import ListNotations.
Local Open Scope Z_scope.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* (* STAND-IN until an ARx image-visibility law (either of two Theorem Labs lanes) *) an image cell the runtime reads in every state (the
   stack-protector guard printf_core reads): its 8 bytes are visible under ARx. Image bytes are mapped for the whole
   run and no runtime step hides them; ARx keeps no such clause today. *)
Definition ARx_cell_vis (c : Z) : Prop :=
  forall ly S Hp W mem md, ARx ly S Hp W mem md -> forall i, 0 <= i < 8 -> aview segs (w_H W) mem (c + i) <> None.

End k.
