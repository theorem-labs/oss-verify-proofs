(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at 48d3cf0d8e40 (its closing
   theorem rt_m02_key_A and m2k_near) for image B (fuzz_rate.asan-ubsan): the four pieces are image B's files
   lib/AU/RtPgM02KeyCB.v, RtPgM02KeyVB.v, RtPgM02KeyFB.v chained by lib/AU/RtPgM02KitB.v m2kb_chain, and pod_nearest's
   contract comes from lib/AU/RtPgNearB.v rt_pod_nearest_B (its Section hypotheses are this file's). *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1). Proves no function (kind: segment lemma):
   rt_m02_key_B, lib/AU/RtPgSegB.v's rsb_piece_W11b_key_stmt, the key compare and the value readers of
   LLVMFuzzerTestOneInput's segment M02, from the cut KM 0x82c40 to O 0x82b48 (the key is not "reac.cfg.rate":
   at = m + 2), ABS 0x82d1c (dead), MAL 0x82de0 (the value is not a rate) or A 0x82dec (check_rate ran).

   SECTION HYPOTHESES of rt_m02_key_B: MTL : ameter_laws MT; ASTRCMP : forall fy, astrcmp_realizes (fx := fy) rsegs
   B 0x421f4 (the strcmp wrapper's contract at every float state, lib/Reusable/AStrcmpDef.v); and those of
   lib/AU/RtPgNearB.v rt_pod_nearest_B (with them it gives pod_nearest's contract at every float state): the two cells
   of the runtime's symbol record pod_nearest's code reads, HGOT : as_got_shadow B = 0x9c170 and HSC :
   as_shadow_cell B = 0xa4f38, and the five soft-float callee contracts at image B's map RtPgNearImgB.N_img (HEX,
   HLE, HFD, HSB, HGE). The frame's laws come from the kernel theorem YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgM02BaseB RtPgM02KitB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgM02KeyCB RtPgM02KeyVB RtPgM02KeyFB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgNearImgB RtPgNearB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Local Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.
Module NI := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RtPgNearImgB.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis ASTRCMP : forall fy : YK11.FPState, astrcmp_realizes (fx := fy) rsegs B M2B_STRCMP.
Hypothesis HGOT : as_got_shadow B = NI.B_GOT_SHADOW.
Hypothesis HSC : as_shadow_cell B = NI.B_SHADOW_CELL.
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract NI.N_img.
Hypothesis HLE : @G_letf2.letf2_contract NI.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract NI.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract NI.N_img.
Hypothesis HGE : @G_getf2.getf2_contract NI.N_img.

(* pod_nearest 0x83fcc at every float state (lib/AU/RtPgNearB.v rt_pod_nearest_B): the Float arm calls it at the
   float state the `flw` leaves *)
Lemma m2kb_near : forall fy : YK11.FPState, rt_pod_nearest_specX (fx := fy) rsegs B MT M2B_NEAREST.
Proof using MTL HGOT HSC HEX HLE HFD HSB HGE.
intros fy. exact (RtPgNearB.rt_pod_nearest_B (fx := fy) B MT MTL (AR_laws_ok rsegs B) HGOT HSC HEX HLE HFD HSB HGE).
Qed.

(* KM -> O (mismatch, at = m + 2) | KV -> FLT / MAL / JN -> A, by m2kb_chain *)
Theorem rt_m02_key_B : rsb_piece_W11b_key_stmt rsegs B MT.
Proof using MTL ASTRCMP HGOT HSC HEX HLE HFD HSB HGE.
exact (m2kb_chain B MT (m2kb_join B MT MTL) (m2kb_float B MT MTL m2kb_near) (m2kb_val B MT MTL)
  (m2kb_key B MT MTL ASTRCMP)).
Qed.
End t.

Print Assumptions rt_m02_key_B.
