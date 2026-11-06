(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: GENERATED from lib/A/PresetD1preAx.v (lane CwPreA, a working branch a9e03801db9b) by port/a2b.py (sha256 e4f47803449f38c2) with its measured literal map (a table literal in code is written as its image-B cell name from lib/Reusable/YImgCellsB.v) and --map 0x10000=0x10000 0x20e00=0x20e00 0x20f40=0x20f40 (image B's first zero-shadow range is also (YImgTop.IMG_LO, 0x20f40 - YImgTop.IMG_LO), lib/Reusable/YF0m.v Tfib_zero_shadow). No hand edit. PENDING YF0m, as PresetD1preB.v. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset (asan-ubsan image), the driver's interceptor SITE
   results over the second allocator instance ARcf, made from the core's lib/Reusable (relocated from
   proofs/cgif/cgif_file_fuzzer/lib): YD1k.v:273 tfib_fwrite_site, :314 tfib_refused_site and YD1l.v:147 / :152 /
   :157 tfib_fprintf_{open,rderr,usage}_site, over this lane's site forms (lib/AU/PresetD1preB.v).
   Changes from the donor: the sites are over ARcf at Hp = []; the stderr state est is a parameter, with the one fact
   of it each proof uses (the donor's YD1k.v:103 est_written for the fwrite site, :105 est_after_vf for the fprintf
   sites), so that this file does not import YD1k.v; the driver lane instantiates est := YD1k.est with those two
   lemmas. The proofs (PresetD1preBxPf.v) use the ARcf copies of the interceptor walks (YE2x / YE2t / YE2u / YE2v /
   YE2w and their closure, copied mechanically to <name>cf.v), not premises.
   Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YD2j YD2i YD1t YD20
YD1v YD2h YD2f YD1w YD1x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YE2p YE3h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1preB.
Import ListNotations.
Local Open Scope Z_scope.

(* YD1k.v:273 tfib_fwrite_site. *)
Definition tfib_fwrite_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, YE2p.stderr_written (mrestrict H m) -> est H m) ->
fwrite_site_tfa_cf B est.

(* YD1k.v:314 tfib_refused_site. *)
Definition tfib_refused_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, YE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
refused_site_tfa_cf B est.

(* YD1l.v:147 tfib_fprintf_open_site. *)
Definition tfib_fprintf_open_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, YE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0XD562 (strB "cli: cannot open "%string) nlB.

(* YD1l.v:152 tfib_fprintf_rderr_site. *)
Definition tfib_fprintf_rderr_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, YE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0XD577 (strB "cli: read error on "%string) nlB.

(* YD1l.v:157 tfib_fprintf_usage_site. *)
Definition tfib_fprintf_usage_site_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, YE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0X55CA (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
