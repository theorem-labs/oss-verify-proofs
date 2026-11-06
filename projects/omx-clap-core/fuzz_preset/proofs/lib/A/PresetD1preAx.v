(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset (asan image), the driver's interceptor SITE
   results over the second allocator instance ARcf, made from the core's lib/A (relocated from
   proofs/cgif/cgif_file_fuzzer/lib/A): AD1k.v:273 tfib_fwrite_site, :314 tfib_refused_site and AD1l.v:147 / :152 /
   :157 tfib_fprintf_{open,rderr,usage}_site, over this lane's site forms (lib/A/PresetD1preA.v).
   Changes from the donor: the sites are over ARcf at Hp = []; the stderr state est is a parameter, with the one fact
   of it each proof uses (the donor's AD1k.v:103 est_written for the fwrite site, :105 est_after_vf for the fprintf
   sites), so that this file does not import AD1k.v; the driver lane instantiates est := AD1k.est with those two
   lemmas. The proofs (PresetD1preAxPf.v) use the ARcf copies of the interceptor walks (AE2x / AE2t / AE2u / AE2v /
   AE2w and their closure, copied mechanically to <name>cf.v), not premises.
   Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20
AD1v AD2h AD2f AD1w AD1x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AE2p AE3h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1preA.
Import ListNotations.
Local Open Scope Z_scope.

(* AD1k.v:273 tfib_fwrite_site. *)
Definition tfib_fwrite_site_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, AE2p.stderr_written (mrestrict H m) -> est H m) ->
fwrite_site_tfa_cf B est.

(* AD1k.v:314 tfib_refused_site. *)
Definition tfib_refused_site_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
refused_site_tfa_cf B est.

(* AD1l.v:147 tfib_fprintf_open_site. *)
Definition tfib_fprintf_open_site_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est 0x1d845 (strB "cli: cannot open "%string) nlB.

(* AD1l.v:152 tfib_fprintf_rderr_site. *)
Definition tfib_fprintf_rderr_site_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est 0x1d85a (strB "cli: read error on "%string) nlB.

(* AD1l.v:157 tfib_fprintf_usage_site. *)
Definition tfib_fprintf_usage_site_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms)
(est : (word -> bool) -> (word -> option byte) -> Prop),
TfibSyms B ->
(forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est 0x158b3 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
