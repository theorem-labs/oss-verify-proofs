(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: so_not_owned_cf, the donor's so_not_owned (proofs/cgif/cgif_file_fuzzer/lib/A/AD29.v:57)
   with cgif's AR replaced by ARcf at any hidden-head set Hp and cgif's AR_laws by a Theorem Labs lane's AR_laws_cf (used by
   field name), for the asan image. It is alone in this file because its STDOUT_MUT is lib/A/AD1w.v's over lib/A/AD2f.v's
   bounds: lib/A/PresetD1rAx.v (the other frame lemmas) stays free of that closure, and a consumer of this lemma takes
   only PresetD1rAx's closure plus AD1w / AD2f (none of PresetD1rAt.v's AD21 / AD23 / AD25). Statement and argument
   order (B HB ARL ly S Hp W mem md a) are those it had in PresetD1rAx.v. Asan-ubsan twin: lib/AU/PresetD1rBso.v.
   Nothing in this file is a proof of a function (rule 24: the driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK15 YK18 YP0n YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q YK09 YA0e YG0v YG00 YG01 YG0f YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AB1h AB13 AF0m AD2j AD2i AD1t AE22 AD1y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD2h AD1w AD2f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG0ncf YG0dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section so. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.

(* AD29.v:57 *)
Lemma so_not_owned_cf : forall ly S Hp W mem md a, ARcf tfibsegs B ly S Hp W mem md -> STDOUT_MUT a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Ha X.
assert (Hi : in_img tfibsegs a) by (apply in_img_rw; unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
pose proof (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR Hi) X) as Y. rewrite (ts_owned B HB) in Y.
apply Exists_exists in Y as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Tfib_owned_static in Hin. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. cbn in Hin.
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|]). exact Hin.
Qed.
End so.
