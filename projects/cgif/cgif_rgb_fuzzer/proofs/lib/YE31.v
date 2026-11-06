(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YI00 YK05 YA0i YA0l YG00 YG01 YG0h YG0u YG0d YB1u YF9j YFa1 YE2z YE3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Open Scope Z_scope.
Definition A_GOT_CANARY : Z := 0xa3f00.
Definition V_GOT_CANARY : Z := 0x5fe250.
Section a.
Section S.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Lemma canary_got_kept : forall ly S W mem md ly' S' W' mem' md' i,
AR trbsegs B ly S W mem md -> AR trbsegs B ly' S' W' mem' md' -> 0 <= i < 8 ->
mbyte trbsegs (mrestrict (w_H W') mem') (A_GOT_CANARY + i) = mbyte trbsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + i).
Proof. first [ exact (YE06.canary_got_kept (imgk := YF00.K_trb)) | exact ((YE06.canary_got_kept (imgk := YF00.K_trb)) B HB) | exact ((YE06.canary_got_kept (imgk := YF00.K_trb)) B) | exact ((YE06.canary_got_kept (imgk := YF00.K_trb)) HB) | exact (YE06.canary_got_kept (imgk := YF00.K_trb)) | solve [ eapply (YE06.canary_got_kept (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE06.canary_got_kept (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Lemma got_canary_of_AR : forall ly S W mem md,
AR trbsegs B ly S W mem md -> val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_CANARY 8 V_GOT_CANARY.
Proof. first [ exact (YE06.got_canary_of_AR (imgk := YF00.K_trb)) | exact ((YE06.got_canary_of_AR (imgk := YF00.K_trb)) B HB) | exact ((YE06.got_canary_of_AR (imgk := YF00.K_trb)) B) | exact ((YE06.got_canary_of_AR (imgk := YF00.K_trb)) HB) | exact (YE06.got_canary_of_AR (imgk := YF00.K_trb)) | solve [ eapply (YE06.got_canary_of_AR (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE06.got_canary_of_AR (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End S.
End a.
