(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan): the CLOSED TOPS of the asan image, from the A' driver's one composition
   of its discharges (lib/A/Prog/Ent102DrvTopA3.v TFIB_T_room_all_A_walked3, the room form at
   PAYLOAD_ROOM := fun _ => True) and from walked3 (Ent102DrvTopA3.TFIB_T_closed_A_walked3), which that file derives
   from it.
   preset_asan_agrees_closed: lib/A/AsanAgreesTop.v preset_asan_agrees_of_tfib, whose one hypothesis is
   lib/A/PresetTFIB.v TFIB_T, applied to walked3. walked3's statement PresetD2pA.TFIB_T_closed_A is defined as
   PresetTFIB.TFIB_T (lib/A/PresetD2pA.v), so the two meet by conversion (fit_TFIB_T_closed_A below).
   preset_asan_halts_closed: lib/A/AsanTop.v preset_asan_halts_of_tfib, whose one hypothesis is lib/A/HaltsTFIB.v
   TFIB_T, applied to TFIB_T_halts_A_closed below.
   rule 24: no function proved (kind: composition by citation). *)
From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102DrvTopA3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetTFIB PresetD2pA AsanAgreesTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require HaltsTFIB AsanTop.

(* the fit: walked3's statement is the agreement top's hypothesis, by conversion *)
Example fit_TFIB_T_closed_A : PresetD2pA.TFIB_T_closed_A = PresetTFIB.TFIB_T := eq_refl.

Theorem preset_asan_agrees_closed : OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_agrees.
Proof. exact (AsanAgreesTop.preset_asan_agrees_of_tfib Ent102DrvTopA3.TFIB_T_closed_A_walked3). Qed.

(* The halts top composes from the ROOM form, not from walked3. walked3's statement (PresetTFIB.TFIB_T) has one more
   binder, the plain entry en_p, and one more premise, that the plain run from en_p is never refused at the agreement's
   budget. The halts statement has no plain run and grants no such premise, so walked3 does not give HaltsTFIB.TFIB_T.
   The room form at PAYLOAD_ROOM := fun _ => True has neither: its room premise is I here. HaltsTFIB.TFIB_T_of_specx
   gives the exit shape from preset_SPECX_shape_ok (every exit 0 or 2). *)
Lemma TFIB_T_halts_A_closed : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.HaltsTFIB.TFIB_T.
Proof.
apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.HaltsTFIB.TFIB_T_of_specx.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
exact (Ent102DrvTopA3.TFIB_T_room_all_A_walked3 sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp (fun _ _ _ _ _ => I)).
Qed.

Theorem preset_asan_halts_closed : OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_halts.
Proof. exact (AsanTop.preset_asan_halts_of_tfib TFIB_T_halts_A_closed). Qed.

Print Assumptions preset_asan_agrees_closed.
Print Assumptions preset_asan_halts_closed.
