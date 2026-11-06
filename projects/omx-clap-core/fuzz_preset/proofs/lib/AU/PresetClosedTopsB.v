(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan): the CLOSED TOPS of the asan-ubsan image, from the B' driver's one
   composition of its discharges (lib/AU/Prog/Ent102DrvTopB3.v TFIB_T_room_all_B_walked3, the room form at
   PAYLOAD_ROOM := fun _ => True) and from walked3 (Ent102DrvTopB3.TFIB_T_closed_B_walked3), which that file derives
   from it.
   preset_asan_ubsan_agrees_closed: lib/AU/AsanUbsanTop.v preset_asan_ubsan_agrees_of_tfib, whose one hypothesis is
   lib/AU/PresetTFIBAU.v TFIB_T_AU, applied to walked3. walked3's statement PresetD2pB.TFIB_T_closed_B is defined as
   PresetTFIBAU.TFIB_T_AU (lib/AU/PresetD2pB.v), so the two meet by conversion (fit_TFIB_T_closed_B below).
   preset_asan_ubsan_halts_closed: lib/AU/HaltsTop.v preset_asan_ubsan_halts_of_tfib, whose one hypothesis is
   lib/AU/HaltsTFIB.v TFIB_T_AU_H, applied to TFIB_T_halts_B_closed below. (lib/AU/HaltsClosedB.v has a theorem of the
   same short name; it keeps Section hypotheses and does not rest on walked3.)
   rule 24: no function proved (kind: composition by citation). *)
From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Ent102DrvTopB3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetTFIBAU PresetD2pB AsanUbsanTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require HaltsTFIB HaltsTop.

(* the fit: walked3's statement is the agreement top's hypothesis, by conversion *)
Example fit_TFIB_T_closed_B : PresetD2pB.TFIB_T_closed_B = PresetTFIBAU.TFIB_T_AU := eq_refl.

Theorem preset_asan_ubsan_agrees_closed : OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_ubsan_agrees.
Proof. exact (AsanUbsanTop.preset_asan_ubsan_agrees_of_tfib Ent102DrvTopB3.TFIB_T_closed_B_walked3). Qed.

(* The halts top composes from the ROOM form, not from walked3. walked3's statement (PresetTFIBAU.TFIB_T_AU) has one
   more binder, the plain entry en_p, and one more premise, that the plain run from en_p is never refused at the
   agreement's budget. The halts statement has no plain run and grants no such premise, so walked3 does not give
   HaltsTFIB.TFIB_T_AU_H. The room form at PAYLOAD_ROOM := fun _ => True has neither: its room premise is I here.
   HaltsTFIB.TFIB_T_AU_H_of_specx gives the exit shape from presetAU_SPECX_shape_ok (every exit 0 or 2). *)
Lemma TFIB_T_halts_B_closed : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.HaltsTFIB.TFIB_T_AU_H.
Proof.
apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.HaltsTFIB.TFIB_T_AU_H_of_specx.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
exact (Ent102DrvTopB3.TFIB_T_room_all_B_walked3 sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp (fun _ _ _ _ _ => I)).
Qed.

Theorem preset_asan_ubsan_halts_closed : OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_ubsan_halts.
Proof. exact (HaltsTop.preset_asan_ubsan_halts_of_tfib TFIB_T_halts_B_closed). Qed.

Print Assumptions preset_asan_ubsan_agrees_closed.
Print Assumptions preset_asan_ubsan_halts_closed.
