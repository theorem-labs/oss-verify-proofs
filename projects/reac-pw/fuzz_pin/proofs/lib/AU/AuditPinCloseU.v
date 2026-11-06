(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/AU closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   AU/YD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: YD2o.ASAN_UBSAN_T_closed, YD2o.knock_asan_ubsan_agrees_closed and YD2o.knock_asan_ubsan_halts_closed
   (the lib/AU/YD2o.v assembly, which closes Statements.asan_ubsan_agrees / asan_ubsan_halts at B := YD2l.TfibB), and
   the allocator closure at that B in lib/AU/YKnockAllocClose.v.
   CONDITIONAL parts, kept for the record: KnockAsanTop's asan_ubsan_*_of_asan_side take ASAN_UBSAN_T as a premise, and
   KnockClose's knock_asan_ubsan_*_of_parts are stated inside Section asan_ubsan over the Hypotheses H_STARTUP_U,
   H_ALLOC_MALLOC_U, H_ALLOC_FREE_U, H_RT_MEMCPY_U, H_TRACES_B_U, H_DRIVER_U, so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   YD2o assembly, not from these conditional parts. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_pin image B (fuzz_pin.asan-ubsan) from
   proofs/libreac/fuzz_knock/lib/AU/AuditKnockCloseU.v at origin/ossv/recipes 88154566652, in the form of this
   library's lib/A/AuditPinClose.v: Print Assumptions of the two closed statements only. On fuzz_pin each print of a
   closed top takes 6 to 7 minutes (image A's audit: ASAN_T_closed 360 s, pin_asan_agrees_closed 410 s,
   pin_asan_halts_closed 358 s), so the file prints the two statements, whose dependency closure holds
   ASAN_UBSAN_T_closed, PinClose's asan_ubsan parts, the allocator closure of lib/AU/YPinAllocClose.v, the binders of
   lib/AU/PinWrapBinders.v, the program contract's proof (lib/AU/PPgLibX.v pin_lib_x_of) and H_DRIVER_U at
   YD2l.TfibB (YD2o.pin_driver_TfibB_U). The conditional parts print in their own files (lib/A/PinAsanTop.v,
   lib/A/PinClose.v). About shows that no Section argument is left on the closed theorems. Names knock_* -> pin_*,
   module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require YD2o PPgLibX.
Check YD2o.pin_asan_ubsan_agrees_closed.
Print Assumptions YD2o.pin_asan_ubsan_agrees_closed.
Check YD2o.pin_asan_ubsan_halts_closed.
Print Assumptions YD2o.pin_asan_ubsan_halts_closed.
About YD2o.ASAN_UBSAN_T_closed.
About YD2o.pin_asan_ubsan_agrees_closed.
About YD2o.pin_asan_ubsan_halts_closed.
About YD2o.pin_driver_TfibB_U.
About PPgLibX.pin_lib_x_of.
Check YD2o.pin_ag_sil_shape_eq_U.
