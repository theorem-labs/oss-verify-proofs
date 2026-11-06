(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/A closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   A/AD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: AD2o.ASAN_T_closed, AD2o.knock_asan_agrees_closed and AD2o.knock_asan_halts_closed (h-small-a11's
   lib/A/AD2o.v assembly, which closes Statements.asan_agrees / asan_halts at B := AD2l.TfibB), and the allocator
   closure at that B in lib/A/KnockAllocClose.v (c-libc-fmt).
   CONDITIONAL parts, kept for the record: KnockAsanTop's *_of_asan_side take ASAN_T / ASAN_UBSAN_T as premises, and
   KnockClose's *_of_parts are stated inside Section asan / asan_ubsan over the Hypotheses H_STARTUP, H_ALLOC_MALLOC,
   H_ALLOC_FREE, H_RT_MEMCPY, H_TRACES_B, H_DRIVER (and their _U twins), so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   AD2o assembly, not from these conditional parts. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/AuditKnockClose.v at origin/ossv/recipes 6ebe35ba632;
   taken for reac-pw/fuzz_pin image A: Print Assumptions of the two closed statements only. On fuzz_pin each print of a
   closed top takes 6 to 7 minutes (measured on a build machine: ASAN_T_closed 360 s, pin_asan_agrees_closed 410 s,
   pin_asan_halts_closed 358 s), so the file prints the two statements, whose dependency closure holds ASAN_T_closed,
   PinClose's parts, the allocator closure of lib/A/PinAllocClose.v, the binders of lib/A/PinWrapBinders.v and the
   program contract's proof (AD2o.pin_lib_x_of). The conditional parts print in their own files (lib/A/PinAsanTop.v,
   lib/A/PinClose.v). About shows that no Section argument is left on the closed theorems. Names knock_* -> pin_*,
   module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require AD2o.
Check AD2o.pin_asan_agrees_closed.
Print Assumptions AD2o.pin_asan_agrees_closed.
Check AD2o.pin_asan_halts_closed.
Print Assumptions AD2o.pin_asan_halts_closed.
About AD2o.ASAN_T_closed.
About AD2o.pin_asan_agrees_closed.
About AD2o.pin_asan_halts_closed.
About AD2o.pin_lib_x.
Check AD2o.pin_ag_sil_shape_eq.
