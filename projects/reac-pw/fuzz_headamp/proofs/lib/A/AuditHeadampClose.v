(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/A closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   A/AD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: AD2o.ASAN_T_closed, AD2o.knock_asan_agrees_closed and AD2o.knock_asan_halts_closed (the
   lib/A/AD2o.v assembly, which closes Statements.asan_agrees / asan_halts at B := AD2l.TfibB), and the allocator
   closure at that B in lib/A/KnockAllocClose.v.
   CONDITIONAL parts, kept for the record: KnockAsanTop's *_of_asan_side take ASAN_T / ASAN_UBSAN_T as premises, and
   KnockClose's *_of_parts are stated inside Section asan / asan_ubsan over the Hypotheses H_STARTUP, H_ALLOC_MALLOC,
   H_ALLOC_FREE, H_RT_MEMCPY, H_TRACES_B, H_DRIVER (and their _U twins), so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   AD2o assembly, not from these conditional parts. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/AuditKnockClose.v
   at origin/ossv/recipes 6ebe35ba632: the same pairs for qdisc's AD2o, QdiscAllocClose, QdiscAsanTop and QdiscClose;
   qdisc's allocator closure is the one-trace text of fuzz_identity (no AD3j); names knock_* -> qdisc_*, module paths
   changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/AuditQdiscClose.v at 56ce9edaafc, for reac-pw/fuzz_role
   image A: the same pairs for role's AD2o, RoleAllocClose, RoleAsanTop and RoleClose, with `About` for each top (it
   lists the leading arguments: AD2o's open Section Variables role_lib_x_all and role_plain_slot_ag while their files
   have not landed, RoleAsanTop.PLAIN_SLOT_AG for the agreement statements, RoleClose's Section parts); names
   qdisc_* -> role_*, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/AuditRoleClose.v at fa745625e7d, for reac-pw/fuzz_headamp
   image A: the same pairs for headamp's AD2o, HeadampAllocClose, HeadampAsanTop and HeadampClose, and for the plain
   slot lib/A/HeadampPlainSlot.v headamp_plain_slot_ag_closed (AD2o's tops take no argument: image A's program
   contract is lib/A/HPgTopI.v headamp_lib_x_all); names role_* -> headamp_*, module paths changed. Every Print Assumptions over a top that
   uses the relocated frame walks the whole frame (measured with Time on the build VM while the program contract was
   still a premise: ASAN_T_closed 402 s, the agrees top 472 s, the halts top 377 s, the malloc / free / memcpy lemmas
   98 / 253 / 9 s; the plain slot 79 s; the conditional tops 1-53 s each), so with all of them this file took
   1939-2378 s; with the closed tops and one frame-wide Print Assumptions it takes 864 s. It now prints the halts top, the
   plain slot and the conditional tops; the agrees top's Print Assumptions is lib/A/AuditHeadampCloseAgrees.v; the
   closures of AD2o.ASAN_T_closed and of the three allocator lemmas lie inside the halts top's (headamp_asan_halts_closed
   applies ASAN_T_closed, which applies the three), so they keep their About / Check lines only.
   The T0.6 witness files of image A and of the plain side image A's statements read are Required here, so that they
   are in the closure of an audit file: lib/A/HPgM3aSat.v (ERRNO_RW at image A's errno cell), lib/Pod/Sat.v,
   lib/Pod/HeadampSat.v, lib/Pod/HeadampBin.v (the Pod model's witnesses; the model is the plain side of both images'
   agreement and the content of their walks' posts) and lib/Prog/SlotInvSat.v (the plain frame's slot invariant at
   its entry, read by the plain slot of the agreement statements); with Print Assumptions of image A's errno witness
   and of the slot invariant's two theorems. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require AD2o HeadampAllocClose HeadampAsanTop HeadampClose
  HeadampPlainSlot HPgM3aSat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Sat HeadampSat HeadampBin.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require SlotInvSat.
About AD2o.ASAN_T_closed.
About AD2o.headamp_asan_agrees_closed.
About AD2o.headamp_asan_halts_closed.
Print Assumptions AD2o.headamp_asan_halts_closed.
Check HeadampAllocClose.headamp_amalloc_closed.
Check HeadampAllocClose.headamp_afree_closed.
Check HeadampAllocClose.headamp_aicpy_closed.
About HeadampPlainSlot.headamp_plain_slot_ag_closed.
Print Assumptions HeadampPlainSlot.headamp_plain_slot_ag_closed.
About HeadampAsanTop.asan_agrees_of_asan_side.
Print Assumptions HeadampAsanTop.asan_agrees_of_asan_side.
About HeadampAsanTop.asan_halts_of_asan_side.
Print Assumptions HeadampAsanTop.asan_halts_of_asan_side.
About HeadampAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions HeadampAsanTop.asan_ubsan_agrees_of_asan_side.
About HeadampAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions HeadampAsanTop.asan_ubsan_halts_of_asan_side.
About HeadampClose.ASAN_T_of_parts.
Print Assumptions HeadampClose.ASAN_T_of_parts.
About HeadampClose.ASAN_UBSAN_T_of_parts.
Print Assumptions HeadampClose.ASAN_UBSAN_T_of_parts.
About HeadampClose.headamp_asan_agrees_of_parts.
Print Assumptions HeadampClose.headamp_asan_agrees_of_parts.
About HeadampClose.headamp_asan_halts_of_parts.
Print Assumptions HeadampClose.headamp_asan_halts_of_parts.
About HeadampClose.headamp_asan_ubsan_agrees_of_parts.
Print Assumptions HeadampClose.headamp_asan_ubsan_agrees_of_parts.
About HeadampClose.headamp_asan_ubsan_halts_of_parts.
Print Assumptions HeadampClose.headamp_asan_ubsan_halts_of_parts.
Print Assumptions HPgM3aSat.hq_errno_rw_A.
Print Assumptions HPgM3aSat.hq_errno_rw_of.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.SlotInvSat.slotinv_entry_sat.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.SlotInvSat.slotinv_four_block_room.
