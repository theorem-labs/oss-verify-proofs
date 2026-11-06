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
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/AU/AuditKnockCloseU.v at origin/ossv/recipes
   2d2ff01bb6f, for reac-pw/fuzz_headamp image B: the same pairs for headamp's lib/AU/YD2o.v, YHeadampAllocClose.v,
   HeadampAsanTop's asan_ubsan tops, HeadampClose's asan_ubsan Section (ASAN_UBSAN_T_of_parts too) and the shared plain
   slot lib/A/HeadampPlainSlot.v, with `About` for each top (YD2o's tops take no argument: image B's program contract
   is lib/AU/HPgTopI.v headamp_lib_x_all); names knock_* -> headamp_*, module paths changed. Every Print
   Assumptions over a top that uses the frame walks the whole frame (image A's, measured with Time: 377-472 s per
   statement top), and with both statement tops this file took 1097 s; it now prints the halts top, the plain slot and
   the conditional tops, and the agrees top's Print Assumptions is lib/AU/AuditHeadampCloseUAgrees.v. The closures of
   YD2o.ASAN_UBSAN_T_closed and of the three allocator lemmas lie inside the halts top's, so they keep About / Check.
   The T0.6 witness files of image B are Required here, so that they are in the closure of an audit file:
   lib/AU/HPgBM3aSat.v (ERRNO_RW at image B's errno cell), lib/AU/HPgParseSat.v (the parse's errno premises on image
   B's segments), lib/AU/HPgSatU.v and lib/AU/HPgSatSegU.v (image B's witness of the segment contracts' image-level
   premises) and lib/AU/HPgSegSat.v (lib/AU/HPgSeg.v's witness at headamp_himg_B / headamp_bld_B), with Print
   Assumptions of lemmas that each of them prints itself. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YD2o YHeadampAllocClose HPgBM3aSat HPgParseSat HPgSatU
  HPgSatSegU HPgSegSat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HeadampAsanTop HeadampClose HeadampPlainSlot.
About YD2o.ASAN_UBSAN_T_closed.
About YD2o.headamp_asan_ubsan_agrees_closed.
About YD2o.headamp_asan_ubsan_halts_closed.
Print Assumptions YD2o.headamp_asan_ubsan_halts_closed.
Check YHeadampAllocClose.headamp_amalloc_closed_U.
Check YHeadampAllocClose.headamp_afree_closed_U.
Check YHeadampAllocClose.headamp_aicpy_closed_U.
About HeadampPlainSlot.headamp_plain_slot_ag_closed.
Print Assumptions HeadampPlainSlot.headamp_plain_slot_ag_closed.
About HeadampAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions HeadampAsanTop.asan_ubsan_agrees_of_asan_side.
About HeadampAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions HeadampAsanTop.asan_ubsan_halts_of_asan_side.
About HeadampClose.ASAN_UBSAN_T_of_parts.
Print Assumptions HeadampClose.ASAN_UBSAN_T_of_parts.
About HeadampClose.headamp_asan_ubsan_agrees_of_parts.
Print Assumptions HeadampClose.headamp_asan_ubsan_agrees_of_parts.
About HeadampClose.headamp_asan_ubsan_halts_of_parts.
Print Assumptions HeadampClose.headamp_asan_ubsan_halts_of_parts.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgBM3aSat.hqu_errno_rw_B.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgBM3aSat.hqu_errno_rw_of.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgParseSat.pb_errno_img.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSatU.hd_entries_B.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSatU.hd_sat_parse_strs_B.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSatSegU.headamp_seg_static_B_shB.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSatSegU.headamp_seg_shB_B.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSegSat.headamp_bld_B_sat.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSegSat.headamp_bld_B_w1.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSegSat.headamp_bld_B_w1_covers.
Print Assumptions OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgSegSat.hsu_pod_offsets.
