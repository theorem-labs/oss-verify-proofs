(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/fast_float/from_chars/lib/MAX/AXF_dec63z.v, with its module paths and module names changed; 100 of its 140 lines of code are new or changed and 4021 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the rewrites from the walks'
   listing terms to SegInstB's image-B terms at image B's instance SegImg.PB_seg (lib/B/Prog/SegImg.v). The twin of
   image A's lib/A/SegInstPB.v (commit 6f7a1561a103): every lemma name is the
   image-A file's; the Require lines take lib/B/Prog's listing and SegInstB; image B adds the entries of strip and fold
   (UBSan outlines them; image A inlines them into m_file). Walks state entries and call targets as listing terms under
   `Context {PI : PAImg seg_listing}` (pa_val A_TEXT + AF_<F>, pa_sigma SS_<x>); the close instantiates PI with
   PB_seg and rewrites by these lemmas. PB_seg's fields: pa_val := seg_val (seg_val A_TEXT = seg_text),
   pa_sigma := SegAddr.seg_sigma.
   proves no function (kind: instantiation lemmas, closed by computation). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegImg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pb_val_text : pa_val (PAImg := PB_seg) A_TEXT = seg_text.
Proof. vm_compute. reflexivity. Qed.
(* the entries: BASE + AF_<F> at PB_seg is A_<F>_A *)
Lemma pb_entry_LLVMFuzzerTestOneInput : pa_val (PAImg := PB_seg) A_TEXT + AF_LLVMFuzzerTestOneInput = A_LLVMFuzzerTestOneInput_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_m_file : pa_val (PAImg := PB_seg) A_TEXT + AF_m_file = A_m_file_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_segments : pa_val (PAImg := PB_seg) A_TEXT + AF_check_segments = A_check_segments_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_role : pa_val (PAImg := PB_seg) A_TEXT + AF_check_role = A_check_role_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_model : pa_val (PAImg := PB_seg) A_TEXT + AF_check_model = A_check_model_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_ignore : pa_val (PAImg := PB_seg) A_TEXT + AF_check_ignore = A_check_ignore_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_provenance : pa_val (PAImg := PB_seg) A_TEXT + AF_check_provenance = A_check_provenance_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_refusals : pa_val (PAImg := PB_seg) A_TEXT + AF_check_refusals = A_check_refusals_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_address : pa_val (PAImg := PB_seg) A_TEXT + AF_check_address = A_check_address_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_knock_refused : pa_val (PAImg := PB_seg) A_TEXT + AF_check_knock_refused = A_check_knock_refused_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_m_find : pa_val (PAImg := PB_seg) A_TEXT + AF_m_find = A_m_find_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_absent : pa_val (PAImg := PB_seg) A_TEXT + AF_check_absent = A_check_absent_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_check_declared : pa_val (PAImg := PB_seg) A_TEXT + AF_check_declared = A_check_declared_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_m_refuse : pa_val (PAImg := PB_seg) A_TEXT + AF_m_refuse = A_m_refuse_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_strip : pa_val (PAImg := PB_seg) A_TEXT + AF_strip = A_strip_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_ieq : pa_val (PAImg := PB_seg) A_TEXT + AF_ieq = A_ieq_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_fold : pa_val (PAImg := PB_seg) A_TEXT + AF_fold = A_fold_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_init : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_init = A_reac_segconf_init_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_parse_file : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_parse_file = A_reac_segconf_parse_file_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_refuse : pa_val (PAImg := PB_seg) A_TEXT + AF_refuse = A_refuse_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_trim : pa_val (PAImg := PB_seg) A_TEXT + AF_trim = A_trim_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_parse : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_parse = A_reac_segconf_parse_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_cross_check : pa_val (PAImg := PB_seg) A_TEXT + AF_cross_check = A_cross_check_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_find : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_find = A_reac_segconf_find_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_ignored : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_ignored = A_reac_segconf_ignored_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_role : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_role = A_reac_segconf_role_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_role_file : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_role_file = A_reac_segconf_role_file_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_ignore_file : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_ignore_file = A_reac_segconf_ignore_file_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_model : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_model = A_reac_segconf_model_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_segconf_declared : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_segconf_declared = A_reac_segconf_declared_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_declared_vlan_split : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_declared_vlan_split = A_reac_declared_vlan_split_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_name_ok : pa_val (PAImg := PB_seg) A_TEXT + AF_name_ok = A_name_ok_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_declared_vlan_add : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_declared_vlan_add = A_reac_declared_vlan_add_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_fuzz_catalogue_row : pa_val (PAImg := PB_seg) A_TEXT + AF_fuzz_catalogue_row = A_fuzz_catalogue_row_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_box_catalogue : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_box_catalogue = A_reac_box_catalogue_A.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_entry_reac_box_catalogue_by_token : pa_val (PAImg := PB_seg) A_TEXT + AF_reac_box_catalogue_by_token = A_reac_box_catalogue_by_token_A.
Proof. vm_compute. reflexivity. Qed.
(* the call targets: pa_sigma SS_<x> at PB_seg is pc_<x>A *)
Lemma pb_pc_memsetA : pa_sigma (PAImg := PB_seg) SS___asan_memset = pc_memsetA.
Proof. reflexivity. Qed.
Lemma pb_pc_memcpyA : pa_sigma (PAImg := PB_seg) SS___asan_memcpy = pc_memcpyA.
Proof. reflexivity. Qed.
Lemma pb_pc_mallocA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_malloc = pc_mallocA.
Proof. reflexivity. Qed.
Lemma pb_pc_callocA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_calloc = pc_callocA.
Proof. reflexivity. Qed.
Lemma pb_pc_memchrA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_memchr = pc_memchrA.
Proof. reflexivity. Qed.
Lemma pb_pc_snprintfA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_snprintf = pc_snprintfA.
Proof. reflexivity. Qed.
Lemma pb_pc_freeA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_free = pc_freeA.
Proof. reflexivity. Qed.
Lemma pb_pc_strlenA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strlen = pc_strlenA.
Proof. reflexivity. Qed.
Lemma pb_pc_strrchrA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strrchr = pc_strrchrA.
Proof. reflexivity. Qed.
Lemma pb_pc_strcmpA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strcmp = pc_strcmpA.
Proof. reflexivity. Qed.
Lemma pb_pc_strchrA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strchr = pc_strchrA.
Proof. reflexivity. Qed.
Lemma pb_pc_bcmpA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_bcmp = pc_bcmpA.
Proof. reflexivity. Qed.
Lemma pb_pc_strncmpA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strncmp = pc_strncmpA.
Proof. reflexivity. Qed.
Lemma pb_pc_strstrA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strstr = pc_strstrA.
Proof. reflexivity. Qed.
Lemma pb_pc_strspnA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strspn = pc_strspnA.
Proof. reflexivity. Qed.
Lemma pb_pc_strncasecmpA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strncasecmp = pc_strncasecmpA.
Proof. reflexivity. Qed.
Lemma pb_pc_strcasecmpA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strcasecmp = pc_strcasecmpA.
Proof. reflexivity. Qed.
Lemma pb_pc_vsnprintfA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_vsnprintf = pc_vsnprintfA.
Proof. reflexivity. Qed.
Lemma pb_pc_strtolA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strtol = pc_strtolA.
Proof. reflexivity. Qed.
Lemma pb_pc_strncpyA : pa_sigma (PAImg := PB_seg) SS___interceptor_trampoline_strncpy = pc_strncpyA.
Proof. reflexivity. Qed.
Lemma pb_pc_stack_malloc_0A : pa_sigma (PAImg := PB_seg) SS___asan_stack_malloc_0 = pc_stack_malloc_0A.
Proof. reflexivity. Qed.
Lemma pb_pc_stack_malloc_1A : pa_sigma (PAImg := PB_seg) SS___asan_stack_malloc_1 = pc_stack_malloc_1A.
Proof. reflexivity. Qed.
Lemma pb_pc_stack_malloc_3A : pa_sigma (PAImg := PB_seg) SS___asan_stack_malloc_3 = pc_stack_malloc_3A.
Proof. reflexivity. Qed.
Lemma pb_pc_stack_malloc_5A : pa_sigma (PAImg := PB_seg) SS___asan_stack_malloc_5 = pc_stack_malloc_5A.
Proof. reflexivity. Qed.
Lemma pb_pc_stack_free_5A : pa_sigma (PAImg := PB_seg) SS___asan_stack_free_5 = pc_stack_free_5A.
Proof. reflexivity. Qed.
Lemma pb_pc_isalnumA : pa_sigma (PAImg := PB_seg) SS_isalnum = pc_isalnumA.
Proof. reflexivity. Qed.
Lemma pb_pc_set_shadow_00A : pa_sigma (PAImg := PB_seg) SS___asan_set_shadow_00 = pc_set_shadow_00A.
Proof. reflexivity. Qed.
Lemma pb_pc_set_shadow_f5A : pa_sigma (PAImg := PB_seg) SS___asan_set_shadow_f5 = pc_set_shadow_f5A.
Proof. reflexivity. Qed.
Lemma pb_pc_set_shadow_f8A : pa_sigma (PAImg := PB_seg) SS___asan_set_shadow_f8 = pc_set_shadow_f8A.
Proof. reflexivity. Qed.
End b.
