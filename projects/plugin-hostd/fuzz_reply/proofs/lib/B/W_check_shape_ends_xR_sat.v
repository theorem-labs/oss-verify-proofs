(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the composition of the image-B (fuzz_reply.asan-ubsan) walk of check_shape_ends, after
   lib/A/W_check_shape_ends.v (a working branch), a NEW walk over lib/B/W_listing.v.  The pieces meet at the interface
   predicates of lib/B/W_cshe_epi.v: the head (lib/B/W_cshe_hd.v) ends in cshe_out_B, cshe_l2_in or cshe_l3_in; loop 2
   (lib/B/W_cshe_l2.v) and loop 3 (lib/B/W_cshe_l3.v) take cshe_l2_in / cshe_l3_in to cshe_out_B; this file takes
   cshe_out_B through the epilogue 0x8592c (cshe_epi_m_B) to whatever the caller's post asks of the run, which is the
   form the kit's cshe_post has. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_check_shape_ends.v; 15 of its 85 lines of code are new or changed and 265 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_contract_xR_g6.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_check_shape_ends.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin W_cshe_epi.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_cshe_hd W_cshe_l2 W_cshe_l3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_check_shape_ends_xR_sat: cshe_spec_xR at R := wle' SEGS RZ_cf, from W_check_shape_ends.pb_check_shape_ends_x by cshe_spec_xR_of_x and YA0nH.wle_wle'. The
   Section hypotheses are pb_check_shape_ends_x's own (W_check_shape_ends.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat_pb_check_shape_ends_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis ML : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis LDROP : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_x B PST ARx MT RP G' (BASE + AF_fr_list_drop).
Hypothesis HP : hp_spec_x B PST ARx (BASE + AF_fr_has_prefix).
Hypothesis HGR : gx_ok SEGS B cshe_ro_B.
Hypothesis HGRR : gx_rt B cshe_ro_B.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Theorem pb_check_shape_ends_xR_sat :
  cshe_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP G A_csheBP.
Proof.
apply cshe_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_check_shape_ends.pb_check_shape_ends_x; eassumption.
Qed.
End sat_pb_check_shape_ends_x.
