(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the function theorem of fuzz_reply's check_shape_ends (0x853b0),
   pb_check_shape_ends : cshe_spec B MT G A_csheP (W_contract.v Section w3e), composed from the walk's segments:
     held.n = 0                      cshe_n0_x                                (W_check_shape_ends.v)
     held.n > 0, entry and loop 1    cshe_to_tst_x, to the 0x85498 state       (W_check_shape_ends.v)
       g_gone <> 0                   cshe_gone_l2_x, then loop 2: cshe_l2_run_x (W_check_shape_ends.v, W_cshe_l2w.v)
       g_gone = 0, want = 0          cshe_want0_x                             (W_check_shape_ends.v)
       g_gone = 0, want > 0          cshe_gone_l3_x, then loop 3: cshe_l3_top_x (W_check_shape_ends.v, W_cshe_l3.v)
   THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): pb_check_shape_ends_x : cshe_spec_x B PST ARx MT
   G A_csheP over any allocator relation ARx with its laws, in W_check_shape_ends.v's generic Section header plus the
   free rule's caller-context form (CTX_AFREE, one singleton per free site: loop 2's HCTX_cshe_l2, loop 3's
   HCTX_cshe_l3).  THE AR STATEMENT (Section cAR) is re-derived from it at ARx := ARi0, PST := [], its conclusion and
   Section hypotheses byte-identical to the AR walk's but LX0 (the laws at ARi0) in place of LAWS. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_cshe_top.v; 15 of its 102 lines of code are new or changed and 498 lines of the source are left out. *)
(* Satisfiability at the real image A of the R contract texts (W_contract_xR_g6.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_cshe_top.v), so each hypothesis reads as there. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_check_shape_ends W_cshe_l2w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_cshe_l3.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_cshe_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

(* pb_check_shape_ends_xR_sat: cshe_spec_xR at R := wle' SEGS RZ_cf, from W_cshe_top.pb_check_shape_ends_x by cshe_spec_xR_of_x and YA0nH.wle_wle'. The
   Section hypotheses are pb_check_shape_ends_x's own (W_cshe_top.v, Sections a / b / c), unchanged; their comments are left out. *)
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
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HCTX_cshe_l2 : In [BASE + AF_fr_check_shape_ends + 0x16c] CTX_AFREE.
Hypothesis HCTX_cshe_l3 : In [BASE + AF_fr_check_shape_ends + 0x27c] CTX_AFREE.
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis ALDROP : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
Hypothesis PLACEG0 : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Hypothesis PLACEG32 : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
Hypothesis HGR : gx_ok SEGS B cshe_ro.
Hypothesis HGRR : gx_rt B cshe_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Theorem pb_check_shape_ends_xR_sat :
  cshe_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP G A_csheP.
Proof.
apply cshe_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_cshe_top.pb_check_shape_ends_x; eassumption.
Qed.
End sat_pb_check_shape_ends_x.
