(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths changed; 41 of its 74 lines of code are new or changed and 297 lines of the source are left out. *)
(* G4.ExDecl.DeclD5B: a live heap block is visible to the end of the 8-byte word holding its last byte. Copied from
   G6/G5's walk kit (a Theorem Labs lane's lib/A/FMW_kit.v:113-168, block_word_tail_vis with fmw_word_end_le and
   fmw_extent_mod8), under d5k_ names; FMW_ex_decl_d5_kits.v uses it to carry C strings across the program call
   plain (FMW_ex_decl_d5.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the 8-byte word end of a byte below an 8-aligned end stays at or below that end *)
Lemma d5k_word_end_le : forall x base ext, base mod 16 = 0 -> ext mod 8 = 0 -> x < base + ext ->
x - x mod 8 + 8 <= base + ext.
Proof.
intros x base ext H1 H2 H3.
pose proof (Z.div_mod base 16 ltac:(lia)) as D1. pose proof (Z.div_mod ext 8 ltac:(lia)) as D2.
pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
lia.
Qed.

(* a chunk's extent is whole 8-byte words: primary class_size mod 32 = 0, secondary a page multiple less a page (YG0a.v) *)
Lemma d5k_extent_mod8 : forall k, 0 <= ck_req k -> ck_extent k mod 8 = 0.
Proof.
intros k Hq. unfold ck_extent. destruct (from_primary (ck_req k)) eqn:Ep.
- pose proof (primary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & H32 & _).
set (c := class_size (chunk_class (ck_req k))) in *.
pose proof (Z.div_mod c 32 ltac:(lia)) as D. pose proof (Z.div_mod c 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as R8. lia.
- pose proof (secondary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & _ & HP & _).
set (s := sec_map_size (ck_req k)) in *. unfold kPage in *.
pose proof (Z.div_mod s 4096 ltac:(lia)) as D. pose proof (Z.div_mod (s - 4096) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (s - 4096) 8 ltac:(lia)) as R8. lia.
Qed.

(* the block bytes by al_blocks (apresent), the bytes after it by ARm am_junk over the chunk's tail junk range
   (YG0n.v chunk_junk) *)
Lemma d5k_block_word_tail_vis : forall ly S (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  forall a, b <= a < (b + m - 1) - (b + m - 1) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md b m HAR Hin Hm a Ha.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hpres a ltac:(lia))).
- destruct HAR as (M & _).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & Hb16 & Huser & _ & _ & Hreq & Hext & _).
rewrite Hn, Hrq in Hext.
assert (Hcn : ck_n k = m) by (unfold ck_n; rewrite Hn; exact Hrq).
pose proof (d5k_extent_mod8 k ltac:(lia)) as Hx8.
pose proof (d5k_word_end_le (b + m - 1) (ck_base B ly k) (ck_extent k) Hb16 Hx8 ltac:(lia)) as Hend.
pose proof (am_junk B ly S _ M) as HJ. rewrite Forall_forall in HJ.
specialize (HJ (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)).
unfold range_vis in HJ. cbn [fst snd] in HJ.
assert (NSH : forall e', sptr_exp (ck_beg k) <> ASh e') by (intros e'; destruct (ck_beg k); cbn; discriminate).
rewrite (aeval_aoff B ly (sptr_exp (ck_beg k)) (ck_rz k + ck_n k) NSH) in HJ.
assert (Eb : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
replace a with (aeval B ly (sptr_exp (ck_beg k)) + (ck_rz k + ck_n k) + (a - (b + m))) by lia.
apply HJ; [|lia].
unfold ajunk. apply in_cons. apply in_cons.
apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_junk. cbv zeta.
apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_eq.
Qed.
End w.
