(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 85 of its 105 lines of code are new or changed and 498 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), the segment S_MF_HDRB: the MODEL step of each of
   its four paths, and what the tail's mf_loop needs from the model at the end of the segment. A walk lane of
   the image-B m_file-family owner's G2B. No instruction is executed here and no reader is read: every lemma is about SegModel's mconf,
   m_file_m.v's mh_find / mf_fin / mf_loop and mf_hdrb_2.v's hb_mod.
   ADAPTED from image A's lib/A/Prog/m_file_s_hdrb_4.v (commit d8beabc2758c): its lemmas word
   for word, plus hb4_mod_head, hb4_mod_cur and hb4_mod_grow, which image B needs because its join stores the
   cursor itself (0x86bb4): the cut points before the join carry the head's cursor cur0 with hb_mod of the current
   model.

   THE FOUR PATHS (the image-B m_file cut map section 4 "S_MF_HDRB"; the model's cases are the hb_mh_find_ lemmas of
   mf_hdrb_1.v):
     found, the entry's gen is not the file's (0x86608 `bne` taken): the model is kept and the join writes the
       gen -> m_upd mcc i (ms_with_gen (mc_gen mcc));
     found, the gens are equal: m_refuse(c, line + 1) first (0x86614), then the same join;
     not found and c->n = 32 (0x86b1c `blt` not taken): overflow + 1 (0x86b3c), m_refuse (0x86b48), cur = NULL;
     not found and c->n < 32: a new entry (0x86b60 n + 1, 0x86b88 memset, 0x86b98 memcpy) and the same join.
   In each case the model grows (no entry and no kept refusal is dropped), the cursor names an entry of the model
   the block ends with, refused goes up by at most one and overflow by at most one: that is hb_mod, and it is what
   m_file_m.v's mf_loop asks at the tail, where the text left is at least one byte shorter (hb4_tail_model). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m m_file_mdl mf_hdrb_1 mf_hdrb_2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== hb_mod at each path's end ============================== *)
(* nothing happened to the model: the cursor of the found entry, the kept refusals and the counters are the
   head's (the found path with g->gen <> c->gen) *)
Lemma hb4_mod_keep : forall k0 mcc i, (i < length (mc_seg mcc))%nat -> (k0 <= length (mc_kept mcc))%nat ->
  hb_mod k0 mcc mcc (Some i).
Proof. intros k0 mcc i Hi Hk. unfold hb_mod, mf_cur_ok. repeat split; try exact Hi; try exact Hk; lia. Qed.

(* one m_refuse: seg is kept, kept grows by at most one, refused by at most one, overflow not at all *)
Lemma hb4_mod_refuse : forall k0 mc0 mcc cur l b, hb_mod k0 mc0 mcc cur ->
  mc_refused mcc = mc_refused mc0 -> hb_mod k0 mc0 (m_refuse mcc l b) cur.
Proof.
  intros k0 mc0 mcc cur l b (HC & HK & HR & HO) HE.
  destruct (m_refuse_sizes mcc l b) as (Eseg & Hk1 & Hk2).
  destruct (hb_refuse_fields mcc l b) as (_ & Eov & Href & _ & _).
  unfold hb_mod, mf_cur_ok in *. destruct cur as [i|].
  - rewrite Eseg. repeat split; try exact I; try exact HC; lia.
  - repeat split; try exact I; lia.
Qed.

(* the overflow path: overflow + 1 and then one m_refuse, with no cursor *)
Lemma hb4_mod_overflow : forall k0 mcc l, (k0 <= length (mc_kept mcc))%nat ->
  hb_mod k0 mcc (m_refuse (mc_set_overflow (mc_overflow mcc + 1) mcc) l false) None.
Proof.
  intros k0 mcc l Hk.
  destruct (m_refuse_sizes (mc_set_overflow (mc_overflow mcc + 1) mcc) l false) as (_ & Hk1 & _).
  destruct (hb_refuse_fields (mc_set_overflow (mc_overflow mcc + 1) mcc) l false) as (_ & Eov & Href & _ & _).
  unfold mc_set_overflow in *. cbn [mc_kept mc_refused mc_overflow] in *.
  unfold hb_mod, mf_cur_ok. repeat split; try exact I; lia.
Qed.

(* the new entry: one more entry, nothing else *)
Lemma hb4_mod_append : forall k0 mcc g, (k0 <= length (mc_kept mcc))%nat ->
  hb_mod k0 mcc (m_set_segs mcc (mc_seg mcc ++ [g])) (Some (length (mc_seg mcc))).
Proof.
  intros k0 mcc g Hk. unfold hb_mod, mf_cur_ok, m_set_segs. cbn [mc_seg mc_kept mc_refused mc_overflow].
  rewrite length_app. cbn [length]. repeat split; lia.
Qed.

(* the join's store of the gen: it edits one entry, so no size and no counter moves *)
Lemma hb4_mod_upd : forall k0 mc0 mcc i f, hb_mod k0 mc0 mcc (Some i) -> hb_mod k0 mc0 (m_upd mcc i f) (Some i).
Proof.
  intros k0 mc0 mcc i f (HC & HK & HR & HO). unfold hb_mod, mf_cur_ok, m_upd, m_set_segs in *.
  cbn [mc_seg mc_kept mc_refused mc_overflow] in *. rewrite upd_nth_length. repeat split; assumption.
Qed.

(* the head: the cursor of the head names an entry of the model the block holds and n_kept has not gone below the
   call's (mf_loop's mf_cur_ok and n_kept fact), nothing moved yet *)
Lemma hb4_mod_head_of : forall k0 mc0 cur0, mf_cur_ok mc0 cur0 -> (k0 <= length (mc_kept mc0))%nat ->
  hb_mod k0 mc0 mc0 cur0.
Proof. intros k0 mc0 cur0 HC HK. unfold hb_mod. repeat split; try exact HC; try exact HK; lia. Qed.

(* another cursor that names an entry of the same model *)
Lemma hb4_mod_cur : forall k0 mc0 mcc cur cur', hb_mod k0 mc0 mcc cur -> mf_cur_ok mcc cur' -> hb_mod k0 mc0 mcc cur'.
Proof. intros k0 mc0 mcc cur cur' (_ & HK & HR & HO) HC. unfold hb_mod. repeat split; assumption. Qed.

(* one more entry appended: the old cursor still names an entry, nothing else moves *)
Lemma hb4_mod_grow : forall k0 mc0 mcc cur g, hb_mod k0 mc0 mcc cur ->
  hb_mod k0 mc0 (m_set_segs mcc (mc_seg mcc ++ [g])) cur.
Proof.
  intros k0 mc0 mcc cur g (HC & HK & HR & HO). unfold hb_mod, mf_cur_ok, m_set_segs in *.
  cbn [mc_seg mc_kept mc_refused mc_overflow] in *.
  destruct cur as [i|]; [rewrite length_app; cbn [length]; repeat split; lia | repeat split; assumption].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ======================= what the tail needs of the model at the next line =======================
   mf_loop's model half at (the model the segment ends with, the line after this one, the text after this line).
   The counters' room is where the +1 of a refusal is absorbed: the text left is at least one byte shorter. *)
Lemma hb4_tail_model : forall v Wc memc mc0 mcc cur0 cur line p rest,
  mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur -> rest <> [] ->
  mf_cur_ok mcc cur /\ (mv_k0 v <= length (mc_kept mcc))%nat /\
  0 <= line + 1 /\ (line + 1) + Z.of_nat (length (mf_rest rest)) <= 65535 /\
  mc_refused mcc + Z.of_nat (length (mf_rest rest)) < 2 ^ 32 /\
  mc_overflow mcc + Z.of_nat (length (mf_rest rest)) < 2 ^ 32.
Proof.
  intros v Wc memc mc0 mcc cur0 cur line p rest HL HM HNE.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & Hl0 & Hl1 & Hrf & Hov).
  destruct HM as (HC & HK & HR & HO).
  pose proof (hb_mf_rest_lt rest HNE) as Hlt.
  repeat split; try assumption; lia.
Qed.

(* the head's model fact at the tail: mf_fin IS the tail's `fst (m_lines ...)` (m_file_m.v:125) *)
Lemma hb4_fin_unfold : forall st line rest,
  mf_fin st line rest = fst (m_lines st (line + 1) (lines (mf_rest rest))).
Proof. intros st line rest. reflexivity. Qed.

Section e.
Variable B : asyms.

(* the cursor of the head names an entry of the model the block holds (mf_loop's mf_cur_ok), and n_kept has not
   gone below the call's: the two facts every hb_mod of this segment starts from *)
Lemma hb4_head_mod : forall v Wc memc mcc cur line p rest,
  mf_loop v Wc memc mcc cur line p rest -> mf_cur_ok mcc cur /\ (mv_k0 v <= length (mc_kept mcc))%nat.
Proof.
  intros v Wc memc mcc cur line p rest (_ & _ & _ & _ & _ & HC & HK & _). exact (conj HC HK).
Qed.

End e.
End f.
End d.
