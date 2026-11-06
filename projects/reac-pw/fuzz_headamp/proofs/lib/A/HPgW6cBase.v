(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v; 642 of its 685 lines of code are new or changed and 90 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW6cEng.v, with its module names changed; 85 of its 135 lines of code are new or changed and 635 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the BLOCK STATEMENTS of the
   walk piece "ent_build C" of LLVMFuzzerTestOneInput (0x80bc0), ent_build's cases 6, 7 and 8 (pod.h:340-366) from
   their switch entries to the join J 0x8237c, and the small facts their proofs share. Proves no function (kind:
   segment lemma).

   ONE STATEMENT PER CASE (w6c_case_stmt c, c = 6, 7, 8): from the case entry (w6c_pc c) with the facts the
   cut hs_cut_D gives there (w6c_ctx, w6c_in_D), the run reaches J in the state lib/A/HPgW6cTail.v's w6c_jpost
   names, with the pod Model.ent_build makes of the kind byte c and the input r after it: these three cases never
   read the kind byte beyond kind % 10, so ent_build (kind :: r) = ent_build (c :: r) (w6c_build_kind).

   THE REGISTERS AT A CASE ENTRY (hs_L_D): s1 = R, s7 = SHADOW_OFF, s8 = cur (the cursor after the kind byte),
   a4 = cur - 1 (the kind byte's address), s9 = |r|; the cells [R+0x18] = 0x15555556 (the `% 12u` multiplier),
   [R+0xd0] = sa (the shadow address the cases reload into s4), [R+0xe0] = F + 0xf8 (e.body), [R+0x110] = F + 0xf0 (e),
   [R+0x118] = |r| + 1 (what was left before the kind byte); e's 104 bytes are zero (the memset 0x817e4) and e's
   granules are in scope (hs_PJ). The two tables the cases read are registered globals of 16 bytes (HPgImgA
   hi_globs): t at 0x210e0 (case 6) and t.9 at 0x21100 (case 8). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6cTail HPgW6cEng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition W6C_D6 : Z := 0x81dc8.
Definition W6C_D7 : Z := 0x81c84.
Definition W6C_D8 : Z := 0x81e18.
Definition w6c_pc (c : Z) : Z := if c =? 6 then W6C_D6 else if c =? 7 then W6C_D7 else W6C_D8.
Definition W6C_T6 : Z := 0x210e0.
Definition W6C_T8 : Z := 0x21100.

(* the pod of one turn whose kind byte reads c *)
Definition w6c_ent (c : Z) (r : list byte) : ent * list byte := ent_build (Z_to_bv 8 c :: r).

(* cases 6, 7 and 8 read the kind byte only through kind % 10 *)
Lemma w6c_build_kind : forall rr kd r, (kd, r) = Cursor.fuzz_u8 rr -> rr <> [] -> In (kd mod 10) [6; 7; 8] ->
ent_build rr = w6c_ent (kd mod 10) r.
Proof.
intros rr kd r Hf Hne Hin. destruct rr as [|b r0]; [contradiction|].
cbn [Cursor.fuzz_u8] in Hf. injection Hf as Hkd Hr. subst r0.
unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8]. rewrite <- Hkd.
cbv [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; rewrite <- E; reflexivity.
Qed.

(* ===================== dropping a region from a symbolic state ===================== *)
Lemma w6c_regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. intros l1 l2. induction l1 as [|r l1 IH]; [reflexivity|]. cbn [app regions_wf]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma w6c_all_disj_drop : forall E a l1 r l2, all_disjoint E a (l1 ++ r :: l2) -> all_disjoint E a (l1 ++ l2).
Proof.
intros E a l1 r l2. induction l1 as [|x l1 IH]; cbn [app all_disjoint]; [intros [_ H]; exact H|].
intros [H1 H2]. split; [exact H1 | exact (IH H2)].
Qed.
Lemma w6c_pw_disj_drop : forall E l1 r l2, pairwise_disjoint E (l1 ++ r :: l2) -> pairwise_disjoint E (l1 ++ l2).
Proof.
intros E l1 r l2. induction l1 as [|x l1 IH]; cbn [app pairwise_disjoint]; [intros [_ H]; exact H|].
intros [H1 H2]. split; [exact (w6c_all_disj_drop E x l1 r l2 H1) | exact (IH H2)].
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma w6c_st_ok_drop : forall E pc rg l1 r l2 resv f ms,
st_ok rsegs E (mkSS pc rg (l1 ++ r :: l2) resv f) ms -> st_ok rsegs E (mkSS pc rg (l1 ++ l2) resv f) ms.
Proof.
intros E pc rg l1 r l2 resv f ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpw) & H9).
repeat (split; [assumption|]). split; [|exact H9]. cbn [ss_mem] in *.
split; [|split].
- rewrite w6c_regions_wf_app in *. cbn [regions_wf] in Hwf.
  apply andb_true_iff in Hwf as [Ha Hb]. apply andb_true_iff in Hb as [_ Hb]. rewrite Ha, Hb. reflexivity.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb; subst. apply Forall_app. split; assumption.
- exact (w6c_pw_disj_drop E l1 r l2 Hpw).
Qed.
End b.

(* ===================== e's bytes from its two header words ===================== *)
Lemma w6c_le32_val : forall v, 0 <= v < 2 ^ 32 -> Z_to_le_bytes 4 v = le32 v.
Proof. reflexivity. Qed.
Lemma w6c_e_hdr : forall H m0 m1 F ty sz,
hm_bytes rsegs H m0 (F + 0xf0) (zeros 104) ->
val_mem rsegs (mrestrict H m1) (F + 0xf0) 4 ty -> val_mem rsegs (mrestrict H m1) (F + 0xf4) 4 sz ->
(forall x, F + 0xf8 <= x < F + 0x158 -> aview rsegs H m1 x = aview rsegs H m0 x) ->
hm_bytes rsegs H m1 (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96).
Proof.
intros H m0 m1 F ty sz Z0 Vt Vs K.
apply hm_bytes_app. split; [exact (hm_bytes_of_val rsegs H m1 (F + 0xf0) 4 ty Vt)|].
rewrite length_le32. apply hm_bytes_app. split.
- replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia. exact (hm_bytes_of_val rsegs H m1 (F + 0xf4) 4 sz Vs).
- rewrite length_le32. replace (F + 0xf0 + Z.of_nat 4 + Z.of_nat 4) with (F + 0xf0 + Z.of_nat 8) by lia.
  apply (hm_bytes_kept rsegs H m0 H m1).
  + replace (zeros 96) with (hm_slice (zeros 104) 8 96) by reflexivity.
    apply (hm_bytes_slice rsegs H m0 (F + 0xf0) (zeros 104) 8 96 Z0). rewrite length_zeros. lia.
  + intros x Hx. rewrite length_zeros in Hx. apply K. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.

(* ===================== the context and the facts at a case entry ===================== *)
Definition w6c_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
w6c_geo STK sp0 own lyc R F pos /\ rom_view rsegs W memc.

Definition w6c_in_D (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F cur sa : Z)
(r : list byte) : Prop :=
(* registers *)
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 23 = w64 SHADOW_OFF /\
getr regs 24 = w64 cur /\ getr regs 14 = w64 (cur - 1) /\ getr regs 25 = w64 (Z.of_nat (length r)) /\
(* the real frame's cells *)
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x18) 8 0x15555556 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 sa /\ 0 <= sa < 2 ^ 64 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xf8) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (Z.of_nat (length r) + 1) /\
(* e and its granules *)
hm_bytes rsegs (w_H W) memc (F + 0xf0) (zeros 104) /\
hd_fsh rsegs (w_H W) memc F hs_PJ /\
(* the input after the kind byte *)
hm_bytes rsegs (w_H W) memc cur r /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) cur (Z.of_nat (length r))) /\
amem_range cur (Z.of_nat (length r)) /\ 1 <= cur /\ cur + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R + 0x160) /\ ~ (F + 0x20 <= a < F + 0x158)) /\
(* the two tables, and the frame apart from them *)
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_T6 16 /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_T8 16 /\
(forall a, W6C_T6 <= a < W6C_T8 + 16 -> ~ (F <= a < F + 1024)).

(* ===================== the three cases, entry -> J ===================== *)
Definition w6c_case_stmt (c : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur sa : Z) (r : list byte),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D W memc regs R F cur sa r ->
SRr rsegs W (cfg_at rsegs (w6c_pc c) regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (fst (w6c_ent c r)) (cur + Z.of_nat (length r - length (snd (w6c_ent c r))))
 (Z.of_nat (length (snd (w6c_ent c r)))) sa).
Definition w6c_case6_stmt : Prop := w6c_case_stmt 6.
Definition w6c_case7_stmt : Prop := w6c_case_stmt 7.
Definition w6c_case8_stmt : Prop := w6c_case_stmt 8.

(* the frame's bytes are present: e's region and the cells' window may be written *)
Lemma w6c_present : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
(forall o, 0 <= o < 1024 -> apresent (w_H W) memc (F + o)) /\
(forall a, R <= a < R + 0x1e0 -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok rsegs B) lyc Sc W memc mdc 4 pos HAR Hin3) as (_ & _ & HFp & _).
rewrite <- HF in HFp. change (fs_frame_bytes 4) with 1024 in HFp.
split; [intros o Ho; exact (proj1 (HFp (F + o) ltac:(lia)))|]. intros a Ha. apply Hpres. unfold T_SEG_STK, ASTACK in *. lia.
Qed.
End d.
End c.
