(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj3 ACj1 ACgw ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition af_lcDDn (na : nat) : list YP09.chunk :=
[YP09.mkChunk 104 (CVal 8 (SOff 32 92)); YP09.mkChunk 112 (CVal 8 (shq 32 92)); YP09.mkChunk 56 (CVal 8 (SOff 67 0));
YP09.mkChunk 8 (CVal 8 (shq 46 0)); YP09.mkChunk 16 (CVal 8 (shq na 0)); YP09.mkChunk 24 (CVal 8 (shq 46 26));
YP09.mkChunk 32 (CVal 8 (shq 32 50)); YP09.mkChunk 40 (CVal 8 (shq 32 48)); YP09.mkChunk 48 (CVal 8 (SOff 32 48));
YP09.mkChunk 64 (CVal 8 (shq 46 8)); YP09.mkChunk 72 (CVal 8 (SOff 46 26)); YP09.mkChunk 80 (CVal 8 (SOff na 8));
YP09.mkChunk 88 (CVal 8 (shq na 8)); YP09.mkChunk 96 (CVal 8 (SOff 46 8))].
Definition af_lcDD : list YP09.chunk := Eval cbv [af_lcDDn] in af_lcDDn 23.
Ltac af_locsD_tac HR0 Xsp X32 X38 X46 X67 Xnw HZg Hgceil Hcfp Hn0 Hnc C1 Ra4 :=
lazymatch goal with |- af_locsD _ ?sp0 ?g ?cfp ?a4v ?nw =>
unfold af_locsD;
lazymatch type of HR0 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let shcell b o bv Xb :=
(split; [ apply (denot_shx Ex b 38 o bv SB Xb X38); clear - HZg Hgceil Hcfp Hn0 Hnc C1; unfold SB; lia
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); let Hd := fresh "Hd" in
assert (Hd : 0 <= (bv + o) / 8 < 2 ^ 61) by (clear - HZg Hgceil Hcfp Hn0 Hnc C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
clear - Hd C1; unfold SB; lia ]) in
let ptr b o bv Xb :=
(split; [ cbn [sv_denot]; rewrite Xb, unsigned_lit_small by (clear - HZg Hgceil Hcfp Hn0 Hnc C1; lia); reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HZg Hgceil Hcfp Hn0 Hnc C1; lia ]) in
let one od :=
lazymatch cs with context [YP09.mkChunk od (CVal 8 ?e)] =>
lazymatch goal with |- val_mem _ _ _ _ ?v =>
let Hdr := fresh "Hdr" in
assert (Hdr : sv_denot Ex e = Z_to_bv 64 v /\ 0 <= v < 2 ^ (8 * Z.of_N 8));
[ lazymatch e with
| SOff 67 0 => split; [cbn [sv_denot]; rewrite X67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Ra4]
| SOff 32 ?o => ptr 32%nat o g X32
| SOff 46 ?o => ptr 46%nat o cfp X46
| SOff ?na ?o => ptr na o nw Xnw
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 ?o) (SLit 3)) (SOff 38 0) => shcell 32%nat o g X32
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 ?o) (SLit 3)) (SOff 38 0) => shcell 46%nat o cfp X46
| SAlu ALU_ADD (SAlu ALU_SRL (SOff ?na ?o) (SLit 3)) (SOff 38 0) => shcell na o nw Xnw
| _ => idtac "AF_LOCSD-SHAPE" od e; fail
end
| apply (field_of_region Ex _ 2 (sp0 - 224) cs lo hi wlo whi od 8 e v HR0 Xsp ltac:(cbn; tauto) (proj1 Hdr) (proj2 Hdr)); cbn; clear; lia ]
end
| _ => idtac "AF_LOCSD-NOCHUNK" od; fail end in
split; [one 104|]; split; [one 112|]; split; [one 56|]; split; [one 8|]; split; [one 16|]; split; [one 24|]; split; [one 32|];
split; [one 40|]; split; [one 48|]; split; [one 64|]; split; [one 72|]; split; [one 80|]; split; [one 88|]; one 96
end end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_lcDD_ok : forall E (m : word -> option byte) sp0 g cfp a4v nw,
af_locsD m sp0 g cfp a4v nw ->
ew E 32 = Z_to_bv 64 g -> ew E 38 = Z_to_bv 64 SB -> ew E 46 = Z_to_bv 64 cfp ->
ew E 67 = Z_to_bv 64 a4v -> ew E 23 = Z_to_bv 64 nw ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= nw -> nw + 40 <= alloc_ceiling -> 0 <= a4v < 2 ^ 64 ->
Forall (YP09.chunk_ok SEGS E m (sp0 - 224 - 0)) af_lcDD.
Proof.
intros E m sp0 g cfp a4v nw (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14) E32 E38 E46 E67 E23 Hg0 Hgc Hc0 Hcc Hn0 Hnc Ha4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SH : forall n o b, ew E n = Z_to_bv 64 b -> 0 <= b -> 0 <= o -> b + o <= alloc_ceiling ->
sv_denot E (shq n o) = Z_to_bv 64 (SB + (b + o) / 8) /\ 0 <= SB + (b + o) / 8 < 2 ^ (8 * Z.of_N 8)).
{ intros n o b En Hb Ho Hbc. split; [apply (denot_shx E n 38 o b SB En E38); unfold SB; lia|].
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
assert (Hd : 0 <= (b + o) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
assert (PT : forall n o b, ew E n = Z_to_bv 64 b -> 0 <= b -> 0 <= o -> b + o <= alloc_ceiling ->
sv_denot E (SOff n o) = Z_to_bv 64 (b + o) /\ 0 <= b + o < 2 ^ (8 * Z.of_N 8)).
{ intros n o b En Hb Ho Hbc. split; [cbn [sv_denot]; rewrite En, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]. }
replace (sp0 - 224 - 0) with (sp0 - 224) by lia. unfold af_lcDD. change (2 ^ 64) with (2 ^ (8 * Z.of_N 8)) in Ha4.
repeat apply Forall_cons; try apply Forall_nil.
- destruct (PT 32%nat 92 g E32 Hg0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 104 8 _ _ Dd Dr); [cbn; lia | exact L1].
- destruct (SH 32%nat 92 g E32 Hg0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 112 8 _ _ Dd Dr); [cbn; lia | exact L2].
- apply (chunk_ok_val SEGS E m (sp0 - 224) 56 8 _ a4v); [cbn [sv_denot]; rewrite E67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Ha4 | cbn; lia | exact L3].
- destruct (SH 46%nat 0 cfp E46 Hc0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 8 8 _ _ Dd Dr); [cbn; lia | exact L4].
- destruct (SH 23%nat 0 nw E23 Hn0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 16 8 _ _ Dd Dr); [cbn; lia | exact L5].
- destruct (SH 46%nat 26 cfp E46 Hc0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 24 8 _ _ Dd Dr); [cbn; lia | exact L6].
- destruct (SH 32%nat 50 g E32 Hg0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 32 8 _ _ Dd Dr); [cbn; lia | exact L7].
- destruct (SH 32%nat 48 g E32 Hg0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 40 8 _ _ Dd Dr); [cbn; lia | exact L8].
- destruct (PT 32%nat 48 g E32 Hg0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 48 8 _ _ Dd Dr); [cbn; lia | exact L9].
- destruct (SH 46%nat 8 cfp E46 Hc0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 64 8 _ _ Dd Dr); [cbn; lia | exact L10].
- destruct (PT 46%nat 26 cfp E46 Hc0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 72 8 _ _ Dd Dr); [cbn; lia | exact L11].
- destruct (PT 23%nat 8 nw E23 Hn0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 80 8 _ _ Dd Dr); [cbn; lia | exact L12].
- destruct (SH 23%nat 8 nw E23 Hn0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 88 8 _ _ Dd Dr); [cbn; lia | exact L13].
- destruct (PT 46%nat 8 cfp E46 Hc0 ltac:(lia) ltac:(lia)) as [Dd Dr]. apply (chunk_ok_val SEGS E m (sp0 - 224) 96 8 _ _ Dd Dr); [cbn; lia | exact L14].
Qed.
Lemma af_reseedD : forall pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 X more nw,
let a4v := Z.land fattr 4 in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midx B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 X ->
getr regs1 2 = w64 (spZ regs - 224) -> getr regs1 23 = w64 nw -> In (nw, FRAME_SIZE) (ablocks B lyc Sc) ->
af_locsD (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v nw ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 224 - 0)) lcx ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regions 0 true (af_lcDD ++ lcx) (cg_ihead s1) wlo whi) = true ->
st_ok_pi SEGS VAL E (ss_af pc sregs 0 true (af_lcDD ++ lcx) (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 X more nw a4v E
CX MID Rsp R23 HnwIn HL HLX Hwlo Hwhi HREG HWFR.
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof (proj1 HJ) as HAR1. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing1 : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR1 HnwIn) as (Hn16 & Hn4096 & Hnceil & _).
change (req_size FRAME_SIZE) with 40 in Hnceil.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) as HFO1.
pose proof HFO1 as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (Hf4096 & Hfceil & Hfhigh).
assert (Hcfp : 0 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (Rsp' : bv_unsigned (getr regs1 2) = sp0 - 224 - 0) by (rewrite Rsp; rewrite unsigned_lit_small by lia; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more)) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 47%nat ltac:(unfold A_TEXT; lia)) as E47. pose proof (ES 48%nat ltac:(unfold A_TEXT; lia)) as E48.
pose proof (ES 49%nat ltac:(unfold A_TEXT; lia)) as E49. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46.
cbn [Nat.sub nth af_extra map app firstn repeat] in E32, E38, E46, E47, E48, E49, E67.
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rlpal.
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) img HCF eq_refl eq_refl) as [_ Rimg]. cbn [snd] in Rimg. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rimg.
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (Ha4r : 0 <= a4v < 2 ^ 64) by (subst a4v; pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; lia) ltac:(clear - PBASE PBLO; lia)) as Xl; cbn in Xl; clear - Xl; lia).
exact (af_seed B TL LAWS pc sregs 0 true (af_lcDD ++ lcx) (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(proj2 (Forall_app _ _ _) (conj (af_lcDD_ok E _ sp0 g cfp a4v nw HL E32 E38 E46 E67 E23 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) ltac:(lia) Hnceil Ha4r) HLX))
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF)).
Qed.
End d.
End c.
End a.
