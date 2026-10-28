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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgl.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awr_nX_rec Usp E32u Hing HTS Bres Anew HrIn :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPb, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bres with _ = ?res =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat res);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bres
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with (res + (a - res)) by lia; apply Anew; [exact HrIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_n: no rule for the head region" ];
awr_nX_rec Usp E32u Hing HTS Bres Anew HrIn
end.
Ltac awr_nX Usp E32u Hing HTS Bres Anew HrIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_nX_rec Usp E32u Hing HTS Bres Anew HrIn.
Lemma U_zext_small : forall E w a v, U E a = v -> 0 <= v < 2 ^ Z.of_N w -> Z.of_N w <= 64 -> U E (SExt false w a) = v.
Proof.
intros E w a v Ha Hv Hw. rewrite U_SExt, Ha. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64.
split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma U_mul_smallD : forall E a b, U E a * U E b < 2 ^ 64 -> U E (SMd M_MUL a b) = U E a * U E b.
Proof.
intros E a b H. rewrite U_SMd. cbn [zmd_raw]. pose proof (U_range E a). pose proof (U_range E b).
apply zcanon_id. unfold M64. split; [apply Z.mul_nonneg_nonneg; lia | exact H].
Qed.
Lemma U_add0 : forall E x, U E (SAlu ALU_ADD x (SLit 0)) = U E x.
Proof.
intros E x. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma land_mod2p : forall x m k, 0 <= x -> 0 <= m < 2 ^ k -> 0 <= k -> Z.land (x mod 2 ^ k) m = Z.land x m.
Proof.
intros x m k Hx Hm Hk. rewrite <- (Z.land_ones x k) by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Ltac awr_n_rec Usp E32u Hing HTS Bres Anew HrIn :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPa, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bres with _ = ?res =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat res);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bres
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with (res + (a - res)) by lia; apply Anew; [exact HrIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_n: no rule for the head region" ];
awr_n_rec Usp E32u Hing HTS Bres Anew HrIn
end.
Ltac awr_n Usp E32u Hing HTS Bres Anew HrIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_n_rec Usp E32u Hing HTS Bres Anew HrIn.
Ltac rregD HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = sv_denot E e) by (exact (st_ok_pi_restrict_reg H E ss ms r HS))
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = sv_denot E e) by (exact (st_ok_restrict_reg segs H E ss ms r HS)) end.
Ltac regvD HS AGx EEo2 X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
unfold w64; apply (shq_word Ex n 38 c _ SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGVD-ALU" r; fail
| |- _ =>
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| idtac "REGVD-FAIL" r; fail ]
end end.
Ltac locvD1 HR0 sp0 E32 E32u E38 E46 E67 E72 E72u Usp Hcfp HZg Hgceil Hr4096 HrCeil C1 :=
lazymatch goal with |- val_mem _ _ (?spx - 224 + ?off) 8 ?v =>
lazymatch type of HR0 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk off (CVal 8 ?e)] =>
apply (field_of_region Ex _ 2 (spx - 224) cs lo hi wlo whi off 8 e v HR0 Usp); [cbn; tauto | | | cbn; lia];
[ lazymatch e with
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 _) (SLit 3)) (SOff 38 0) => apply (denot_shx Ex 32 38 _ _ SB E32 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 _) (SLit 3)) (SOff 38 0) => apply (denot_shx Ex 46 38 _ _ SB E46 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 _) (SLit 3)) (SOff 38 0) => apply (denot_shx Ex 516 38 _ _ SB E72 E38); clear - Hr4096 HrCeil C1; unfold SB; lia
| _ => cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E46 | exact E67 | exact E72 | rewrite E32u; reflexivity | rewrite E72u; reflexivity | rewrite E46, unsigned_lit_small by lia; reflexivity
| idtac "LOCVD1-DENOT-FAIL" off ]
end
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
first [ lazymatch goal with |- 0 <= _ + ?x / 8 < _ =>
let Hd := fresh "Hd" in
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (clear - Hcfp HZg Hr4096 HrCeil C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
clear - Hd C1; unfold SB; lia end
| clear - Hcfp HZg Hr4096 HrCeil C1; lia
| destruct (Z.land _ 4 =? 0); clear; lia
| idtac "LOCVD1-RANGE-FAIL" off ] ]
| _ => idtac "LOCVD1-NO-CHUNK" off
end end end.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
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
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition regsD : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88).
Definition af_SH72 : list shent := af_SH ++ [mkSHE 516 0 FRAME_SIZE].
Section l.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis HTR : forall t, In t (af_sites B) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_D1X : AF_D2_stmtX K MT XN B -> AF_D_stmtX K MT XN B.
Proof.
intros PD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i GPAL IMG LPAL gs gsF gs1
CX MID Hk HBB HR HR9 R24 HL HnoTab Hi Hnone Hs1 XD.
destruct XD as [XDV XM].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK).
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R22).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (HEVF : EV_FLUSH = 35) by reflexivity. assert (HEVA : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (af_reseedX B TL LAWS AF_D regsD 0 0 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 []
(proj1 CX) MID Rsp HL ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsFL_ok B regs regs1 g s1 cfp _ _ HR HR9 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp)) ltac:(vm_compute; reflexivity) Hpfr) as [HS SHOK].
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38.
pose proof (ES 42%nat ltac:(unfold A_TEXT; lia)) as E42. pose proof (ES 43%nat ltac:(unfold A_TEXT; lia)) as E43. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46.
pose proof (ES 47%nat ltac:(unfold A_TEXT; lia)) as E47. pose proof (ES 48%nat ltac:(unfold A_TEXT; lia)) as E48. pose proof (ES 49%nat ltac:(unfold A_TEXT; lia)) as E49. pose proof (ES 50%nat ltac:(unfold A_TEXT; lia)) as E50.
pose proof (ES 51%nat ltac:(unfold A_TEXT; lia)) as E51. pose proof (ES 52%nat ltac:(unfold A_TEXT; lia)) as E52. pose proof (ES 53%nat ltac:(unfold A_TEXT; lia)) as E53. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E36, E37, E38, E42, E43, E46, E47, E48, E49, E50, E51, E52, E53, E67.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
{ awr_aX Usp E32u Hing HTS. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pmkst HS.
ppcs.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre lyc _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp, Usp; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot]; rewrite E32u; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
assert (HliveC : blocks_bytes Sc + 40 <= LIVE_MAX) by (clear - HBB Hlive; unfold LIVE_ADDFRAME in Hlive; lia).
assert (XNLP : 0 <= mo_malloc MT (3 * nlp)).
{ pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rq]. cbn [snd] in Rq. apply (mo_malloc_nonneg MT MLAW). clear - Rq. cbn in Rq. lia. }
assert (XNN : 0 <= mo_malloc MT N).
{ pose proof HWF as (_ & XWge & XHge & XNWH & _). apply (mo_malloc_nonneg MT MLAW). clear - XWge XHge XNWH. nia. }
assert (XMOKn : mo_ok MT Sc (mo_malloc MT (40))).
{ apply (af_xmtr_ok MT XN S Sc N _ _ _ MLAW XMOK (mo_malloc_nonneg MT MLAW (40) ltac:(clear; lia)) XM). unfold af_need1, af_need2, af_need3. clear - XNLP XNN. lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 Wc (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPb g s N) ly S W mem md []
lyc Sc _ k 40 (-224) (Z_to_bv 64 (BASE + 0xc2c)) [] HJ);
[ rewrite Ra0; reflexivity
| unfold MALLOC_MAX; clear; lia
| exact HliveC
| unfold spZ; rewrite Qsp, Usp; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp, (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite Qtp, (EEo 4%nat 4%bv eq_refl); exact Rtp
| exact Rra
| apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| clear - Hnev Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (pal_rt_below B TL) as Hrtb; clear - Hrtb PBASE; lia);
apply HTR; cbn [af_sites In]; repeat (first [left; reflexivity | right])
| exact XMOKn ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hr4096X & EblX & HKX & MLE2 & HJf).
mresX Hr4096X EblX HKX Hres.
pose proof (proj1 HJ2) as HAR2.
destruct (mres_kept B lyc Sc Wc _ W2 mem2 ly2 S2 _ _ res 40 Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 lyc Sc res 40 _ _ HAR2 Hres) as Hrng. change (req_size 40) with 40 in Hrng, HK.
pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & _ & _).
assert (HnewG : forall a, g + 0 <= a < g + 96 -> ~ (res <> 0 /\ res <= a < res + 40)).
{ intros a Ha [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (Permutation_app HPerm1 (Permutation_refl [(res, 40)])) as P2. rewrite <- Ebl in P2. unfold cgif_blocks in P2. cbn [app] in P2.
pose proof (sep_hd_in B LAWS ly2 S2 W2 mem2 md2 _ (res, 40) _ HAR2 P2 ltac:(right; apply in_or_app; right; left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size 40) with 40 in D. clear - D Ha Hin. lia. }
assert (HnewF : forall a, cfp + 0 <= a < cfp + 32 -> ~ (res <> 0 /\ res <= a < res + 40)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ res 40 cid pos HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2; exact Hfin)) as D.
pose proof HJ2 as (_ & Hly2' & _). assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct Hly2' as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. change (req_size 40) with 40 in D. clear - D Ha Hin Hflo Hfhi. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[img_word_fact | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | clear; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[img_word_fact | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | clear; lia].
- eapply (region_kept_block_aj SEGS B); [exact HK | exact E32u | exact Hing | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | exact HnewG].
- eapply (region_kept_frame_aj SEGS B); [exact HK | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia | clear; lia | exact HnewF]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS. try (let Hx := fresh "HEIo" in rename HEI2 into Hx). assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; clear - Hn; lia).
assert (E2r : ew E2 516 = Z_to_bv 64 res) by (rewrite HE2; change 516%nat with (512 + 4)%nat; rewrite (YN3v.ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Ha0).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 224) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (E42_2 : ew E2 42 = Z_to_bv 64 (cg_W s1)) by (rewrite OLD2 by lia; exact E42).
assert (E43_2 : ew E2 43 = Z_to_bv 64 (cg_H s1)) by (rewrite OLD2 by lia; exact E43).
assert (E46_2 : ew E2 46 = Z_to_bv 64 cfp) by (rewrite OLD2 by lia; exact E46).
assert (E47_2 : ew E2 47 = Z_to_bv 64 lpal) by (rewrite OLD2 by lia; exact E47).
assert (E48_2 : ew E2 48 = Z_to_bv 64 img) by (rewrite OLD2 by lia; exact E48).
assert (E49_2 : ew E2 49 = Z_to_bv 64 fattr) by (rewrite OLD2 by lia; exact E49).
assert (E50_2 : ew E2 50 = Z_to_bv 64 fgen) by (rewrite OLD2 by lia; exact E50).
assert (E51_2 : ew E2 51 = Z_to_bv 64 delay) by (rewrite OLD2 by lia; exact E51).
assert (E52_2 : ew E2 52 = Z_to_bv 64 nlp) by (rewrite OLD2 by lia; exact E52).
assert (E53_2 : ew E2 53 = Z_to_bv 64 tidx) by (rewrite OLD2 by lia; exact E53).
assert (E67_2 : ew E2 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD2 by lia; exact E67).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 512)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD2 by exact Hn68; exact (EEo n rr Hn)).
assert (SEPn : forall b m ii, In (b, m) (ablocks B lyc Sc) -> 0 <= ii < req_size m -> ~ (res <> 0 /\ res <= b + ii < res + 40)).
{ intros b m ii Hb Hii [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res 40 b m HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hb) as D.
change (req_size 40) with 40 in D. clear - D Hii Hin. lia. }
assert (Kblk : forall b m, In (b, m) (ablocks B lyc Sc) -> blk_kept (w_H Wc) (w_H W2) memc mem2 b (req_size m)).
{ intros b m Hb ii Hii. pose proof HK as (_ & K2 & _). etransitivity; [exact (K2 b m ii Hb Hii (SEPn b m ii Hb Hii))|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _). apply UN1; clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia. }
assert (HT2 : xcgif_at SEGS wfn path hw pf (mrestrict (w_H W2) mem2) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- exact (obj_at_blk_kept _ _ _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF (Kblk g CGIF_SIZE Hing)).
- apply (obj_at_blk_kept _ _ _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). apply (Kblk (cg_raw s1) RAW_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. left. reflexivity.
- intros f Hfi. apply (obj_at_blk_kept _ _ _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). apply (Kblk (fr_ptr f) FRAME_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
assert (HFR2 : af_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR). intros a Ha. pose proof HK as (K1 & _). apply (mbyte_of_aview SEGS).
etransitivity; [apply (K1 a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|]. apply UN1; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{   exfalso. clear - Hres0 Hr4096X. lia. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
prreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia;
change (2 ^ 4) with 16; clear - Hr4096 HrHi HrCeil Hr16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 40 HAR2 HrIn) as (_ & _ & _ & _ & HrP & _). change (req_size 40) with 40 in HrP.
assert (Bres : bv_unsigned (ew E2 516) = res) by (rewrite E2r; apply unsigned_lit_small; lia).
assert (Dgn : g + 96 <= res \/ res + 40 <= g).
{ pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res 40 g CGIF_SIZE HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hing) as D.
change (req_size CGIF_SIZE) with 96 in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= res \/ res + 40 <= cfp).
{ pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ res 40 cid pos HAR2 HrIn ltac:(rewrite Hfrs2; exact Hfin)) as D.
pose proof HJ2 as (_ & Hly2' & _). assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct Hly2' as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 516%nat) 0 40 0 40 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bres; split; [clear - Hr4096 HrCeil C1; lia|]; split; [clear - Hr4096 HrCeil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HrP (res + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bres, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hr4096 HrHi HrCeil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 516%nat) 0 40 0 40 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bres; split; [clear - Hr4096 HrCeil C1; lia|]; split; [clear - Hr4096 HrCeil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HrP (res + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bres, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hr4096 HrHi HrCeil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH72 E2 (mrestrict (w_H W2) mem2)).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO Hpfcb) as (_ & _ & HRA2).
unfold sh_ok, af_SH72, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 516 res 40 0 FRAME_SIZE HAR2 HrIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bres.
+ lia.
+ change (req_size 40) with 40. unfold FRAME_SIZE. lia. }
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 40 HJ HAR2 Ebl ltac:(clear - PBASE PBLO; lia)) as Tnew.
assert (Anew : forall blc ii lyq ownq, In (res, 40) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (res + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 40 blc ii lyq ownq HJ HAR2 Ebl ltac:(clear - PBASE PBLO; lia) Hbl Hii). }
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK RBspanA.
{ awr_nX Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bres Anew HrIn. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bres in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
pose proof (af_xmtr_step MT XN S Sc S2 N _ _ _ (af_need2 MT N nlp) (af_need2 MT N nlp) MLAW (mo_malloc_nonneg MT MLAW 40 ltac:(clear; lia)) XM MLE2 ltac:(unfold af_need1; clear; lia) ltac:(unfold af_need1; clear; lia)) as XM2.
af_xunz2 UN1 B LAWS lyc Sc Wc memc mdc g s1 N (@nil (Z * Z)) (@nil (Z * Z)) ly sp0 HAR HPerm1 Hstk HTS HTS XZb1 XZi1.
lazymatch type of HJf with ajournal _ _ _ _ _ _ _ _ _ ?mdq _ _ _ _ _ _ _ =>
pose proof (af_xdv_unz B K AIL (w_H Wc) memc _ mdc mdq s s1 N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (@nil (Z * Z)) _ _ UN1 XZb1 XZi1 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XDV) as XDV1 end.
pose proof (af_xdv_subj B K AIL _ _ lyc Sc Wc _ _ _ ly2 S2 W2 mem2 md2 _ g s s1 N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (@nil (Z * Z)) _ HJf HPerm1 HBin Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) Hlen1 XDV1) as XDV2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) (cgif_blocks g s1 N ++ ((@nil (Z * Z)) ++ [(res, 40)]) ++ af_cblocks img N fattr lpa nlp rest))
by (rewrite Ebl; exact (perm_new_own _ _ (@nil (Z * Z)) _ (res, 40) HPerm1)).
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr0]. cbn [snd] in Rfattr0.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
-
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq6 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq6 by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq6.
lazymatch type of Hq6 with Z.land (U ?Ex ?e) 6 = _ =>
rewrite <- (land_mod2p (U Ex e) 6 32 (proj1 (U_range Ex e)) ltac:(clear; lia) ltac:(clear; lia)) in Hq6;
rewrite (U_sext32_low Ex 49 fattr ltac:(rewrite ?ew_ewset_other by lia; exact E49_2) ltac:(clear - Rfattr0; lia)) in Hq6 end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK RBspanA AF_D2; [awr_nX Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bres Anew HrIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bres in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) -> aview SEGS (w_H W2) (ms_mem msL) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha Hn; etransitivity; [exact (UN3 a Ha Hn) | exact (UN2 a Ha Hn)]).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn  end.
assert (AGx : forall n, (n < 528)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67_2).
assert (X72 : ew EL 516 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 516) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr].
pose proof (obj_at_nth SEGS _ _ _ _ 3 (20, 4%N) fgen HCF eq_refl eq_refl) as [_ Rfgen]. pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdelay].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. pose proof (obj_at_nth SEGS _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx].
pose proof (obj_at_nth SEGS _ _ _ _ 7 (48, 2%N) (cg_W s1) (proj1 HT1) eq_refl eq_refl) as [_ RW]. pose proof (obj_at_nth SEGS _ _ _ _ 8 (50, 2%N) (cg_H s1) (proj1 HT1) eq_refl eq_refl) as [_ RH].
cbn [snd] in Rlpal, Rfattr, Rfgen, Rdelay, Rnlp, Rtidx, RW, RH.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i res GPAL IMG LPAL gs gsF gs1 CX) end.
+
split; [exact HJ2|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview SEGS); apply K23; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha HrCeil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview SEGS). apply K23; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia.
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZf f ii Hfi Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
pose proof (SEPn _ _ ii Hfb ltac:(change (req_size FRAME_SIZE) with 40; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia. }
split; [exact HOK|]. split.
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
split; [exact Hnew|]. intros b [<- | []]. split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ rewrite (blocks_bytes_bsum B ly2 S2), Ebl, bsum_app, <- (blocks_bytes_bsum B lyc Sc). cbn [bsum fold_right snd]. unfold FRAME_SIZE. clear - HBB. lia.
+ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+
unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64;
apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear - PBASE PBLO; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear - PBASE PBLO; lia)); exact R24.
+
let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X72.
+
assert (UH : U EL (SExt false 16 (SOff 43 0)) = cg_H s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 43 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E43_2) ltac:(clear - RH; lia))); [clear - RH; cbn in RH |- *; lia | cbn; clear; lia]).
assert (UW : U EL (SExt false 16 (SOff 42 0)) = cg_W s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 42 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E42_2) ltac:(clear - RW; lia))); [clear - RW; cbn in RW |- *; lia | cbn; clear; lia]).
let R := fresh "R" in rregD HS (10%bv : bv 5) R; rewrite R; rewrite denot_lit_U; unfold w64; f_equal.
rewrite U_mul_smallD by (rewrite UH, UW; clear - RW RH; nia). rewrite UH, UW. clear - HWF1. destruct HWF1 as (_ & _ & _ & HN & _). lia.
+
let R := fresh "R" in prreg HS (21%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
+
let R := fresh "R" in rregD HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 46 38 8 cfp SB X46 X38); clear - Hcfp C1; unfold SB; lia.
+
let R := fresh "R" in prreg HS (26%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+
let R := fresh "R" in rregD HS (19%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 48 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
let R := fresh "R" in prreg HS (27%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+
let R := fresh "R" in rregD HS (20%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 50 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
unfold af_locsD2, af_locsD3, af_locsE; change (spZ regs) with sp0.
repeat match goal with |- _ /\ _ => split end; locvD1 HR0 sp0 X32 X32u X38 X46 X67 X72 X72u Xsp Hcfp HZg Hgceil Hr4096 HrCeil C1.
+ exact HnoTab.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HrIn.
+
pose proof (U_sext32_low EL 49 fattr ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E49_2) ltac:(clear - Rfattr; lia)) as Q49. unfold U in Q49.
pose proof (U_sext32_low EL 50 fgen ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E50_2) ltac:(clear - Rfgen; lia)) as Q50. unfold U in Q50.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 51 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E51_2) ltac:(clear - Rdelay; lia)) ltac:(clear - Rdelay; cbn in Rdelay |- *; lia) ltac:(cbn; clear; lia)) as Q51. unfold U in Q51.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 52 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E52_2) ltac:(clear - Rnlp; lia)) ltac:(clear - Rnlp; cbn in Rnlp |- *; lia) ltac:(cbn; clear; lia)) as Q52. unfold U in Q52.
lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 516 res cs lo hi wlo whi 0 8 (SOff 47 0) lpal HRn X72u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rlpal; lia) ltac:(cbn; lia)) as V0;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 16 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V16;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 20 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V20;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 24 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V24;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 26 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V26 end.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V16, V20. change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V24, V26.
rewrite Q49 in V16. rewrite Q50 in V20. rewrite Q51, Z.mod_small in V24 by (clear - Rdelay; lia). rewrite Q52, Z.mod_small in V26 by (clear - Rnlp; lia).
rewrite Z.add_0_r in V0. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V16, V20, V24, V26.
split; [exact V0|]. split; [exact V16|]. split; [exact V20|]. split; [exact V24|]. split; [exact V26|].
intros Hne; exfalso; apply Hne; exact Hq6.
+
af_xunz3 K23 B LAWS ly2 S2 W2 mem2 md2 g s1 N ((@nil (Z * Z)) ++ [(res, 40)]) [(res, 40)] (@nil (Z * Z)) ly sp0 HAR2 HPerm2
(Permutation_refl ((@nil (Z * Z)) ++ [(res, 40)])) Hstk HTS HTS XZb4 XZi4.
split; [| exact XM2].
exact (af_xdv_unz B K AIL (w_H W2) mem2 _ md2 _ s s1 N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (@nil (Z * Z)) _ _ K23 XZb4 XZi4 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XDV2).
-
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq6 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq6 by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq6.
lazymatch type of Hq6 with Z.land (U ?Ex ?e) 6 <> _ =>
rewrite <- (land_mod2p (U Ex e) 6 32 (proj1 (U_range Ex e)) ltac:(clear; lia) ltac:(clear; lia)) in Hq6;
rewrite (U_sext32_low Ex 49 fattr ltac:(rewrite ?ew_ewset_other by lia; exact E49_2) ltac:(clear - Rfattr0; lia)) in Hq6 end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK RBspanA AF_D2; [awr_nX Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bres Anew HrIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bres in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) -> aview SEGS (w_H W2) (ms_mem msL) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha Hn; etransitivity; [exact (UN3 a Ha Hn) | exact (UN2 a Ha Hn)]).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn  end.
assert (AGx : forall n, (n < 528)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67_2).
assert (X72 : ew EL 516 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 516) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr].
pose proof (obj_at_nth SEGS _ _ _ _ 3 (20, 4%N) fgen HCF eq_refl eq_refl) as [_ Rfgen]. pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdelay].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. pose proof (obj_at_nth SEGS _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx].
pose proof (obj_at_nth SEGS _ _ _ _ 7 (48, 2%N) (cg_W s1) (proj1 HT1) eq_refl eq_refl) as [_ RW]. pose proof (obj_at_nth SEGS _ _ _ _ 8 (50, 2%N) (cg_H s1) (proj1 HT1) eq_refl eq_refl) as [_ RH].
cbn [snd] in Rlpal, Rfattr, Rfgen, Rdelay, Rnlp, Rtidx, RW, RH.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i res GPAL IMG LPAL gs gsF gs1 CX) end.
+
split; [exact HJ2|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview SEGS); apply K23; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha HrCeil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview SEGS). apply K23; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia.
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZf f ii Hfi Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
pose proof (SEPn _ _ ii Hfb ltac:(change (req_size FRAME_SIZE) with 40; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia. }
split; [exact HOK|]. split.
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
split; [exact Hnew|]. intros b [<- | []]. split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ rewrite (blocks_bytes_bsum B ly2 S2), Ebl, bsum_app, <- (blocks_bytes_bsum B lyc Sc). cbn [bsum fold_right snd]. unfold FRAME_SIZE. clear - HBB. lia.
+ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+
unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64;
apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear - PBASE PBLO; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear - PBASE PBLO; lia)); exact R24.
+
let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X72.
+
assert (UH : U EL (SExt false 16 (SOff 43 0)) = cg_H s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 43 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E43_2) ltac:(clear - RH; lia))); [clear - RH; cbn in RH |- *; lia | cbn; clear; lia]).
assert (UW : U EL (SExt false 16 (SOff 42 0)) = cg_W s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 42 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E42_2) ltac:(clear - RW; lia))); [clear - RW; cbn in RW |- *; lia | cbn; clear; lia]).
let R := fresh "R" in rregD HS (10%bv : bv 5) R; rewrite R; rewrite denot_lit_U; unfold w64; f_equal.
rewrite U_mul_smallD by (rewrite UH, UW; clear - RW RH; nia). rewrite UH, UW. clear - HWF1. destruct HWF1 as (_ & _ & _ & HN & _). lia.
+
let R := fresh "R" in prreg HS (21%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
+
let R := fresh "R" in rregD HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 46 38 8 cfp SB X46 X38); clear - Hcfp C1; unfold SB; lia.
+
let R := fresh "R" in prreg HS (26%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+
let R := fresh "R" in rregD HS (19%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 48 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
let R := fresh "R" in prreg HS (27%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+
let R := fresh "R" in rregD HS (20%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 50 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
unfold af_locsD2, af_locsD3, af_locsE; change (spZ regs) with sp0.
repeat match goal with |- _ /\ _ => split end; locvD1 HR0 sp0 X32 X32u X38 X46 X67 X72 X72u Xsp Hcfp HZg Hgceil Hr4096 HrCeil C1.
+ exact HnoTab.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HrIn.
+
pose proof (U_sext32_low EL 49 fattr ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E49_2) ltac:(clear - Rfattr; lia)) as Q49. unfold U in Q49.
pose proof (U_sext32_low EL 50 fgen ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E50_2) ltac:(clear - Rfgen; lia)) as Q50. unfold U in Q50.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 51 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E51_2) ltac:(clear - Rdelay; lia)) ltac:(clear - Rdelay; cbn in Rdelay |- *; lia) ltac:(cbn; clear; lia)) as Q51. unfold U in Q51.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 52 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E52_2) ltac:(clear - Rnlp; lia)) ltac:(clear - Rnlp; cbn in Rnlp |- *; lia) ltac:(cbn; clear; lia)) as Q52. unfold U in Q52.
lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 516 res cs lo hi wlo whi 0 8 (SOff 47 0) lpal HRn X72u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rlpal; lia) ltac:(cbn; lia)) as V0;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 16 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V16;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 20 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V20;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 24 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V24;
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 26 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V26 end.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V16, V20. change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V24, V26.
rewrite Q49 in V16. rewrite Q50 in V20. rewrite Q51, Z.mod_small in V24 by (clear - Rdelay; lia). rewrite Q52, Z.mod_small in V26 by (clear - Rnlp; lia).
rewrite Z.add_0_r in V0. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V16, V20, V24, V26.
split; [exact V0|]. split; [exact V16|]. split; [exact V20|]. split; [exact V24|]. split; [exact V26|].
intros _.
pose proof (U_zext_small EL 8 _ _ (U_atom EL 53 _ ltac:(rewrite AGx by (clear - PBASE PBLO; lia); exact E53_2) ltac:(clear - Rtidx; cbn in Rtidx |- *; lia)) ltac:(clear - Rtidx; cbn in Rtidx |- *; lia) ltac:(cbn; clear; lia)) as Q53. unfold U in Q53.
lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 516 res cs lo hi wlo whi 28 1 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V28 end.
change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8) in V28. rewrite Q53, Z.mod_small in V28 by (clear - Rtidx; cbn in Rtidx |- *; lia). exact V28.
+
af_xunz3 K23 B LAWS ly2 S2 W2 mem2 md2 g s1 N ((@nil (Z * Z)) ++ [(res, 40)]) [(res, 40)] (@nil (Z * Z)) ly sp0 HAR2 HPerm2
(Permutation_refl ((@nil (Z * Z)) ++ [(res, 40)])) Hstk HTS HTS XZb4 XZi4.
split; [| exact XM2].
exact (af_xdv_unz B K AIL (w_H W2) mem2 _ md2 _ s s1 N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (@nil (Z * Z)) _ _ K23 XZb4 XZi4 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XDV2).
Qed.
End l.
End j.
End h.
