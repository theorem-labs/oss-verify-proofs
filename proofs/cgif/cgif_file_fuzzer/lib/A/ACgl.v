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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACjq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma bsum_nonneg : forall l, (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
intros l. unfold bsum. induction l as [|b l IH]; intros H; [cbn; lia|].
cbn. pose proof (H b ltac:(left; reflexivity)). pose proof (IH ltac:(intros b' Hb'; apply H; right; exact Hb')). lia.
Qed.
Lemma tcgif_vals_set_frames : forall hw s fr,
tcgif_vals hw (set_frames s fr) = frame_ptr (nth 0 fr None) :: frame_ptr (nth 1 fr None) :: frame_ptr (nth 2 fr None) :: skipn 3 (tcgif_vals hw s).
Proof. intros. reflexivity. Qed.
Lemma cgif_blocks_in_set_frames : forall g s fr N x,
(forall f, In (Some f) fr -> In (Some f) (cg_frames s)) -> In x (cgif_blocks g (set_frames s fr) N) -> In x (cgif_blocks g s N).
Proof.
intros g s fr N x Hsub Hx. rewrite cgif_blocks_set_frames in Hx. unfold cgif_blocks.
cbn [In] in Hx |- *. rewrite in_app_iff in Hx |- *.
destruct Hx as [H | [H | [H | H]]]; [tauto | tauto | tauto |]. right. right. right.
unfold frames_blocks in *. apply in_flat_map in H as (o & Ho & Hb). apply in_flat_map. exists o. split; [|exact Hb].
destruct o as [f|]; [exact (Hsub f Ho) | destruct Hb].
Qed.
Ltac ew_lift2 Ex En Hx :=
lazymatch type of En with ew _ ?n = ?v =>
assert (Hx : ew Ex n = v) by (rewrite ?ew_ewset_other by (clear; lia); rewrite ?ew_havoc_old by (clear; lia); exact En) end.
Ltac regv2 HS EEo E32 E32u E38 E46 Rsp Rgp Rtp Hcfp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
let Enx := fresh "Enx" in let E38x := fresh "E38x" in
lazymatch n with 32%nat => ew_lift2 Ex E32 Enx | 46%nat => ew_lift2 Ex E46 Enx end;
ew_lift2 Ex E38 E38x;
unfold w64; apply (shq_word Ex n 38 c _ SB Enx E38x); clear - Hcfp HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGV2-ALU" r; fail
| |- _ =>
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ reflexivity | exact E32 | exact E38 | exact E46 | rewrite E32u; reflexivity
| rewrite (EEo 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (EEo 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp | rewrite (EEo 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| rewrite E46, unsigned_lit_small by lia; reflexivity | apply bv_eq; vm_compute; reflexivity
| idtac "REGV2-FAIL" r; fail ]
end end.
Ltac locv2 HR0 sp0 E32 E32u E38 E46 E67 Usp Hcfp HZg Hgceil C1 Rfattr :=
lazymatch goal with |- val_mem _ _ (?spx - 224 + ?off) 8 ?v =>
lazymatch type of HR0 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk off (CVal 8 ?e)] =>
apply (field_of_region Ex _ 2 (spx - 224) cs lo hi wlo whi off 8 e v HR0 Usp); [cbn; tauto | | | cbn; lia];
[ first [ lazymatch goal with |- sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n ?c) (SLit 3)) (SOff 38 0)) = _ =>
let Enx := fresh "Enx" in let E38x := fresh "E38x" in
lazymatch n with 32%nat => ew_lift2 Ex E32 Enx | 46%nat => ew_lift2 Ex E46 Enx end; ew_lift2 Ex E38 E38x;
apply (denot_shx Ex n 38 c _ SB Enx E38x); clear - HZg Hcfp Hgceil C1; unfold SB; lia end
| lazymatch goal with |- sv_denot _ (SAlu _ _ _) = _ => idtac "LOCV2-ALU" off; fail | |- _ => idtac end;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E46 | exact E67 | rewrite E32u; reflexivity | rewrite E46, unsigned_lit_small by lia; reflexivity
| idtac "LOCV2-DENOT-FAIL" off; fail ] ]
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
first [ lazymatch goal with |- 0 <= _ + ?x / 8 < _ =>
let Hd := fresh "Hd" in
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (clear - Hcfp HZg C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
clear - Hd Hcfp HZg C1; unfold SB; lia end
| clear - Hcfp HZg C1; lia
| destruct (Z.land _ 4 =? 0); clear; lia
| lazymatch goal with |- 0 <= Z.land ?x 4 < _ => pose proof (land_small_r x 4 ltac:(clear - Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; clear - Xl; lia end
| idtac "LOCV2-RANGE-FAIL" off; fail ] ]
end end end.
Definition ZsW (g sp0 : Z) (a : Z) : Prop := (sp0 - 224 <= a < sp0 - 104) \/ (g <= a < g + 24).
Ltac kstep K Usp E32u :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m2) |- _ =>
lazymatch type of K with (forall a : Z, _ -> ~ ?Zs a -> aview _ _ _ a = aview _ ?Hh ?m0 a) =>
let UN := fresh "UN" in let K' := fresh "K" in
pose proof (kept_of_frame (segs:=pa_segs) _ _ _ _ _ Zs HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u in Hrr;
red; clear - Hrr; lia |]);
destruct Hin)) as UN;
assert (K' : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview _ Hh m2 a = aview _ Hh m0 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; etransitivity; [exact (UN a Ha Hn) | exact (K a Ha Hn)]);
clear K UN; rename K' into K end end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
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
Definition regsFL : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88).
Section q.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis HXMN : forall N, 1 <= N <= 100000000 -> 0 <= xn_flush XN N <= xm_flush XN N.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis HTR : forall t, In t (af_sites B) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Variable CTXfl : list (list Z).
Hypothesis HCTXfl : In [BASE + 0xba8] CTXfl.
Hypothesis FLUSHX : tflush_specX SEGS K B MT XN (BASE + AF_asan3_flushFrame) CTXfl wfn pa_relro_lo pa_relro_hi.
Lemma regsFL_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more,
af_regs_at B regs regs1 g -> af_s1_at regs1 g ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))) regsFL regs1.
Proof.
intros regs regs1 g s1 cfp cf more (R2 & R3 & R4 & R18 & R8 & R22) R9 Hg0 Hgc Hc0 Hcc. unfold af_s1_at in R9.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 88 g SB E32 E38) by (unfold SB; lia); exact R9
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; exact R8]
| rewrite E38; exact R22 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_FLX : AF_RETC_stmtX K MT XN B -> AF_D_stmtX K MT XN B -> AF_FL_stmtX K MT XN B.
Proof.
intros PRC PD ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 f1 GPAL IMG LPAL gs gsF
CX MID Hk HBB HR R9 HL HnoTab Hf1 Hsome2 XFL.
destruct XFL as (XREL & XLV & XGF & XM).
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
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HTF : TFLUSH_STK = 17440) by reflexivity.
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
pose proof (frames3 s1 N HWF1) as Hfr. rewrite Hf1 in Hfr. set (o0 := nth 0 (cg_frames s1) None) in Hfr.
destruct (nth 2 (cg_frames s1) None) as [f2|] eqn:Eo2; [| exfalso; exact (Hsome2 eq_refl)]. clear Eo2. clearbody o0.
assert (HfI : nth_error (cg_frames s1) 1 = Some (Some f1)) by (rewrite Hfr; reflexivity).
assert (HfI2 : nth_error (cg_frames s1) 2 = Some (Some f2)) by (rewrite Hfr; reflexivity).
destruct (af_reseedX B TL LAWS AF_FL regsFL 0 0 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 []
(proj1 CX) MID Rsp HL ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsFL_ok regs regs1 g s1 cfp _ _ HR R9 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp)) ltac:(vm_compute; reflexivity) Hpfr) as [HS SHOK].
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [(if Z.land fattr 4 =? 0 then 1 else 0)]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35. pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E33, E34, E35, E36, E37, E38, E46, E67.
rewrite Hfr in E33, E34, E35. cbn [nth frame_ptr] in E33, E34, E35.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA A_flushFrame.
{ awr_aX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
assert (HT' : xcgif_at SEGS wfn path hw pf (mrestrict (w_H Wc) (ms_mem ms)) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros i Hi. apply (mbyte_of_aview SEGS). apply UN1; clear - Hi Hg4096 Hgceil Hceil Hslo HTS C1; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZr i Hi) as [Hb Hn]. exact (UN1 _ Hb Hn).
- intros f Hin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZf f i Hin Hi) as [Hb Hn]. exact (UN1 _ Hb Hn). }
assert (HFR' : af_frame (mrestrict (w_H Wc) (ms_mem ms)) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR). intros a Ha. apply (mbyte_of_aview SEGS). apply UN1; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia. }
assert (Hfrin : In (fr_ptr f1, FRAME_SIZE) (frames_blocks N (cg_frames s1))).
{ unfold frames_blocks. apply in_flat_map. exists (Some f1). split; [rewrite Hfr; cbn; tauto | left; reflexivity]. }
assert (Hfrin2 : In (fr_ptr f2, FRAME_SIZE) (frames_blocks N (cg_frames s1))).
{ unfold frames_blocks. apply in_flat_map. exists (Some f2). split; [rewrite Hfr; cbn; tauto | left; reflexivity]. }
assert (Hfc : In (fr_ptr f1, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f1) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s1) RAW_SIZE HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
assert (Dgf : g + 96 <= fr_ptr f1 \/ fr_ptr f1 + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f1, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Dgr : g + 96 <= cg_raw s1 \/ cg_raw s1 + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (cg_raw s1, RAW_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D.
apply D. unfold cgif_blocks. left. reflexivity. }
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -224) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; exact E32);
assert (Q11' : getr rg 11 = w64 (fr_ptr f1)) by (rewrite Q11; exact E34);
assert (Q12' : getr rg 12 = w64 (frame_ptr (nth (1 - 1) (cg_frames s1) None))) by (rewrite Q12, Hfr; exact E33);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -224) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; rewrite E32u, unsigned_lit_small by lia; lia);
assert (Hctx1 : In (raZ rg :: spine []) CTXfl)
by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; cbn [spine]; exact HCTXfl);
assert (Htop' : spZ rg + 32 <= ly_top lyc) by (rewrite Qsp, Etopc; clear - Htop; lia);
assert (HROD' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) mm)) by (exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD));
assert (HEVc : st_nev Sc + EV_FLUSH <= EV_MAX) by (clear - Hnev Hk Hev Hk0 HEVF HEVA; lia)
end.
assert (Hfr7' : Z.of_nat (length (frames Sc)) <= 7) by (rewrite Hfrs; exact Hfr7).
assert (HLIVEc : blocks_bytes Sc + LIVE_FLUSH <= LIVE_MAX) by (clear - HBB Hlive; unfold LIVE_FLUSH, LIVE_ADDFRAME in *; lia).
af_xunz UN1 B LAWS lyc Sc Wc memc mdc g s1 N (@nil (Z * Z)) ly sp0 HAR HPerm1 Hstk HTS HTS XZb1 XZi1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdq) _ =>
pose proof (af_xrel_unz B K AIL (w_H Wc) memc _ mdc mdq s1 N img lpa fattr nlp GPAL IMG LPAL gs _ _ UN1 XZb1 XZi1 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) HWF1 eq_refl eq_refl XREL) as XREL1 end.
clear XZb1 XZi1.
pose proof XREL1 as (XR1 & _).
apply (proj1 (cgif_relA_split SEGS K _ _ s1 pf N GPAL gs)) in XR1 as (_ & XS1 & XL1).
destruct (XL1 XLV) as (XHrc & XHra & XHih & XHgp & XS0 & XSq1 & XSq2). clear XL1.
rewrite Hfr in XS0, XSq1, XSq2. cbn [nth] in XS0, XSq1, XSq2.
destruct (YO07.s_q1 gs) as [F1|] eqn:Hq1; [| destruct XSq1]. destruct (YO07.s_q2 gs) as [F2|] eqn:Hq2; [| destruct XSq2]. cbn [oframe_relbA] in XSq1, XSq2.
assert (XNUM : af_xf (1 <= N <= 100000000 /\ 0 <= xn_flush XN N <= xm_flush XN N /\ 0 <= mo_free MT /\ 0 <= af_needF MT N nlp /\ 0 <= af_need1 MT N nlp)).
{ unfold af_xf. pose proof HWF1 as (_ & XWge & XHge & XNWH & XNmax & _).
assert (XN1 : 1 <= N <= 100000000) by (clear - XWge XHge XNWH XNmax; nia).
pose proof (HXMN N XN1) as XFLn. pose proof (mo_free_nonneg MT MLAW) as Xf0.
assert (XNLP : 0 <= mo_malloc MT (3 * nlp)).
{ pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rq]. cbn [snd] in Rq. apply (mo_malloc_nonneg MT MLAW). clear - Rq. cbn in Rq. lia. }
pose proof (mo_malloc_nonneg MT MLAW 40 ltac:(clear; lia)) as X40. pose proof (mo_malloc_nonneg MT MLAW N ltac:(clear - XN1; lia)) as XNN.
unfold af_needF, af_need1, af_need2, af_need3. clear - XN1 XFLn Xf0 XNLP X40 XNN. lia. }
assert (XMOKfl : mo_ok MT Sc (xm_flush XN N)).
{ pose proof XNUM as XF. unfold af_xf in XF. apply (af_xmtr_ok MT XN S Sc N (xm_flush XN N) _ _ MLAW XMOK ltac:(clear - XF; lia) XM). clear - XF. lia. }
destruct (in_split _ _ Hpfr) as (xr1 & xr2 & Erest).
assert (HPermF : Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: af_cblocks img N fattr lpa nlp (xr1 ++ xr2)))
by (eapply Permutation_trans; [exact HPerm1 | rewrite Erest; apply af_perm_file]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS Wc rg mm _ TADDFRAME_STK sp0 (FPb g s N) ly S W mem md [] lyc Sc mdq k TFLUSH_STK
((fr_ptr f1 + 20, fr_ptr f1 + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) EV_FLUSH (-224) (Z_to_bv 64 (BASE + 0xba8)) []
(fun ly3 S3 W3 regs3 mem3 md3 => exists r gen' rwcur' : Z,
getr regs3 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
xcgif_at SEGS wfn path hw pf (mrestrict (w_H W3) mem3) g (flush_upd s1 1 gen' rwcur') /\
cgif_wf (flush_upd s1 1 gen' rwcur') N /\
Permutation (ablocks B ly3 S3) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) /\
gen' = fl_gen3 (gcfg_of s1 GPAL) F1 (YO07.s_q0 gs) /\
(exists code bytes, YO07.flush_frame (gcfg_of s1 GPAL) (rc_int (rw_cur s1)) F1 (YO07.s_q0 gs) = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
asink_at SEGS K (mrestrict (w_H W3) mem3) md3 pf (concat (YO07.s_out gs) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
mo_le MT Sc S3 (xn_flush XN N)) HJ Qsp);
[ reflexivity | lia | rewrite HTF; lia | rewrite HTS, HTF; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [clear; lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (FLUSHX lyc Sc Wc rg mm _ [] g s1 N 1%nat f1 pf path hw (af_cblocks img N fattr lpa nlp (xr1 ++ xr2)) (concat (YO07.s_out gs)) GPAL F1 (YO07.s_q0 gs)
HPRE1 Hctx1 Hfr7' Htop' HROD' Q10' HT' HWF1 Hpf0 ltac:(left; reflexivity) HfI Q11' Q12' HPermF XS1 XSMAX XHgp XSq1
ltac:(rewrite Hfr; exact XS0) XHra HEVc HLIVEc XMOKfl)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & (r & rwcur' & Hr10 & Rr & HTx & HWFx & HPx & HXx & HMx));
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP |]]];
exists r, (fl_gen3 (gcfg_of s1 GPAL) F1 (YO07.s_q0 gs)), rwcur';
split; [exact Hr10 | split; [exact Rr | split; [exact HTx | split; [exact HWFx | split; [| split; [reflexivity | split; [exact HXx | exact HMx]]]]]]];
eapply Permutation_trans; [exact HPx | rewrite Erest; apply Permutation_sym; apply af_perm_file] ]
| intros a Ha; destruct Ha as (rr & Hrr & Hrg); cbn [In] in Hrr;
destruct Hrr as [<- | [<- | Hrr]]; cbn [fst snd] in Hrg;
[ destruct (af_fp_coverX B ly S regs g s N lyc Sc (fr_ptr f1, FRAME_SIZE) a) as [[Hq _] | Hq]; [apply Hnew; exact (af_frame_in_blocks g s1 N f1 ltac:(rewrite Hfr; cbn; tauto)) | exact Hfc | cbn [fst snd]; change (req_size FRAME_SIZE) with 40; clear - Hrg; lia | left; exact Hq | right; exact Hq]
| destruct (af_fp_coverX B ly S regs g s N lyc Sc (cg_raw s1, RAW_SIZE) a) as [[Hq _] | Hq]; [apply Hnew; unfold cgif_blocks; right; left; reflexivity | exact Hinr | cbn [fst snd]; change (req_size RAW_SIZE) with 48; clear - Hrg; lia | left; exact Hq | right; exact Hq]
|   left; unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); right; exists rr; split; [exact Hrr | exact Hrg] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hr10 & Rr & HT2 & HWF2 & HPerm2 & Xgen & (code & bytes & Hff & Hrcode & Hrw & XS2 & Hlenb) & MLE2)).
pose proof (af_xq_flush B K LAWS _ _ lyc Sc Wc _ _ _ ly2 S2 W2 mem2 md2 _ g s1 N o0 f1 f2 F1 F2 gen' rwcur' img lpa fattr nlp rest GPAL IMG LPAL gs _
HJc2 HPerm1 HPerm2 Hpfr Hfr Hq1 Hq2 XLV XREL1 XS2) as XQ2.
assert (XM2 : af_xmtr MT XN S S2 N (af_needF MT N nlp) (af_needF MT N nlp)).
{ pose proof XNUM as XF. unfold af_xf in XF.
exact (af_xmtr_step MT XN S Sc S2 N (xn_flush XN N) _ _ (af_needF MT N nlp) (af_needF MT N nlp) MLAW ltac:(clear - XF; lia) XM MLE2 ltac:(clear - XF; lia) ltac:(clear; lia)). }
assert (XCODE : af_xf ((- 2 ^ 31 <= code < 2 ^ 31 /\ (code <> YO07.C_OK -> code <> YO07.C_PENDING) /\ (code <> YO07.C_OK -> bytes = [])) /\
((r = 0 <-> code = 0) /\ rc_int (r mod 2 ^ 32) = code) /\ rc_int (code mod 2 ^ 32) = code)).
{ unfold af_xf.
assert (Xrw : 0 <= rw_cur s1 < 2 ^ 32) by (pose proof (obj_at_nth SEGS _ _ _ _ 8 (40, 4%N) (rw_cur s1) (proj1 (proj2 HT1)) eq_refl eq_refl) as [_ Rq]; cbn [snd] in Rq; cbn in Rq; exact Rq).
pose proof (af_flush_code _ _ _ _ _ _ Hff (rc_int_range _ Xrw)) as XA.
split; [exact XA|]. split; [exact (af_code_reg r code Rr Hrcode (proj1 XA)) | exact (rc_int_mod32 code (proj1 XA))]. }
assert (XREST : gsF = if code =? YO07.C_OK
then YI0b.af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG (YO07.mkS (Some F1) (Some F2) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2
else YO07.mkS None (Some F1) (Some F2) (YO07.s_ihead gs) code code (YO07.s_out gs)).
{ assert (XG : gcfg_of s1 GPAL = gcfg_of s GPAL) by (unfold gcfg_of; rewrite HW1, HH1, Hattr1, Hgen1, Hngp1; reflexivity).
pose proof Hff as Hff'. rewrite XG, XHrc in Hff'.
assert (Xih : YO07.s_ihead gs = 1 \/ YO07.s_ihead gs = 2) by (rewrite <- XHih; pose proof HWF1 as (_ & _ & _ & _ & _ & _ & Hq & _); clear - Hq; tauto).
rewrite XGF. exact (af_rest_flushed (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs F1 F2 code bytes Hq1 Hq2 Xih Hff'). }
pose proof (proj1 HJ2) as HAR2.
set (s2 := flush_upd s1 1 gen' rwcur') in *.
pose proof (af_obj_ok_flush s s1 N 1 gen' rwcur' HOK HWF2) as HOK2. change (flush_upd s1 1 gen' rwcur') with s2 in HOK2.
set (f1' := set_fr_gen f1 gen') in *.
assert (Hfr2 : cg_frames s2 = [o0; Some f1'; Some f2]) by (subst s2 f1'; unfold flush_upd; cbn [cg_frames]; rewrite Hfr; reflexivity).
assert (EBL2 : cgif_blocks g s2 N = cgif_blocks g s1 N) by (subst s2; exact (cgif_blocks_flush_upd g s1 N 1 gen' rwcur' f1 HfI)).
assert (HPerm2s : Permutation (ablocks B ly2 S2) (cgif_blocks g s2 N ++ af_cblocks img N fattr lpa nlp rest)) by (rewrite EBL2; exact HPerm2).
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (Hpfc : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPermF|]; apply in_app_iff; right; left; reflexivity).
assert (HnFg : forall a, g + 0 <= a < g + 96 -> ~ inFP ((fr_ptr f1 + 20, fr_ptr f1 + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) a).
{ assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (pf, FILE_BLOCK) _ HAR HPermF) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D.
apply D. unfold cgif_blocks. cbn [app]. right. apply in_app_iff. right. left. reflexivity. }
intros a Ha (rr & Hrr & Hrg). cbn [In asink_fp] in Hrr. destruct Hrr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hrg;
[clear - Ha Hrg Dgf | clear - Ha Hrg Dgr | unfold FILE_BLOCK in Hrg; clear - Ha Hrg Dgp | unfold sink_token in Hrg; cbn [fst snd] in Hrg; clear - Ha Hrg Hg4096]; lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcellc & _ & Kgotc & _). rewrite HBgot, HBcell in Kgotc. rewrite HBcell in Kcellc.
pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & _ & _).
pose proof (proj2 (proj2 HJ2)) as HJ2r. cbn [ms_mem] in HJc2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[img_word_fact | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotc) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[img_word_fact | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellc) | lia].
- eapply (YC4b.region_kept_block_subw B); [exact HJc2 | exact E32u | exact Hing | exact Hing2 | clear; lia
| change (req_size CGIF_SIZE) with 96; clear; lia | intros a Ha HFP; exact (HnFg a Ha HFP) | intros a Ha; exfalso; clear - Ha; lia].
- eapply (region_kept_frame_sub B); [exact HJc2 | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia
| intros a Ha HFP; destruct HFP as (rr & Hrr & Hrg); cbn [In] in Hrr;
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc _ _ (fr_ptr f1) FRAME_SIZE cid pos HAR Hfc Hfin) as D1;
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc _ _ (cg_raw s1) RAW_SIZE cid pos HAR Hinr Hfin) as D2;
unfold zdisjoint in D1, D2; cbn [fst snd] in D1, D2; change (req_size FRAME_SIZE) with 40 in D1; change (req_size RAW_SIZE) with 48 in D2;
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc _ _ pf FILE_BLOCK cid pos HAR Hpfc Hfin) as D3; unfold zdisjoint in D3; cbn [fst snd] in D3; change (req_size FILE_BLOCK) with 1264 in D3;
cbn [In asink_fp] in Hrr; destruct Hrr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hrg;
[ | | unfold FILE_BLOCK in Hrg | unfold sink_token in Hrg; cbn [fst snd] in Hrg]; clear - Ha Hrg D1 D2 D3 Hflo Hfhi Hcfp; lia
| intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS. try (let Hx := fresh "HEIo" in rename HEI2 into Hx). assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; clear - Hn; lia).
assert (E2r : ew E2 516 = Z_to_bv 64 r) by (rewrite HE2; change 516%nat with (512 + 4)%nat; rewrite (YN3v.ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hr10).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 224) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E33_2 : ew E2 33 = Z_to_bv 64 (frame_ptr o0)) by (rewrite OLD2 by lia; exact E33).
assert (E34_2 : ew E2 34 = Z_to_bv 64 (fr_ptr f1)) by (rewrite OLD2 by lia; exact E34).
assert (E35_2 : ew E2 35 = Z_to_bv 64 (fr_ptr f2)) by (rewrite OLD2 by lia; exact E35).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (E46_2 : ew E2 46 = Z_to_bv 64 cfp) by (rewrite OLD2 by lia; exact E46).
assert (E67_2 : ew E2 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD2 by lia; exact E67).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 512)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD2 by exact Hn68; exact (EEo n rr Hn)).
pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO Hpfcb) as ((cid2 & pos2 & Hfin2 & _ & Hfal2 & Hflo2 & Hfhi2) & _ & HRA2).
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH E2 (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, af_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 Hing2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app. }
assert (HFR2 : af_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR'). intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
apply (mbyte_of_aview SEGS). apply (G1 a); clear - Ha Hceil Hslo Hshi H47 HTS HTF C1; lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s2) (proj1 HT2) eq_refl eq_refl) as [_ Rcur2]. cbn [snd] in Rcur2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK RBspanA A_freeFrame.
{ awr_aX Usp2 E32u2 Hing2 HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) P2; prreg HS (10%bv : bv 5) P10; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4; prreg HS (1%bv : bv 5) P1; prreg HS (8%bv : bv 5) P8.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
af_xunz UN2 B LAWS ly2 S2 W2 mem2 md2 g s2 N (@nil (Z * Z)) ly sp0 HAR2 HPerm2s Hstk HTS HTS XZb2 XZi2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdq) _ =>
pose proof (af_xq_unz B K AIL (w_H W2) mem2 _ md2 mdq s2 s2 N f1' f2 F1 F2 img lpa fattr nlp rest GPAL IMG LPAL _ _ UN2 XZb2 XZi2 Hpfr eq_refl eq_refl eq_refl
ltac:(rewrite Hfr2; right; left; reflexivity) ltac:(rewrite Hfr2; right; right; left; reflexivity) eq_refl eq_refl XQ2) as XQ3 end.
pose proof (af_side_sep B LAWS ly2 S2 W2 mem2 md2 g s2 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR2 HPerm2s Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr2 HZf2].
assert (HT2' : xcgif_at SEGS wfn path hw pf (mrestrict (w_H W2) (ms_mem ms0)) g s2).
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros i Hi. apply (mbyte_of_aview SEGS). apply UN2; clear - Hi Hg4096 Hgceil Hceil Hslo HTS C1; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZr2 i Hi) as [Hb Hn]. exact (UN2 _ Hb Hn).
- intros f Hin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZf2 f i Hin Hi) as [Hb Hn]. exact (UN2 _ Hb Hn). }
assert (HFR2' : af_frame (mrestrict (w_H W2) (ms_mem ms0)) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR2). intros a Ha. apply (mbyte_of_aview SEGS). apply UN2; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia. }
pose proof HJ2 as (_ & HLY2 & _ & _ & _ & Hfrs2 & Hnev2 & _). pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (P3' : getr rg 3 = w64 (as_gp B)) by (rewrite P3, OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (P4' : getr rg 4 = w64 (as_tp B)) by (rewrite P4, OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Psp : spZ rg = sp0 + -224) by (unfold spZ; rewrite P2, Usp2; lia);
assert (P10' : getr rg 10 = w64 (frame_ptr o0)) by (rewrite P10; exact E33_2);
assert (Ps0 : achain ly2 (aview SEGS (w_H W2) mm) (sp0 + -224) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite P8; rewrite E32u2, unsigned_lit_small by lia; lia);
assert (HEV2 : st_nev S2 + 3 <= EV_MAX) by (clear - Hnev2 Hk Hev Hk0 HEVF HEVA; lia);
assert (HU3 : In (call_trace0 (pc_free_ra0 (as_code B)) rg []) (as_universe B))
by (unfold call_trace0, unwind_of_chain, raZ; rewrite P1, unsigned_lit_small by lia; cbn; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); cbn; apply HTR; cbn [af_sites In]; repeat (first [left; reflexivity | right]))
end.
assert (HU1 : In [pc_free_ra0 (as_code B); (BASE + 0x2ad0)] (as_universe B)) by (apply HTR; cbn [af_sites In]; repeat (first [left; reflexivity | right])).
assert (HU2 : In [pc_free_ra0 (as_code B); (BASE + 0x2b08)] (as_universe B)) by (apply HTR; cbn [af_sites In]; repeat (first [left; reflexivity | right])).
assert (HBL : Permutation (ablocks B ly2 S2)
(match o0 with Some f => frame_blocks N f | None => [] end
++ ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest))).
{ eapply Permutation_trans; [exact HPerm2s|]. unfold cgif_blocks. rewrite Hfr2. unfold frames_blocks. cbn [flat_map app]. rewrite ?app_nil_r, <- ?app_assoc.
apply (Permutation_app_swap_app ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2)). }
clear CS HnFg.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (CONT : forall W4 ly4 S4 regs4 mem4 md4 ev FP1,
0 <= ev <= 3 ->
ajournal SEGS B TADDFRAME_STK sp0 (FPb g s N) ly S W mem md [] ly4 S4 W4 mem4 md4 (k + EV_FLUSH + ev) ->
ajournal SEGS B FF_STK (sp0 + -224) FP1 ly2 S2 W2 mm mdq [] ly4 S4 W4 mem4 md4 ev ->
aregs_preserved rg regs4 ->
(forall a, inFP FP1 a -> exists p n, In (p, n) match o0 with Some f => frame_blocks N f | None => [] end /\ p <= a < p + req_size n) ->
Permutation (ablocks B ly4 S4) ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest) ->
~ YI16.sink_open_fp FP1 -> mo_le MT S2 S4 (3 * mo_free MT) ->
SRr SEGS W4 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 0xbbc)) mem4 (seg_rom SEGS)) md4) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME)) end.
{ intros W4 ly4 S4 regs4 mem4 md4 ev FP1 Hev4 HJ4 HJc4 HP4 HFP1 HPerm4 XCL XMLE4.
pose proof (proj1 HJ4) as HAR4.
lazymatch type of HP4 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs4 rr = getr rg rr)
by (intros rr Hr; pose proof (HP4 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; left; reflexivity).
assert (Hinr4 : In (cg_raw s2, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; right; left; reflexivity).
assert (SEP0 : forall y a i, In y ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest) ->
fst y <= a < fst y + req_size (snd y) -> inFP FP1 a -> 0 <= i -> False).
{ intros y a i Hy Ha HFx _. destruct (HFP1 a HFx) as (p & n & Hpn & Hpa).
pose proof (sep_app B LAWS ly2 S2 W2 mem2 md2 (p, n) y _ _ HAR2 HBL Hpn Hy) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D Ha Hpa. lia. }
assert (HnFg : forall a, g + 0 <= a < g + 96 -> ~ inFP FP1 a).
{ intros a Ha HFx. apply (SEP0 (g, CGIF_SIZE) a 0 ltac:(left; reflexivity)); [cbn [fst snd]; change (req_size CGIF_SIZE) with 96; clear - Ha; lia | exact HFx | clear; lia]. }
assert (HnFr : forall i, 0 <= i < 48 -> ~ inFP FP1 (cg_raw s2 + i)).
{ intros i Hi HFx. apply (SEP0 (cg_raw s2, RAW_SIZE) (cg_raw s2 + i) 0 ltac:(right; left; reflexivity)); [cbn [fst snd]; change (req_size RAW_SIZE) with 48; clear - Hi; lia | exact HFx | clear; lia]. }
assert (HnFc : forall a, cfp + 0 <= a < cfp + 32 -> ~ inFP FP1 a).
{ intros a Ha HFx. destruct (HFP1 a HFx) as (p & n & Hpn & Hpa).
assert (Hpl : In (p, n) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hpn).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 _ _ p n cid2 pos2 HAR2 Hpl Hfin2) as D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hpa Hflo2 Hfhi2. lia. }
destruct (af_lk_in g s2 N f1' f2 img fattr lpa nlp rest Hpfr) as (XL1 & XL2 & XL3 & XL4 & XL5 & XL6).
pose proof (af_xq_subj B K AIL _ _ FP1 ly2 S2 W2 _ _ _ ly4 S4 W4 mem4 md4 _ _ s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL _ HJc4 XCL
ltac:(intros x Hx; split; [eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; right; exact Hx | eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hx])
ltac:(intros p n xk XHin XHk HFx; exact (SEP0 (p, n) (p + xk) 0 XHin ltac:(cbn [fst snd]; clear - XHk; lia) HFx ltac:(clear; lia)))
XL1 XL2 XL3 XL4 XL5 XL6 XQ3) as XQ4.
clear XL1 XL2 XL3 XL4 XL5 XL6.
assert (XM4 : af_xmtr MT XN S S4 N (af_need1 MT N nlp) (af_need1 MT N nlp)).
{ pose proof XNUM as XF. unfold af_xf in XF.
exact (af_xmtr_step MT XN S S2 S4 N (3 * mo_free MT) _ _ (af_need1 MT N nlp) (af_need1 MT N nlp) MLAW ltac:(clear - XF; lia) XM2 XMLE4 ltac:(unfold af_needF; clear; lia) ltac:(unfold af_needF; clear; lia)). }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcelld & _ & Kgotd & _). rewrite HBgot, HBcell in Kgotd. rewrite HBcell in Kcelld.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR4) as (Kcelle & _ & Kgote & _). rewrite HBgot, HBcell in Kgote. rewrite HBcell in Kcelle.
cbn [ms_mem] in HJc4.
jafter_call_keep_hi HS 528%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3; 4; 5]%nat HS4.
match type of HS4 with ?tt -> _ => assert (HRK : tt); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact Usp2 | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact Usp2 | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E2 _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[img_word_fact | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotd) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgote) | lia].
- apply (region_kept_val_at E2 _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[img_word_fact | exact (val_mem_of_rdword SEGS _ _ _ _ Kcelld) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcelle) | lia].
- eapply (YC4b.region_kept_block_subw B); [exact HJc4 | exact E32u2 | exact Hing2 | exact Hing4 | clear; lia
| change (req_size CGIF_SIZE) with 96; clear; lia | intros a Ha HFP; exact (HnFg a Ha HFP) | intros a Ha; exfalso; clear - Ha; lia].
- eapply (region_kept_frame_sub B); [exact HJc4 | rewrite E46_2; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin2 | clear - Hflo2; lia | clear - Hfhi2; lia
| intros a Ha HFP; exact (HnFc a Ha HFP) | intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E2 528 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS. try (let Hx := fresh "HEIo" in rename HEI4 into Hx). assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [first [exact HEI2 | assumption] | cbv; lia]).
assert (OLD4 : forall n, (n < 528)%nat -> ew E4 n = ew E2 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; clear - Hn; lia).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = sp0 - 224) by (rewrite OLD4 by lia; exact Usp2).
assert (E32u4 : bv_unsigned (ew E4 32) = g) by (rewrite OLD4 by lia; exact E32u2).
assert (E32_4 : ew E4 32 = Z_to_bv 64 g) by (rewrite OLD4 by lia; exact E32_2).
assert (E34_4 : ew E4 34 = Z_to_bv 64 (fr_ptr f1)) by (rewrite OLD4 by lia; exact E34_2).
assert (E35_4 : ew E4 35 = Z_to_bv 64 (fr_ptr f2)) by (rewrite OLD4 by lia; exact E35_2).
assert (E37_4 : ew E4 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD4 by lia; exact E37_2).
assert (E38_4 : ew E4 38 = Z_to_bv 64 SB) by (rewrite OLD4 by lia; exact E38_2).
assert (E46_4 : ew E4 46 = Z_to_bv 64 cfp) by (rewrite OLD4 by lia; exact E46_2).
assert (E67_4 : ew E4 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD4 by lia; exact E67_2).
assert (E72_4 : ew E4 516 = Z_to_bv 64 r) by (rewrite OLD4 by lia; exact E2r).
assert (EEo4 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 512)%nat -> ew E4 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD4 by lia; exact (EEo2 n rr Hn Hn68)).
pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] ly4 S4 W4 _ _ _ g s N _ cfp 32 HJ4 HAR0 HPerm HFO Hpfcb) as ((cid4 & pos4 & Hfin4 & _ & Hfal4 & Hflo4 & Hfhi4) & _ & HRA4).
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH E4 (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, af_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block SEGS B LAWS ly4 S4 W4 mem4 md4 E4 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR4 Hing4).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_4, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u4.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W4) mem4 E4 Bxa 46 cfp 32 cfp 0 32 HRA4).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_4, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_4, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app. }
assert (HFR4 : af_frame (mrestrict (w_H W4) mem4) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR2'). intros a Ha. pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
apply (mbyte_of_aview SEGS). apply (G1 a); clear - Ha Hceil Hslo Hshi H47 HTS HTF C1; unfold FF_STK, ASTACK; lia. }
assert (Kg : blk_kept (w_H W2) (w_H W4) (ms_mem ms0) mem4 g 96).
{ eapply (blk_kept_call B); [exact HJc4 | exact Hing2 | exact Hing4 | intros i Hi; apply HnFg; clear - Hi; lia]. }
assert (Kr : blk_kept (w_H W2) (w_H W4) (ms_mem ms0) mem4 (cg_raw s2) 48).
{ eapply (blk_kept_call B); [exact HJc4 | | exact Hinr4 | exact HnFr].
eapply Permutation_in; [apply Permutation_sym; exact HBL|]. apply in_or_app. right. right. left. reflexivity. }
assert (Kf : forall f, (f = f1' \/ f = f2) -> blk_kept (w_H W2) (w_H W4) (ms_mem ms0) mem4 (fr_ptr f) 40).
{ intros f Hf.
assert (Hy : In (fr_ptr f, FRAME_SIZE) ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest)).
{ right. right. apply in_or_app. right. apply in_or_app. destruct Hf as [-> | ->]; [left; left; reflexivity | right; apply in_or_app; left; left; reflexivity]. }
eapply (blk_kept_call B); [exact HJc4 | | | ].
- eapply Permutation_in; [apply Permutation_sym; exact HBL|]. apply in_or_app. right. exact Hy.
- eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]. exact Hy.
- intros i Hi HFx. apply (SEP0 _ (fr_ptr f + i) 0 Hy ltac:(cbn [fst snd]; change (req_size FRAME_SIZE) with 40; clear - Hi; lia) HFx). clear; lia. }
pose proof HT2' as (Ho2 & Hr2 & Hf2).
assert (Ho4 : obj_at SEGS (mrestrict (w_H W4) mem4) g LAY_CGIF (xcgif_vals path hw pf s2)) by (exact (obj_at_blk_kept _ _ _ _ g LAY_CGIF _ 96 Ho2 lay_inside_CGIF Kg)).
assert (Hr4 : obj_at SEGS (mrestrict (w_H W4) mem4) (cg_raw s2) LAY_Raw (traw_vals wfn g s2)) by (exact (obj_at_blk_kept _ _ _ _ _ LAY_Raw _ 48 Hr2 lay_inside_Raw Kr)).
assert (Hf4 : forall f, (f = f1' \/ f = f2) -> obj_at SEGS (mrestrict (w_H W4) mem4) (fr_ptr f) LAY_Frame (frame_vals f)).
{ intros f Hf. apply (obj_at_blk_kept _ _ _ _ _ LAY_Frame _ 40 (Hf2 f ltac:(rewrite Hfr2; destruct Hf as [-> | ->]; [right; left; reflexivity | right; right; left; reflexivity])) lay_inside_Frame (Kf f Hf)). }
clear Kg Kr Kf Ho2 Hr2 Hf2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR4 Hing4) as (_ & _ & _ & _ & HgP4 & _). change (req_size CGIF_SIZE) with 96 in HgP4.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx 4 r4 (set_window r4 0 24) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r4 0 24 (st_ok_pi_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E32u4; intros o Ho; apply (apresent_writable SEGS); apply HgP4; lia))) as HS5;
clear HS; rename HS5 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (ast_ok_set_region SEGS Ex ssx msx 4 r4 (set_window r4 0 24) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r4 0 24 (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E32u4; intros o Ho; apply (apresent_writable SEGS); apply HgP4; lia))) as HS5;
clear HS; rename HS5 into HS; norm_ss HS  end.
assert (Eptr1 : fr_ptr f1' = fr_ptr f1) by reflexivity.
set (sD := set_frames s2 [Some f1'; Some f2; None]).
set (sF := set_frames s2 [None; Some f1'; Some f2]).
assert (HsubQ : forall f, (Some f1' = Some f \/ Some f2 = Some f) -> In (Some f) (cg_frames s2)).
{ intros f Hf. rewrite Hfr2. cbn [In]. clear - Hf. tauto. }
assert (HwfD : cgif_wf sD N).
{ subst sD. unfold set_frames. apply (cgif_wf_intro s2 _ _ _ N HWF2); [reflexivity | | ].
- clear - HWF2. destruct HWF2 as (_ & _ & _ & _ & _ & _ & A6 & _). destruct A6 as [A6 | [A6 _]]; [left; exact A6 | right; split; [exact A6 | cbn; discriminate]].
- intros f Hf. apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF2))))))). apply HsubQ. cbn [In] in Hf. clear - Hf. destruct Hf as [H|[H|[H|H]]]; [tauto | tauto | discriminate H | destruct H]. }
assert (HwfF : cgif_wf sF N).
{ subst sF. unfold set_frames. apply (cgif_wf_intro s2 _ _ _ N HWF2); [reflexivity | | ].
- clear - HWF2. destruct HWF2 as (_ & _ & _ & _ & _ & _ & A6 & _). destruct A6 as [A6 | [A6 _]]; [left; exact A6 | right; split; [exact A6 | cbn; discriminate]].
- intros f Hf. apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF2))))))). apply HsubQ. cbn [In] in Hf. clear - Hf. destruct Hf as [H|[H|[H|H]]]; [discriminate H | tauto | tauto | destruct H]. }
assert (HokD : af_obj_ok s sD N) by (split; [exact HwfD | exact (proj2 HOK2)]).
assert (HokF : af_obj_ok s sF N) by (split; [exact HwfF | exact (proj2 HOK2)]).
assert (EBD : cgif_blocks g sD N ++ af_cblocks img N fattr lpa nlp rest = (g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest).
{ subst sD. rewrite cgif_blocks_set_frames, frames_blocks_3, frames_blocks_some, frames_blocks_some, frames_blocks_none, app_nil_r. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
assert (EBF : cgif_blocks g sF N ++ af_cblocks img N fattr lpa nlp rest = (g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest).
{ subst sF. rewrite cgif_blocks_set_frames, frames_blocks_3, frames_blocks_some, frames_blocks_some, frames_blocks_none. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
assert (HpermD : Permutation (ablocks B ly4 S4) (cgif_blocks g sD N ++ af_cblocks img N fattr lpa nlp rest)) by (rewrite EBD; exact HPerm4).
assert (HpermF : Permutation (ablocks B ly4 S4) (cgif_blocks g sF N ++ af_cblocks img N fattr lpa nlp rest)) by (rewrite EBF; exact HPerm4).
assert (HsubD : forall b, In b (cgif_blocks g sD N) -> In b (cgif_blocks g s N) \/ af_newtokX B ly S regs g s N b).
{ intros b Hb. apply Hnew. rewrite <- EBL2. apply (cgif_blocks_in_set_frames g s2 _ N b) in Hb; [exact Hb|].
intros f Hf. apply HsubQ. cbn [In] in Hf. clear - Hf. destruct Hf as [H|[H|[H|H]]]; [tauto | tauto | discriminate H | destruct H]. }
assert (HsubF : forall b, In b (cgif_blocks g sF N) -> In b (cgif_blocks g s N) \/ af_newtokX B ly S regs g s N b).
{ intros b Hb. apply Hnew. rewrite <- EBL2. apply (cgif_blocks_in_set_frames g s2 _ N b) in Hb; [exact Hb|].
intros f Hf. apply HsubQ. cbn [In] in Hf. clear - Hf. destruct Hf as [H|[H|[H|H]]]; [discriminate H | tauto | tauto | destruct H]. }
pose proof (af_side_sep B LAWS ly4 S4 W4 mem4 md4 g sD N _ ly sp0 (ZsW g sp0) HAR4 HpermD Hstk ltac:(intros a Ha; unfold ZsW in Ha; clear -Ha HTS; lia)) as [HZr4 HZf4].
assert (HBB4 : blocks_bytes S4 <= blocks_bytes S).
{ rewrite (blocks_bytes_bsum B ly4 S4), (bsum_perm _ _ HPerm4). eapply Z.le_trans; [|exact HBB].
rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPerm1), <- EBL2, (bsum_perm _ _ (Permutation_trans (Permutation_sym HPerm2s) HBL)), bsum_app.
enough (HH : 0 <= bsum match o0 with Some f => frame_blocks N f | None => [] end) by (clear - HH; lia).
apply bsum_nonneg. intros b Hb.
assert (Hbl : In b (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hb).
destruct b as [p n]. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hbl) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. clear - Hn. lia. }
assert (Hf2c : In (fr_ptr f2, FRAME_SIZE) (ablocks B ly4 S4)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]. right. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f2) FRAME_SIZE HAR4 Hf2c) as (_ & Hf24096 & Hf2ceil & _). change (req_size FRAME_SIZE) with 40 in Hf2ceil.
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ ZsW g sp0 a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W4) mem4 a) by (intros; reflexivity).
hei_havoc HS; paj_run_tok RUN HS HJ4 SHOK RBspanA.
{ awr_aX Usp4 E32u4 Hing4 HTS. }
kstep KK Usp4 E32u4.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
+
rewrite branch_eq_U in Hc. rewrite (U_atom E4 516 r E72_4) in Hc by (clear - Rr; lia). rewrite U_lit in Hc by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_eq _ _)) in Hc.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK RBspanA AF_D; [awr_aX Usp4 E32u4 Hing4 HTS |].
kstep KK Usp4 E32u4.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_pi_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR0, HR4 | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR0, HR4  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PD ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly4 S4 W4 rg mm mdq (k + EV_FLUSH + ev) sD 2 GPAL IMG LPAL gs gsF (YO07.mkS (Some F1) (Some F2) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) CX) end.
*
split; [exact HJ4|]. split; [clear - Hk0 Hev4 HEVF; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR4); intros a Ha; apply (mbyte_of_aview SEGS); apply KK; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | unfold ZsW; clear - Ha HZg Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ split; [|split].
-
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H W4) mem4) mF g LAY_CGIF 96 (xcgif_vals path hw pf s2) (xcgif_vals path hw pf sD) [0; 1; 2]%nat [(0, 24)] Ho4 lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros i Hi Hw; apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview SEGS); apply KK; [clear - Hi HZg; lia | unfold ZsW; clear - Hi Hw HZg Hgceil Hceil Hslo HTS C1; lia]. }
{ intros j f v' Hj Hf Hv'; cbn [In] in Hj.
destruct Hj as [<- | [<- | [<- | []]]]; cbn in Hf; injection Hf as <-; subst sD; rewrite (xcgif_vals_set_frames path hw pf) in Hv'; cbn [nth nth_error frame_ptr] in Hv'; injection Hv' as <-;
(split; [| cbn [snd]; first [clear - Hf4096 Hfceil C1; lia | clear - Hf24096 Hf2ceil C1; lia | clear; lia] ]); cbn [fst];
lazymatch type of HR4 with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch goal with |- val_mem _ _ (_ + ?off) _ ?v =>
apply (field_of_region Ex _ 32 g cs lo hi wlo whi off 8 _ v HR4 E32u4 ltac:(cbn; tauto));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [exact E34_4 | exact E35_4 | reflexivity]
| first [clear - Hf4096 Hfceil C1; cbn; lia | clear - Hf24096 Hf2ceil C1; cbn; lia | clear; cbn; lia] | cbn; lia ] end end. }
{ intros j Hj; subst sD; rewrite (xcgif_vals_set_frames path hw pf); destruct j as [|[|[|j]]]; [exfalso; apply Hj; cbn; tauto | exfalso; apply Hj; cbn; tauto | exfalso; apply Hj; cbn; tauto | reflexivity]. }
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr4 lay_inside_Raw). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZr4 i Hi) as [Hb Hn]. exact (KK _ Hb Hn).
- intros f Hf. subst sD. cbn [cg_frames set_frames In] in Hf.
assert (Hf' : f = f1' \/ f = f2) by (clear - Hf; destruct Hf as [H|[H|[H|H]]]; [left; injection H as ->; reflexivity | right; injection H as ->; reflexivity | discriminate H | destruct H]).
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf4 f Hf') lay_inside_Frame). intros i Hi. apply (mbyte_of_aview SEGS).
destruct (HZf4 f i ltac:(cbn [cg_frames set_frames In]; exact Hf) Hi) as [Hb Hn]. exact (KK _ Hb Hn). }
split; [exact HokD|]. split; [exact HpermD | exact HsubD].
* clear - Hk Hev4 HEVF; lia.
* exact HBB4.
* unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]]; regv2 HS EEo4 E32_4 E32u4 E38_4 E46_4 Rsp Rgp Rtp Hcfp HZg Hgceil C1.
* unfold af_s1_at; regv2 HS EEo4 E32_4 E32u4 E38_4 E46_4 Rsp Rgp Rtp Hcfp HZg Hgceil C1.
* regv2 HS EEo4 E32_4 E32u4 E38_4 E46_4 Rsp Rgp Rtp Hcfp HZg Hgceil C1.
* unfold af_locs; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; locv2 HR0 sp0 E32_4 E32u4 E38_4 E46_4 E67_4 Usp4 Hcfp HZg Hgceil C1 Rfattr.
* exact HnoTab.
* right; reflexivity.
* reflexivity.
* intros _; cbn; discriminate.
*
destruct (af_xfoot_unz B LAWS ly4 S4 W4 mem4 md4 g sD N (@nil (Z * Z)) _ ly sp0 (ZsW g sp0) HAR4 HpermD Hstk
ltac:(intros a [Ha | Ha]; [left; clear - Ha HTS; lia | right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]])) as [XZb5 XZi5].
pose proof (af_xq_unz B K AIL (w_H W4) mem4 _ md4 _ sD s2 N f1' f2 F1 F2 img lpa fattr nlp rest GPAL IMG LPAL _ _ KK XZb5 XZi5 Hpfr eq_refl eq_refl eq_refl
ltac:(subst sD; cbn [cg_frames set_frames]; left; reflexivity) ltac:(subst sD; cbn [cg_frames set_frames]; right; left; reflexivity) eq_refl eq_refl XQ4) as XQ5.
pose proof XCODE as XF. unfold af_xf in XF. destruct XF as (_ & (Xr0 & _) & Xrc2).
split; [| exact XM4].
rewrite XREST. replace (code =? YO07.C_OK) with true by (rewrite (proj1 Xr0 Hc); reflexivity).
exact (af_xq_d K _ _ s s2 N f1' f2 F1 F2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs code bytes (YO07.s_ihead gs) (YO07.s_cur gs) XQ5
ltac:(subst s2; cbn [flush_upd rw_cur]; rewrite Hrw; exact Xrc2) XHra XHih Hlenb).
+
rewrite branch_eq_U in Hc. rewrite (U_atom E4 516 r E72_4) in Hc by (clear - Rr; lia). rewrite U_lit in Hc by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_neq _ _)) in Hc.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK RBspanA AF_RETC; [awr_aX Usp4 E32u4 Hing4 HTS |].
kstep KK Usp4 E32u4.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR4 | st_ok _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
cbn [ms_mem restrict mkst] in HR4  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly4 S4 W4 rg mm mdq (k + EV_FLUSH + ev) sF (r mod 2 ^ 32) GPAL IMG LPAL gs gsF CX) end.
*
split; [exact HJ4|]. split; [clear - Hk0 Hev4 HEVF; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR4); intros a Ha; apply (mbyte_of_aview SEGS); apply KK; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | unfold ZsW; clear - Ha HZg Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ split; [|split].
- lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H W4) mem4) mF g LAY_CGIF 96 (xcgif_vals path hw pf s2) (xcgif_vals path hw pf sF) [0; 1; 2]%nat [(0, 24)] Ho4 lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros i Hi Hw; apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview SEGS); apply KK; [clear - Hi HZg; lia | unfold ZsW; clear - Hi Hw HZg Hgceil Hceil Hslo HTS C1; lia]. }
{ intros j f v' Hj Hf Hv'; cbn [In] in Hj.
destruct Hj as [<- | [<- | [<- | []]]]; cbn in Hf; injection Hf as <-; subst sF; rewrite (xcgif_vals_set_frames path hw pf) in Hv'; cbn [nth nth_error frame_ptr] in Hv'; injection Hv' as <-;
(split; [| cbn [snd]; first [clear - Hf4096 Hfceil C1; lia | clear - Hf24096 Hf2ceil C1; lia | clear; lia] ]); cbn [fst];
lazymatch type of HR4 with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch goal with |- val_mem _ _ (_ + ?off) _ ?v =>
apply (field_of_region Ex _ 32 g cs lo hi wlo whi off 8 _ v HR4 E32u4 ltac:(cbn; tauto));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [exact E34_4 | exact E35_4 | reflexivity]
| first [clear - Hf4096 Hfceil C1; cbn; lia | clear - Hf24096 Hf2ceil C1; cbn; lia | clear; cbn; lia] | cbn; lia ] end end. }
{ intros j Hj; subst sF; rewrite (xcgif_vals_set_frames path hw pf); destruct j as [|[|[|j]]]; [exfalso; apply Hj; cbn; tauto | exfalso; apply Hj; cbn; tauto | exfalso; apply Hj; cbn; tauto | reflexivity]. }
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr4 lay_inside_Raw). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZr4 i Hi) as [Hb Hn]. exact (KK _ Hb Hn).
- intros f Hf. subst sF. cbn [cg_frames set_frames In] in Hf.
assert (Hf' : f = f1' \/ f = f2) by (clear - Hf; destruct Hf as [H|[H|[H|H]]]; [discriminate H | left; injection H as ->; reflexivity | right; injection H as ->; reflexivity | destruct H]).
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf4 f Hf') lay_inside_Frame). intros i Hi. apply (mbyte_of_aview SEGS).
destruct (HZf4 f i ltac:(subst sD; cbn [cg_frames set_frames In]; clear - Hf'; destruct Hf' as [-> | ->]; tauto) Hi) as [Hb Hn]. exact (KK _ Hb Hn). }
split; [exact HokF|]. split; [exact HpermF | exact HsubF].
* clear - Hk Hev4 HEVF HEVA; lia.
* unfold af_regs_ret; change (spZ regs) with sp0.
split; [|split; [|split]]; regv2 HS EEo4 E32_4 E32u4 E38_4 E46_4 Rsp Rgp Rtp Hcfp HZg Hgceil C1.
*
let Q := fresh "Q" in prreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E72_4, unsigned_lit_small by (clear - Rr; lia); reflexivity.
*
destruct (af_xfoot_unz B LAWS ly4 S4 W4 mem4 md4 g sD N (@nil (Z * Z)) _ ly sp0 (ZsW g sp0) HAR4 HpermD Hstk
ltac:(intros a [Ha | Ha]; [left; clear - Ha HTS; lia | right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]])) as [XZb5 XZi5].
pose proof (af_xq_unz B K AIL (w_H W4) mem4 _ md4 _ sD s2 N f1' f2 F1 F2 img lpa fattr nlp rest GPAL IMG LPAL _ _ KK XZb5 XZi5 Hpfr eq_refl eq_refl eq_refl
ltac:(subst sD; cbn [cg_frames set_frames]; left; reflexivity) ltac:(subst sD; cbn [cg_frames set_frames]; right; left; reflexivity) eq_refl eq_refl XQ4) as XQ5.
pose proof XCODE as XF. unfold af_xf in XF. destruct XF as ((_ & Xc6 & Xbn) & (Xr0 & Xrv) & _).
pose proof XNUM as XF. unfold af_xf in XF. destruct XF as (XN1 & _ & _ & _ & XN1q).
assert (Xcn : code <> YO07.C_OK) by (intros E0; apply Hc; apply (proj2 Xr0); exact E0).
rewrite XREST. replace (code =? YO07.C_OK) with false by (symmetry; apply Z.eqb_neq; exact Xcn).
rewrite (Xbn Xcn), app_nil_r in XQ5.
exact (af_xq_retc K MT XN S S4 _ _ s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL gs code (YO07.s_ihead gs) (r mod 2 ^ 32) _ _ XQ5 Xrv Xcn (Xc6 Xcn) ltac:(clear - XN1; lia) XM4 XN1q XN1q). }
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
destruct o0 as [f0|].
-
pose proof ((proj2 (proj2 HT2')) f0 ltac:(rewrite Hfr2; left; reflexivity)) as Hof0.
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) (fr_lpal f0) Hof0 eq_refl eq_refl) as [Vlp Rlp].
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) (fr_img f0) Hof0 eq_refl eq_refl) as [Vim Rim].
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) (fr_attr f0) Hof0 eq_refl eq_refl) as [Vat Rat].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) (fr_nlp f0) Hof0 eq_refl eq_refl) as [_ Rnlp].
cbn [fst snd] in Vlp, Rlp, Vim, Rim, Vat, Rat, Rnlp. rewrite Z.add_0_r in Vlp.
change (N.to_nat 8) with 8%nat in Vlp, Vim. change (N.to_nat 4) with 4%nat in Vat.
assert (Hf0in : forall b, In b (frame_blocks N f0) -> In b (cgif_blocks g s1 N)).
{ intros b Hb. rewrite <- EBL2. unfold cgif_blocks. rewrite Hfr2. right. right. apply in_or_app. right. unfold frames_blocks. cbn [flat_map]. apply in_or_app. left. exact Hb. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS W2 rg mm _ TADDFRAME_STK sp0 (FPb g s N) ly S W mem md [] ly2 S2 mdq (k + EV_FLUSH) FF_STK
(ablocks_fp (ff_blocks (fr_ptr f0) (fr_img f0) (fr_lpal f0) (fr_attr f0) N (fr_nlp f0))) 3 (-224) (Z_to_bv 64 (BASE + 0xbbc)) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest) /\ mo_le MT S2 S3 (3 * mo_free MT)) HJ2 Psp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact P3' | exact P4' | exact P1 | apply ret_ok_codeptr_v; [clear; lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Ps0
| intros HPRE1; eapply SRr_mono;
[ eapply (pb_freeFrameX B MT LAWS TL MLAW AFREE4 W2 ly2 S2 rg mm _ [] (fr_ptr f0) (fr_lpal f0) (fr_img f0) (fr_attr f0) N (fr_nlp f0) _ HPRE1 HEV2);
[ exact P10' | exact Vlp | exact Vim | exact Vat | clear - Rlp; lia | clear - Rat; lia | exact HN0 | clear - Rnlp; lia
| exact HBL | exact HU1 | exact HU2 | exact HU3
|   pose proof XNUM as XF; unfold af_xf in XF; exact (af_xmtr_ok MT XN S S2 N (3 * mo_free MT) _ _ MLAW XMOK ltac:(clear - XF; lia) XM2 ltac:(unfold af_needF; clear - XF; lia)) ]
| cbv beta; unfold ff_postX; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa);
change (ff_blocks (fr_ptr f0) (fr_img f0) (fr_lpal f0) (fr_attr f0) N (fr_nlp f0)) with (frame_blocks N f0) in Hpn;
apply (af_fp_coverX B ly S regs g s N ly2 S2 (p, n) a); [apply Hnew; exact (Hf0in _ Hpn) | | cbn [fst snd]; exact Hpa];
eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hpn ]
| ] end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HPerm4 & XMLE4).
apply (CONT W4 ly4 S4 regs4 mem4 md4 3 _ ltac:(clear - PBASE PBLO; lia) HJ4 HJc4 HP4); [| exact HPerm4 | | exact XMLE4].
2: {   apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hpn.
assert (Hl : In (p, n) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hpn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hl) as (_ & Hp4096 & _). cbn [fst]. clear - Hp4096. lia. }
intros a Ha. destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa). exists p, n. split; [exact Hpn | exact Hpa].
-
cbn [app] in HBL.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS W2 rg mm _ TADDFRAME_STK sp0 (FPb g s N) ly S W mem md [] ly2 S2 mdq (k + EV_FLUSH) FF_STK [] 0 (-224)
(Z_to_bv 64 (BASE + 0xbbc)) [] (fun ly3 S3 W3 regs3 mem3 md3 => ly3 = ly2 /\ S3 = S2) HJ2 Psp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact P3' | exact P4' | exact P1 | apply ret_ok_codeptr_v; [clear; lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Ps0
| intros HPRE1; eapply SRr_mono;
[ apply (pb_freeFrame_null B LAWS W2 ly2 S2 rg mm _ [] HPRE1); exact P10'
| cbv beta; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & -> & ->).
apply (CONT W4 ly2 S2 regs4 mem4 md4 0 [] ltac:(clear - PBASE PBLO; lia) HJ4 HJc4 HP4); [| exact HBL | exact sink_closed_nil | pose proof XNUM as XF; unfold af_xf in XF; exact (mle_weaken MT S2 S2 0 (3 * mo_free MT) MLAW (mle_start MT S2 MLAW) ltac:(clear - XF; lia))].
intros a Ha. exfalso. exact (inFP_nil a Ha).
Qed.
End q.
End h.
End d.
