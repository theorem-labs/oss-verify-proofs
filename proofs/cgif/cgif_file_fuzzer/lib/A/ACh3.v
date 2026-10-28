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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC81 YC4b YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp AC8h ACh9 AChc ACh8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0c YC5d YC7z YC7x YC21 YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh7 ACh6 ACh4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Variable hw : Z.
Variable CTX : list (list Z).
Variable path pf : Z.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable XN : xnums.
Hypothesis HXF0 : forall N, 0 <= xn_flush XN N.
Hypothesis HXMF0 : forall N, 0 <= xm_flush XN N.
Hypothesis HXMF : forall N, xn_flush XN N + xm_flush XN N <= xm_close XN N.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Variable CTXfl : list (list Z).
Hypothesis HCTXfl : In [BASE + CL_RET_FLUSH] CTXfl.
Hypothesis FLUSHX : tflush_specX SEGS K B MT XN (BASE + A_flushFrame) CTXfl WFN_ADDR pa_relro_lo pa_relro_hi.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma xcgif_at_stretchXA : forall ly1 S1 (W1 : world SEGS) mem1 md1 (m' : word -> option byte) g s s1 N rest cur',
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (cgif_blocks g s N ++ rest) -> cl_obj_ok g s s1 N ->
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W1) mem1) g s1 ->
(forall a, 0 <= a < alloc_ceiling -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) mem1 a) ->
val_mem SEGS (mrestrict (w_H W1) m') (g + 88) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W1) m') g (cl_set_cur s1 cur').
Proof.
intros ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK (Hg & Hr & Hf) UN Vc Rc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cgif_blocks_obj_ok g s s1 N HOK) as EB. rewrite <- EB in HPerm.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly1 S1)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (_ & Hg4096 & Hgceil & _). change (req_size CGIF_SIZE) with 96 in Hgceil.
assert (HPerm' : Permutation (ablocks B ly1 S1) ((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1) ++ rest))
by (unfold cgif_blocks in HPerm; cbn [app] in HPerm; rewrite <- app_assoc in HPerm; exact HPerm).
assert (SEP : forall b n, In (b, n) ((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1) ++ rest) ->
4096 <= b /\ b + req_size n <= alloc_ceiling /\ (g + 96 <= b \/ b + req_size n <= g)).
{ intros b n Hbn.
assert (Hb : In (b, n) (ablocks B ly1 S1)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm'|]; right; exact Hbn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_hd_in B LAWS ly1 S1 W1 mem1 md1 (g, CGIF_SIZE) (b, n) _ HAR HPerm' Hbn) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D Hb4096 Hbceil. lia. }
split; [|split].
- apply (obj_cgif_setcurX SEGS path hw pf _ _ g s1 cur' Hg); [| exact Vc | exact Rc].
intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hg4096 Hgceil C1 C3; lia.
- cbn [cg_raw cl_set_cur]. change (traw_vals WFN_ADDR g (cl_set_cur s1 cur')) with (traw_vals WFN_ADDR g s1).
destruct (SEP (cg_raw s1) RAW_SIZE ltac:(left; reflexivity)) as (Hr4096 & Hrceil & Dgr). change (req_size RAW_SIZE) with 48 in Hrceil, Dgr.
apply (obj_at_kept _ _ (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgr Hr4096 Hrceil Hg4096 Hgceil C1 C3; lia.
- cbn [cg_frames cl_set_cur]. intros f Hin.
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s1))).
{ apply in_split in Hin as (l1 & l2 & El). rewrite El. unfold frames_blocks. rewrite flat_map_app. cbn [flat_map app].
apply in_or_app. right. left. reflexivity. }
destruct (SEP (fr_ptr f) FRAME_SIZE ltac:(right; apply in_or_app; right; apply in_or_app; left; exact Hfb)) as (Hf4096 & Hfceil & Dgf).
change (req_size FRAME_SIZE) with 40 in Hfceil, Dgf.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf Hf4096 Hfceil Hg4096 Hgceil C1 C3; lia.
Qed.
Lemma xcgif_at_stretchX : forall ly1 S1 (W1 : world SEGS) mem1 md1 (m' : word -> option byte) g s s1 N rest cur',
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (cgif_blocks g s N ++ rest) -> cl_obj_ok g s s1 N ->
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W1) mem1) g s1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) mem1 a) ->
val_mem SEGS (mrestrict (w_H W1) m') (g + 88) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W1) m') g (cl_set_cur s1 cur').
Proof.
intros ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK HT UN Vc Rc. pose proof asan_consts as (C1 & _).
apply (xcgif_at_stretchXA ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK HT); [| exact Vc | exact Rc].
intros a Ha Hna. apply UN; [clear - Ha C1; lia | exact Hna].
Qed.
Lemma regsIT_okX : forall (i : Z) (regs regs1 : bvmap 5 word) g s1,
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
getr regs1 18 = w64 (g + 8 * (i - 1)) -> getr regs1 21 = w64 (g + 8 * i) -> getr regs1 22 = w64 (SB + (g + 8 * i) / 8) -> getr regs1 23 = w64 (3 - i) ->
4096 <= g -> g + 96 <= alloc_ceiling ->     1 <= i <= 2 ->
regs_ok (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) (regsIT i) regs1.
Proof.
intros i regs regs1 g s1 (R2 & R3 & R4 & R9 & R8 & R19 & _) R20 R18 R21 R22 R23 Hlo Hhi Hi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))). assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia); first [exact R19 | exact R22]
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R9 | rewrite R18; unfold w64; f_equal; lia]
| rewrite E38; exact R20
| rewrite E32, unsigned_lit_small by lia; first [exact R8 | rewrite R18; unfold w64; f_equal; lia | rewrite R21; unfold w64; f_equal; lia]
| rewrite R23; unfold w64; f_equal; lia ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cl_IT2_okX : CL_B_stmtX B hw CTX path pf K MT XN -> CL_IT2_stmtX B hw CTX path pf K MT XN.
Proof.
intros CLB ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1 CX XE MID Hk Hcur HR R20 R18 R21 R22 R23 XO HGS HC1 X2.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof XO as (HSINK & MLE & HROOM & HGC).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R9 & R8 & R19 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity. assert (HTF : TFLUSH_STK = 17440) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
assert (Hinpf : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR Hinpf) as (_ & Hpf4096 & Hpfceil & _). change (req_size FILE_BLOCK) with 1264 in Hpfceil.
assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc g CGIF_SIZE pf FILE_BLOCK HAR Hing Hinpf ltac:(unfold CGIF_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
assert (HPerm1s : Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: rest)) by (rewrite (cgif_blocks_obj_ok g s s1 N HOK); exact HPerm1).
pose proof (obj_at_nth SEGS _ _ _ _ 8 (40, 4%N) (rw_cur s1) (proj1 (proj2 HT1)) eq_refl eq_refl) as [_ Rrc]. cbn [snd] in Rrc.
destruct (cl_seedX B LAWS TL hw path pf CL_IT (regsIT 2) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsIT_okX 2 regs regs1 g s1 HR R20 R18 R21 R22 R23 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s1 pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (EA : ew E 35 = Z_to_bv 64 (frame_ptr (nth 2 (cg_frames s1) None))) by (change 35%nat with (32 + (1 + 2))%nat; rewrite EXo by (clear; lia); reflexivity).
assert (EAm : ew E 34 = Z_to_bv 64 (frame_ptr (nth 1 (cg_frames s1) None))) by (change 34%nat with (32 + (1 + 1))%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_tok RUN HS HJ SHOK RBspanC.
all: try (awr_clX Usp E32u Hing HTS).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
assert (HEVF : EV_FLUSH = 35) by reflexivity.
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 2 (cg_frames s1) None) as [f|] eqn:Hfi.
{ exfalso. cbn [frame_ptr] in EA.
assert (HfI : nth_error (cg_frames s1) 2 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 2 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right.
apply (frames_blocks_in N (cg_frames s) 0 2 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
rewrite (U_atom E 35 (fr_ptr f) EA) in Hc by (clear - Hf4096 Hfceil C1; lia).
apply Z.eqb_eq in Hc. clear - Hc Hf4096. lia. }
cbn [frame_ptr] in EA.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_B.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20; prreg HS (18%bv : bv 5) Q18; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H Wc) m2 a = aview SEGS (w_H Wc) memc a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
assert (HVK : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) m2) s1 N)
by exact (cl_vkept_stretch B LAWS lyc Sc Wc memc mdc _ g s1 N _ HAR HPerm1s UN) end.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (xcgif_at_stretchX lyc Sc Wc memc mdc _ g s s1 N ((pf, FILE_BLOCK) :: rest) (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
assert (Hq2 : YO07.s_q2 gs = None) by (destruct X2 as (_ & _ & _ & _ & F2); rewrite Hfi in F2; destruct (YO07.s_q2 gs); [destruct F2 | reflexivity]).
pose proof (close_gif_none2 (gcfg_of s GPAL) gs HGS HC1 Hq2) as ECG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc rg mm mdq k (cl_set_cur s1 (cg_cur s1)) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s1 N _ HOK) | exact HPerm1].
+ clear - Hk HEVF. lia.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q20. exact E38.
+
split; [| split; [| split; [| exact HGC]]].
* rewrite ECG. apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ].
* apply (mle_weaken MT S Sc _ _ MLAW MLE). unfold cl_macc_b. pose proof (HXF0 N) as H0. clear - H0. lia.
* rewrite ECG. unfold FRAME_OUT in HROOM. clear - HROOM HN0. lia.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 2 (cg_frames s1) None) as [f|] eqn:Hfi.
2:{ exfalso. cbn [frame_ptr] in EA. rewrite (U_atom E 35 0 EA) in Hc by lia. cbn in Hc. discriminate Hc. }
cbn [frame_ptr] in EA. clear Hc.
assert (HfI : nth_error (cg_frames s1) 2 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 2 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfrin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s))).
{ apply (frames_blocks_in N (cg_frames s) 0 2 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Dgr : g + 96 <= cg_raw s \/ cg_raw s + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (cg_raw s, RAW_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D.
apply D. unfold cgif_blocks. left. reflexivity. }
paj_run_to_tok RUNTO HS HJ SHOK RBspanC A_flushFrame.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H Wc) m2 a = aview SEGS (w_H Wc) memc a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
assert (HVK : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) m2) s1 N)
by exact (cl_vkept_stretch B LAWS lyc Sc Wc memc mdc _ g s1 N _ HAR HPerm1s UN) end.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (xcgif_at_stretchX lyc Sc Wc memc mdc _ g s s1 N ((pf, FILE_BLOCK) :: rest) (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E32);
assert (Q11' : getr rg 11 = w64 (fr_ptr f)) by (rewrite Q11; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EA);
assert (Q12' : getr rg 12 = w64 (frame_ptr (nth 1 (cg_frames s1) None))) by (rewrite Q12; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EAm);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u, unsigned_lit_small by lia; clear - Hgceil; lia);
assert (Hctx1 : In (raZ rg :: spine []) CTXfl)
by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; cbn [spine]; exact HCTXfl);
assert (Htop' : spZ rg + 32 <= ly_top lyc) by (rewrite Qsp, Etopc; clear - Htop; lia);
assert (HROD' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) mm)) by (exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD));
assert (HEVc : st_nev Sc + EV_FLUSH <= EV_MAX) by (clear - Hnev Hk Hev Hk0 HEVF; lia)
end.
assert (Hfr7' : Z.of_nat (length (frames Sc)) <= 7) by (rewrite Hfrs; exact Hfr7).
assert (HLIVEc : blocks_bytes Sc + LIVE_FLUSH <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPerm1), <- (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B ly S). exact Hlive. }
assert (HPerm1' : Permutation (ablocks B lyc Sc) (cgif_blocks g (cl_set_cur s1 (cg_cur s1)) N ++ (pf, FILE_BLOCK) :: rest)).
{ rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)). exact HPerm1. }
destruct X2 as (X2rc & X2ra & X2gp & X2f1 & X2f2).
pose proof (oframe_relbA_vkept true _ _ s1 N 2 _ HVK X2f2) as FRc. rewrite Hfi in FRc.
destruct (YO07.s_q2 gs) as [cur2|] eqn:Hq2; [| destruct FRc]. cbn [oframe_relbA] in FRc.
pose proof (oframe_relbA_vkept false _ _ s1 N 1 _ HVK X2f1) as BEFc.
pose proof (gpal_vkept _ _ s1 N GPAL HVK X2gp) as GPALc.
pose proof X2ra as RATTR.
assert (HMOKf : mo_ok MT Sc (xm_flush XN N))
by (apply (mok_station MT S Sc (xm_close XN N) (xn_flush XN N) (xm_flush XN N) MLAW HMOK MLE (HXMF0 N) (HXMF N))).
assert (HROOMf : Z.of_nat (length (concat (YO07.s_out gs) ++ cl_bytes (gcfg_of s GPAL) (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs))) + FRAME_OUT N <= SINK_MAX) by (unfold FRAME_OUT in *; clear - HROOM HN0; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (HSINKc : asink_at SEGS K (mrestrict (w_H Wc) mm) mdq pf (concat (YO07.s_out gs) ++ cl_bytes (gcfg_of s GPAL) (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs)))
by (apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ]) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPcX g s N pf) ly S W mem md [] lyc Sc mdq k TFLUSH_STK
((fr_ptr f + 20, fr_ptr f + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) EV_FLUSH (-80) (Z_to_bv 64 (BASE + CL_RET_FLUSH)) []
(fun ly3 S3 W3 regs3 mem3 md3 => exists r gen' rwcur' : Z,
getr regs3 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W3) mem3) g (flush_upd (cl_set_cur s1 (cg_cur s1)) 2 gen' rwcur') /\
cgif_wf (flush_upd (cl_set_cur s1 (cg_cur s1)) 2 gen' rwcur') N /\
Permutation (ablocks B ly3 S3) (cgif_blocks g s N ++ (pf, FILE_BLOCK) :: rest) /\
(exists code bytes, YO07.flush_frame (gcfg_of s GPAL) (cl_rcur1 (gcfg_of s GPAL) gs) cur2 (YO07.s_q1 gs) = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
asink_at SEGS K (mrestrict (w_H W3) mem3) md3 pf ((concat (YO07.s_out gs) ++ cl_bytes (gcfg_of s GPAL) (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs)) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
mo_le MT Sc S3 (xn_flush XN N)) HJ Qsp);
[ reflexivity | lia | rewrite HTF; lia | rewrite HTS, HTF; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | unfold CL_RET_FLUSH; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (FLUSHX lyc Sc Wc rg mm _ [] g (cl_set_cur s1 (cg_cur s1)) N 2%nat f pf path hw rest (concat (YO07.s_out gs) ++ cl_bytes (gcfg_of s GPAL) (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs)) GPAL cur2 (YO07.s_q1 gs) HPRE1 Hctx1 Hfr7' Htop' HROD' Q10' HT' HWF1
Hpf0 ltac:(clear; lia) HfI Q11' Q12' HPerm1' HSINKc HROOMf GPALc FRc BEFc RATTR HEVc HLIVEc HMOKf)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP |]]];
destruct HK as (r & rwcur' & K1 & K2 & K3 & K4 & K5 & K6 & K7);
change (gcfg_of (cl_set_cur s1 (cg_cur s1)) GPAL) with (gcfg_of s1 GPAL) in K3, K4, K6; rewrite HGC in K3, K4, K6;
cbn [rw_cur cl_set_cur] in K6; rewrite X2rc in K6;
rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)) in K5;
exists r, (fl_gen3 (gcfg_of s GPAL) cur2 (YO07.s_q1 gs)), rwcur';
exact (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7)))))) ]
|
intros a Ha; left; destruct Ha as (rr & Hrr & Hrg); cbn [In] in Hrr;
destruct Hrr as [<- | [<- | Hrr]];
[ cbn [fst snd] in Hrg;
assert (Hq : inFP (FPc g s N) a)
by (unfold FPc; replace a with (fr_ptr f + (a - fr_ptr f)) by lia; apply (inFP_ablocks_fp _ (fr_ptr f) FRAME_SIZE (a - fr_ptr f)); [| change (req_size FRAME_SIZE) with 40; clear - Hrg; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; exact Hfrin);
destruct Hq as (r' & Hr' & Hrr'); exists r'; split; [unfold FPcX; apply in_or_app; left; exact Hr' | exact Hrr']
| cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg;
assert (Hq : inFP (FPc g s N) a)
by (unfold FPc; replace a with (cg_raw s + (a - cg_raw s)) by lia; apply (inFP_ablocks_fp _ (cg_raw s) RAW_SIZE (a - cg_raw s)); [| change (req_size RAW_SIZE) with 48; clear - Hrg; lia];
unfold cgif_blocks; right; left; reflexivity);
destruct Hq as (r' & Hr' & Hrr'); exists r'; split; [unfold FPcX; apply in_or_app; left; exact Hr' | exact Hrr']
| exists rr; split; [unfold FPcX; apply in_or_app; right; exact Hrr | exact Hrg] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hr10 & Rr & HT2 & HWF2 & HPerm2 & (code & bytes & FL & Ecode & Erw & HSINK2 & Hblen) & MLEc)).
subst rwcur'.
pose proof (proj1 HJ2) as HAR2.
set (s2 := flush_upd (cl_set_cur s1 (cg_cur s1)) 2 gen' (code mod 2 ^ 32)) in *.
assert (HOK2 : cl_obj_ok g s s2 N) by (exact (cl_obj_ok_flush g s _ N 2 gen' (code mod 2 ^ 32) (cl_obj_ok_setcur g s s1 N _ HOK) HWF2)).
assert (Hcur2 : cg_cur s2 = cg_cur s1) by reflexivity.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFg : forall a, g + 0 <= a < g + 96 -> ~ inFP ((fr_ptr f + 20, fr_ptr f + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) a).
{ intros a Ha (rr & Hrr & Hrg). cbn [In] in Hrr. destruct Hrr as [<- | [<- | Hrr]];
[cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; clear - Ha Hrg Dgf; lia | cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; clear - Ha Hrg Dgr; lia |].
assert (Hs : inFP (asink_fp pf) a) by (exists rr; split; [exact Hrr | exact Hrg]). apply in_asink_fp in Hs. unfold FILE_BLOCK in Hs. clear - Hs Ha Dgp Hg4096. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcellc & _ & Kgotc & _). rewrite HBgot, HBcell in Kgotc. rewrite HBcell in Kcellc.
jafter_call_keep_pi HS 52%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotc) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellc) | lia].
- eapply (region_kept_block_subw B LAWS); [exact HJc2 | exact E32u | exact Hing | exact Hing2 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | cbn; lia | cbn; unfold CGIF_SIZE; lia | intros a Ha HFP; exact (HnFg a Ha HFP)]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 52 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS. assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD2 : forall n, (n < 52)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 56 = Z_to_bv 64 r) by (rewrite HE2; change 56%nat with (52 + 4)%nat; rewrite (YN3v.ew_havoc_new E 52 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hr10).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 80) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 52)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn50; rewrite OLD2 by exact Hn50; exact (EEo n rr Hn)).
clear SHOK. assert (SHOK : sh_ok SEGS Bxc cl_SH E2 (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 Hing2).
- unfold U, Bxc. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
- lia.
- change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur2]. cbn [snd] in Rcur2.
assert (HFR2 : cl_frame SEGS (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (rewrite ?HTF; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia).
rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
assert (HPerm2s : Permutation (ablocks B ly2 S2) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: rest)) by (rewrite (cgif_blocks_obj_ok g s s1 N HOK); exact HPerm2).
lazymatch type of HVK with cl_vkept _ (mrestrict _ ?m2r) _ _ =>
assert (HVK2 : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) s1 N)
by (apply (cl_vkept_trans _ _ _ _ _ HVK);
exact (cl_vkept_flush B LAWS _ _ lyc Sc Wc m2r _ ly2 S2 W2 mem2 md2 _ g s1 N pf rest f (proj1 HJ) HJc2 HPerm1s HPerm2s (nth_error_In _ _ HfI))) end.
assert (Rcode : - 2 ^ 31 <= code < 2 ^ 31).
{ apply (flush_code_range _ _ _ _ _ _ FL). rewrite <- X2rc. exact (rc_int_range _ Rrc). }
assert (Hpf4096_2 := Hpf4096). assert (MLE2 : mo_le MT S S2 (xn_flush XN N + xn_flush XN N)) by exact (mle_station MT S Sc S2 _ _ MLAW MLE MLEc).
psrr_branch_tok RUN BR HS SHOK RBspanC.
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 56 r E2r) in Hc by (clear - Rr; lia).
assert (Hcode : code <> YO07.C_OK).
{ intros Ec. apply (proj2 (code_zero_iff r code Rr ltac:(clear - Rcode; lia) Ecode)) in Ec. subst r. cbn in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ2 SHOK RBspanC CL_B.
{ awr_clX Usp2 E32u2 Hing2 HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20; prreg HS (18%bv : bv 5) P18.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
set (cR := r mod 2 ^ 32).
pose proof (field_of_region_any E2 _ 32 g _ _ _ _ _ 88 4 (SOff 56 0) HRg3 E32u2 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vcur3.
cbn [sv_denot] in Vcur3. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E2r, unsigned_lit_small in Vcur3 by (clear - Rr; lia).
change (N.to_nat 4) with 4%nat in Vcur3. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vcur3. change (r mod 2 ^ 32) with cR in Vcur3.
assert (RcR : 0 <= cR < 2 ^ 32) by (subst cR; apply Z.mod_pos_bound; lia).
assert (HT3 : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W2) _) g (cl_set_cur s2 cR))
by (eapply (xcgif_at_stretchX ly2 S2 W2 mem2 md2 _ g s s2 N ((pf, FILE_BLOCK) :: rest) cR HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 RcR)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N aM rest GPAL gs ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 cR) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
*
split; [|split; [|split; [|split; [|split; [|split]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P9. rewrite ?OLD2 by lia; exact E32.
-- rewrite P8. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- intros r' Hr'.
assert (Hr4 : r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W2) E2 _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
* rewrite P20. rewrite ?OLD2 by lia. exact E38.
*
pose proof (close_gif_some2 (gcfg_of s GPAL) gs cur2 code bytes HGS HC1 Hq2 FL) as ECG.
split; [| split; [| split; [| exact HGC]]].
-- rewrite ECG. apply (asink_at_kept_mm SEGS K (mrestrict (w_H W2) mem2) _ md2 _ pf _); [| reflexivity | reflexivity | exact HSINK2];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN3;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ].
-- apply (mle_weaken MT S S2 _ _ MLAW MLE2). unfold cl_macc_b. clear. lia.
-- rewrite ECG, length_app, Nat2Z.inj_add. unfold FRAME_OUT in *. clear - HROOM Hblen HN0. lia.
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 56 r E2r) in Hc by (clear - Rr; lia).
assert (Hcode : code = YO07.C_OK).
{ apply (proj1 (code_zero_iff r code Rr ltac:(clear - Rcode; lia) Ecode)). destruct (Z.eqb_spec r 0) as [e|ne]; [exact e | cbn in Hc; discriminate Hc]. }
paj_run_to_tok RUNTO HS HJ2 SHOK RBspanC CL_B.
{ awr_clX Usp2 E32u2 Hing2 HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20; prreg HS (18%bv : bv 5) P18; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (23%bv : bv 5) P23.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
pose proof (field_of_region E2 _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg3 E32u2 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37_2) ltac:(clear - Rcur2; cbn; lia) ltac:(cbn; lia)) as Vcur3.
change (N.to_nat 4) with 4%nat in Vcur3.
assert (HT3 : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W2) _) g (cl_set_cur s2 (cg_cur s1)))
by (eapply (xcgif_at_stretchX ly2 S2 W2 mem2 md2 _ g s s2 N ((pf, FILE_BLOCK) :: rest) (cg_cur s1) HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 Rcur)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N aM rest GPAL gs ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 (cg_cur s1)) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
*
split; [|split; [|split; [|split; [|split; [|split]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P9. rewrite ?OLD2 by lia; exact E32.
-- rewrite P8. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- intros r' Hr'.
assert (Hr4 : r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W2) E2 _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
* rewrite P20. rewrite ?OLD2 by lia. exact E38.
*
pose proof (close_gif_some2 (gcfg_of s GPAL) gs cur2 code bytes HGS HC1 Hq2 FL) as ECG.
split; [| split; [| split; [| exact HGC]]].
-- rewrite ECG. apply (asink_at_kept_mm SEGS K (mrestrict (w_H W2) mem2) _ md2 _ pf _); [| reflexivity | reflexivity | exact HSINK2];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN3;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ].
-- apply (mle_weaken MT S S2 _ _ MLAW MLE2). unfold cl_macc_b. clear. lia.
-- rewrite ECG, length_app, Nat2Z.inj_add. unfold FRAME_OUT in *. clear - HROOM Hblen HN0. lia.
Qed.
Lemma cl_IT1_okX : CL_B_stmtX B hw CTX path pf K MT XN -> CL_IT2_stmtX B hw CTX path pf K MT XN -> CL_IT1_stmtX B hw CTX path pf K MT XN.
Proof.
intros CLB NXT ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1 CX XE MID Hk Hcur HR R20 R18 R21 R22 R23 XO HGS XL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof XO as (HSINK & MLE & HROOM & HGC).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R9 & R8 & R19 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity. assert (HTF : TFLUSH_STK = 17440) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
assert (Hinpf : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR Hinpf) as (_ & Hpf4096 & Hpfceil & _). change (req_size FILE_BLOCK) with 1264 in Hpfceil.
assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc g CGIF_SIZE pf FILE_BLOCK HAR Hing Hinpf ltac:(unfold CGIF_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
assert (HPerm1s : Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: rest)) by (rewrite (cgif_blocks_obj_ok g s s1 N HOK); exact HPerm1).
pose proof (obj_at_nth SEGS _ _ _ _ 8 (40, 4%N) (rw_cur s1) (proj1 (proj2 HT1)) eq_refl eq_refl) as [_ Rrc]. cbn [snd] in Rrc.
destruct (cl_seedX B LAWS TL hw path pf CL_IT (regsIT 1) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsIT_okX 1 regs regs1 g s1 HR R20 R18 R21 R22 R23 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s1 pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (EA : ew E 34 = Z_to_bv 64 (frame_ptr (nth 1 (cg_frames s1) None))) by (change 34%nat with (32 + (1 + 1))%nat; rewrite EXo by (clear; lia); reflexivity).
assert (EAm : ew E 33 = Z_to_bv 64 (frame_ptr (nth 0 (cg_frames s1) None))) by (change 33%nat with (32 + (1 + 0))%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_tok RUN HS HJ SHOK RBspanC.
all: try (awr_clX Usp E32u Hing HTS).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
assert (HEVF : EV_FLUSH = 35) by reflexivity.
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 1 (cg_frames s1) None) as [f|] eqn:Hfi.
{ exfalso. cbn [frame_ptr] in EA.
assert (HfI : nth_error (cg_frames s1) 1 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 1 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right.
apply (frames_blocks_in N (cg_frames s) 0 1 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
rewrite (U_atom E 34 (fr_ptr f) EA) in Hc by (clear - Hf4096 Hfceil C1; lia).
apply Z.eqb_eq in Hc. clear - Hc Hf4096. lia. }
cbn [frame_ptr] in EA.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_IT.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20; prreg HS (18%bv : bv 5) Q18; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (10%bv : bv 5) Q10.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H Wc) m2 a = aview SEGS (w_H Wc) memc a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
assert (HVK : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) m2) s1 N)
by exact (cl_vkept_stretch B LAWS lyc Sc Wc memc mdc _ g s1 N _ HAR HPerm1s UN) end.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (xcgif_at_stretchX lyc Sc Wc memc mdc _ g s s1 N ((pf, FILE_BLOCK) :: rest) (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
lazymatch type of HVK with cl_vkept _ ?m2r _ _ =>
destruct (cl_x2_of_null1 (mrestrict (w_H Wc) memc) m2r s s1 N GPAL gs (cg_cur s1) Hfi HGC XL HVK) as [Hq1 X2n] end.
destruct (cl_slot1_none (gcfg_of s GPAL) gs Hq1) as (Eb1 & Ec1 & Er1).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (NXT ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc rg mm mdq k (cl_set_cur s1 (cg_cur s1)) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s1 N _ HOK) | exact HPerm1].
+ clear - Hk HEVF. lia.
+ cbn [cg_cur cl_set_cur]. exact Hcur.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q20. exact E38.
+ rewrite Q18. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q21. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q22, E32u, E38, cl_shx_incX by (clear - Hgceil Hg4096 C1; lia). unfold w64. f_equal. replace (g + 8 * 2) with ((g + 8) + 1 * 8) by lia. rewrite Z.div_add by lia. lia.
+ rewrite Q23. apply bv_eq. vm_compute. reflexivity.
+
split; [| split; [| split; [| exact HGC]]].
* rewrite Eb1, app_nil_r. apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ].
* apply (mle_weaken MT S Sc _ _ MLAW MLE). exact (HXF0 N).
* rewrite Eb1, app_nil_r. unfold CLOSE_OUT, FRAME_OUT in *. clear - HROOM HN0. lia.
+ exact HGS.
+ exact Ec1.
+ exact X2n.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 1 (cg_frames s1) None) as [f|] eqn:Hfi.
2:{ exfalso. cbn [frame_ptr] in EA. rewrite (U_atom E 34 0 EA) in Hc by lia. cbn in Hc. discriminate Hc. }
cbn [frame_ptr] in EA. clear Hc.
assert (HfI : nth_error (cg_frames s1) 1 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 1 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfrin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s))).
{ apply (frames_blocks_in N (cg_frames s) 0 1 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Dgr : g + 96 <= cg_raw s \/ cg_raw s + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (cg_raw s, RAW_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D.
apply D. unfold cgif_blocks. left. reflexivity. }
paj_run_to_tok RUNTO HS HJ SHOK RBspanC A_flushFrame.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H Wc) m2 a = aview SEGS (w_H Wc) memc a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
assert (HVK : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) m2) s1 N)
by exact (cl_vkept_stretch B LAWS lyc Sc Wc memc mdc _ g s1 N _ HAR HPerm1s UN) end.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (xcgif_at_stretchX lyc Sc Wc memc mdc _ g s s1 N ((pf, FILE_BLOCK) :: rest) (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E32);
assert (Q11' : getr rg 11 = w64 (fr_ptr f)) by (rewrite Q11; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EA);
assert (Q12' : getr rg 12 = w64 (frame_ptr (nth 0 (cg_frames s1) None))) by (rewrite Q12; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EAm);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u, unsigned_lit_small by lia; clear - Hgceil; lia);
assert (Hctx1 : In (raZ rg :: spine []) CTXfl)
by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; cbn [spine]; exact HCTXfl);
assert (Htop' : spZ rg + 32 <= ly_top lyc) by (rewrite Qsp, Etopc; clear - Htop; lia);
assert (HROD' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) mm)) by (exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD));
assert (HEVc : st_nev Sc + EV_FLUSH <= EV_MAX) by (clear - Hnev Hk Hev Hk0 HEVF; lia)
end.
assert (Hfr7' : Z.of_nat (length (frames Sc)) <= 7) by (rewrite Hfrs; exact Hfr7).
assert (HLIVEc : blocks_bytes Sc + LIVE_FLUSH <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPerm1), <- (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B ly S). exact Hlive. }
assert (HPerm1' : Permutation (ablocks B lyc Sc) (cgif_blocks g (cl_set_cur s1 (cg_cur s1)) N ++ (pf, FILE_BLOCK) :: rest)).
{ rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)). exact HPerm1. }
pose proof (af_xlive_vkept _ _ s1 N GPAL gs HVK XL) as (L1 & RATTR & L3 & GPALc & BEFc & FRc & LF2).
rewrite Hfi in FRc. destruct (YO07.s_q1 gs) as [cur1|] eqn:Hq1; [| destruct FRc]. cbn [oframe_relbA] in FRc.
assert (HMOKf : mo_ok MT Sc (xm_flush XN N)).
{ apply (mok_station MT S Sc (xm_close XN N) 0 (xm_flush XN N) MLAW HMOK MLE (HXMF0 N)). pose proof (HXMF N) as Hx. pose proof (HXF0 N) as H0. clear - Hx H0. lia. }
assert (HROOMf : Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX) by (unfold CLOSE_OUT, FRAME_OUT in *; clear - HROOM HN0; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (HSINKc : asink_at SEGS K (mrestrict (w_H Wc) mm) mdq pf (concat (YO07.s_out gs)))
by (apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ]) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPcX g s N pf) ly S W mem md [] lyc Sc mdq k TFLUSH_STK
((fr_ptr f + 20, fr_ptr f + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) EV_FLUSH (-80) (Z_to_bv 64 (BASE + CL_RET_FLUSH)) []
(fun ly3 S3 W3 regs3 mem3 md3 => exists r gen' rwcur' : Z,
getr regs3 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W3) mem3) g (flush_upd (cl_set_cur s1 (cg_cur s1)) 1 gen' rwcur') /\
cgif_wf (flush_upd (cl_set_cur s1 (cg_cur s1)) 1 gen' rwcur') N /\
Permutation (ablocks B ly3 S3) (cgif_blocks g s N ++ (pf, FILE_BLOCK) :: rest) /\
(exists code bytes, YO07.flush_frame (gcfg_of s GPAL) (YO07.s_rcur gs) cur1 (YO07.s_q0 gs) = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
asink_at SEGS K (mrestrict (w_H W3) mem3) md3 pf ((concat (YO07.s_out gs)) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
mo_le MT Sc S3 (xn_flush XN N)) HJ Qsp);
[ reflexivity | lia | rewrite HTF; lia | rewrite HTS, HTF; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | unfold CL_RET_FLUSH; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (FLUSHX lyc Sc Wc rg mm _ [] g (cl_set_cur s1 (cg_cur s1)) N 1%nat f pf path hw rest (concat (YO07.s_out gs)) GPAL cur1 (YO07.s_q0 gs) HPRE1 Hctx1 Hfr7' Htop' HROD' Q10' HT' HWF1
Hpf0 ltac:(clear; lia) HfI Q11' Q12' HPerm1' HSINKc HROOMf GPALc FRc BEFc RATTR HEVc HLIVEc HMOKf)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP |]]];
destruct HK as (r & rwcur' & K1 & K2 & K3 & K4 & K5 & K6 & K7);
change (gcfg_of (cl_set_cur s1 (cg_cur s1)) GPAL) with (gcfg_of s1 GPAL) in K3, K4, K6; rewrite HGC in K3, K4, K6;
cbn [rw_cur cl_set_cur] in K6; rewrite L1 in K6;
rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)) in K5;
exists r, (fl_gen3 (gcfg_of s GPAL) cur1 (YO07.s_q0 gs)), rwcur';
exact (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7)))))) ]
|
intros a Ha; left; destruct Ha as (rr & Hrr & Hrg); cbn [In] in Hrr;
destruct Hrr as [<- | [<- | Hrr]];
[ cbn [fst snd] in Hrg;
assert (Hq : inFP (FPc g s N) a)
by (unfold FPc; replace a with (fr_ptr f + (a - fr_ptr f)) by lia; apply (inFP_ablocks_fp _ (fr_ptr f) FRAME_SIZE (a - fr_ptr f)); [| change (req_size FRAME_SIZE) with 40; clear - Hrg; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; exact Hfrin);
destruct Hq as (r' & Hr' & Hrr'); exists r'; split; [unfold FPcX; apply in_or_app; left; exact Hr' | exact Hrr']
| cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg;
assert (Hq : inFP (FPc g s N) a)
by (unfold FPc; replace a with (cg_raw s + (a - cg_raw s)) by lia; apply (inFP_ablocks_fp _ (cg_raw s) RAW_SIZE (a - cg_raw s)); [| change (req_size RAW_SIZE) with 48; clear - Hrg; lia];
unfold cgif_blocks; right; left; reflexivity);
destruct Hq as (r' & Hr' & Hrr'); exists r'; split; [unfold FPcX; apply in_or_app; left; exact Hr' | exact Hrr']
| exists rr; split; [unfold FPcX; apply in_or_app; right; exact Hrr | exact Hrg] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hr10 & Rr & HT2 & HWF2 & HPerm2 & (code & bytes & FL & Ecode & Erw & HSINK2 & Hblen) & MLEc)).
subst rwcur'.
pose proof (proj1 HJ2) as HAR2.
set (s2 := flush_upd (cl_set_cur s1 (cg_cur s1)) 1 gen' (code mod 2 ^ 32)) in *.
assert (HOK2 : cl_obj_ok g s s2 N) by (exact (cl_obj_ok_flush g s _ N 1 gen' (code mod 2 ^ 32) (cl_obj_ok_setcur g s s1 N _ HOK) HWF2)).
assert (Hcur2 : cg_cur s2 = cg_cur s1) by reflexivity.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFg : forall a, g + 0 <= a < g + 96 -> ~ inFP ((fr_ptr f + 20, fr_ptr f + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) a).
{ intros a Ha (rr & Hrr & Hrg). cbn [In] in Hrr. destruct Hrr as [<- | [<- | Hrr]];
[cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; clear - Ha Hrg Dgf; lia | cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; clear - Ha Hrg Dgr; lia |].
assert (Hs : inFP (asink_fp pf) a) by (exists rr; split; [exact Hrr | exact Hrg]). apply in_asink_fp in Hs. unfold FILE_BLOCK in Hs. clear - Hs Ha Dgp Hg4096. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcellc & _ & Kgotc & _). rewrite HBgot, HBcell in Kgotc. rewrite HBcell in Kcellc.
jafter_call_keep_pi HS 52%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotc) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellc) | lia].
- eapply (region_kept_block_subw B LAWS); [exact HJc2 | exact E32u | exact Hing | exact Hing2 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | cbn; lia | cbn; unfold CGIF_SIZE; lia | intros a Ha HFP; exact (HnFg a Ha HFP)]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 52 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS. assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD2 : forall n, (n < 52)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 56 = Z_to_bv 64 r) by (rewrite HE2; change 56%nat with (52 + 4)%nat; rewrite (YN3v.ew_havoc_new E 52 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hr10).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 80) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 52)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn50; rewrite OLD2 by exact Hn50; exact (EEo n rr Hn)).
clear SHOK. assert (SHOK : sh_ok SEGS Bxc cl_SH E2 (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 Hing2).
- unfold U, Bxc. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
- lia.
- change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur2]. cbn [snd] in Rcur2.
assert (HFR2 : cl_frame SEGS (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (rewrite ?HTF; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia).
rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
assert (HPerm2s : Permutation (ablocks B ly2 S2) (cgif_blocks g s1 N ++ (pf, FILE_BLOCK) :: rest)) by (rewrite (cgif_blocks_obj_ok g s s1 N HOK); exact HPerm2).
lazymatch type of HVK with cl_vkept _ (mrestrict _ ?m2r) _ _ =>
assert (HVK2 : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) s1 N)
by (apply (cl_vkept_trans _ _ _ _ _ HVK);
exact (cl_vkept_flush B LAWS _ _ lyc Sc Wc m2r _ ly2 S2 W2 mem2 md2 _ g s1 N pf rest f (proj1 HJ) HJc2 HPerm1s HPerm2s (nth_error_In _ _ HfI))) end.
assert (Rcode : - 2 ^ 31 <= code < 2 ^ 31).
{ apply (flush_code_range _ _ _ _ _ _ FL). rewrite <- L1. exact (rc_int_range _ Rrc). }
assert (Hpf4096_2 := Hpf4096). assert (MLE2 : mo_le MT S S2 (0 + xn_flush XN N)) by exact (mle_station MT S Sc S2 _ _ MLAW MLE MLEc).
psrr_branch_tok RUN BR HS SHOK RBspanC.
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 56 r E2r) in Hc by (clear - Rr; lia).
assert (Hcode : code <> YO07.C_OK).
{ intros Ec. apply (proj2 (code_zero_iff r code Rr ltac:(clear - Rcode; lia) Ecode)) in Ec. subst r. cbn in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ2 SHOK RBspanC CL_B.
{ awr_clX Usp2 E32u2 Hing2 HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20; prreg HS (18%bv : bv 5) P18.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
set (cR := r mod 2 ^ 32).
pose proof (field_of_region_any E2 _ 32 g _ _ _ _ _ 88 4 (SOff 56 0) HRg3 E32u2 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vcur3.
cbn [sv_denot] in Vcur3. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E2r, unsigned_lit_small in Vcur3 by (clear - Rr; lia).
change (N.to_nat 4) with 4%nat in Vcur3. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vcur3. change (r mod 2 ^ 32) with cR in Vcur3.
assert (RcR : 0 <= cR < 2 ^ 32) by (subst cR; apply Z.mod_pos_bound; lia).
assert (HT3 : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W2) _) g (cl_set_cur s2 cR))
by (eapply (xcgif_at_stretchX ly2 S2 W2 mem2 md2 _ g s s2 N ((pf, FILE_BLOCK) :: rest) cR HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 RcR)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N aM rest GPAL gs ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 cR) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
*
split; [|split; [|split; [|split; [|split; [|split]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P9. rewrite ?OLD2 by lia; exact E32.
-- rewrite P8. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- intros r' Hr'.
assert (Hr4 : r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W2) E2 _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
* rewrite P20. rewrite ?OLD2 by lia. exact E38.
*
destruct (cl_slot1_some (gcfg_of s GPAL) gs cur1 code bytes Hq1 FL) as (Eb1 & Ec1 & Er1).
pose proof (close_gif_fail1 (gcfg_of s GPAL) gs HGS ltac:(rewrite Ec1; exact Hcode)) as ECG. rewrite Eb1 in ECG.
split; [| split; [| split; [| exact HGC]]].
-- rewrite ECG. apply (asink_at_kept_mm SEGS K (mrestrict (w_H W2) mem2) _ md2 _ pf _); [| reflexivity | reflexivity | exact HSINK2];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN3;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ].
-- apply (mle_weaken MT S S2 _ _ MLAW MLE2). unfold cl_macc_b. pose proof (HXF0 N) as H0. clear - H0. lia.
-- rewrite ECG, length_app, Nat2Z.inj_add. unfold CLOSE_OUT, FRAME_OUT in *. clear - HROOM Hblen HN0. lia.
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 56 r E2r) in Hc by (clear - Rr; lia).
assert (Hcode : code = YO07.C_OK).
{ apply (proj1 (code_zero_iff r code Rr ltac:(clear - Rcode; lia) Ecode)). destruct (Z.eqb_spec r 0) as [e|ne]; [exact e | cbn in Hc; discriminate Hc]. }
paj_run_to_tok RUNTO HS HJ2 SHOK RBspanC CL_IT.
{ awr_clX Usp2 E32u2 Hing2 HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20; prreg HS (18%bv : bv 5) P18; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (23%bv : bv 5) P23; prreg HS (10%bv : bv 5) P10.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
pose proof (field_of_region E2 _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg3 E32u2 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37_2) ltac:(clear - Rcur2; cbn; lia) ltac:(cbn; lia)) as Vcur3.
change (N.to_nat 4) with 4%nat in Vcur3.
assert (HT3 : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W2) _) g (cl_set_cur s2 (cg_cur s1)))
by (eapply (xcgif_at_stretchX ly2 S2 W2 mem2 md2 _ g s s2 N ((pf, FILE_BLOCK) :: rest) (cg_cur s1) HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 Rcur)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (NXT ly S W regs mem md ch g s N aM rest GPAL gs ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 (cg_cur s1)) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
* cbn [cg_cur cl_set_cur]. exact Hcur.
*
split; [|split; [|split; [|split; [|split; [|split]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P9. rewrite ?OLD2 by lia; exact E32.
-- rewrite P8. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- intros r' Hr'.
assert (Hr4 : r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W2) E2 _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
* rewrite P20. rewrite ?OLD2 by lia. exact E38.
* rewrite P18. cbn [sv_denot]. rewrite ?OLD2 by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
* rewrite P21. cbn [sv_denot]. rewrite ?OLD2 by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
* rewrite P22. rewrite ?OLD2 by lia. rewrite E32u, E38, cl_shx_incX by (clear - Hgceil Hg4096 C1; lia). unfold w64. f_equal. replace (g + 8 * 2) with ((g + 8) + 1 * 8) by lia. rewrite Z.div_add by lia. lia.
* rewrite P23. apply bv_eq. vm_compute. reflexivity.
*
destruct (cl_slot1_some (gcfg_of s GPAL) gs cur1 code bytes Hq1 FL) as (Eb1 & Ec1 & Er1).
split; [| split; [| split; [| exact HGC]]].
-- rewrite Eb1. apply (asink_at_kept_mm SEGS K (mrestrict (w_H W2) mem2) _ md2 _ pf _); [| reflexivity | reflexivity | exact HSINK2];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN3;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi; lia ].
-- apply (mle_weaken MT S S2 _ _ MLAW MLE2). clear. lia.
-- rewrite Eb1, length_app, Nat2Z.inj_add. unfold CLOSE_OUT, FRAME_OUT in *. clear - HROOM Hblen HN0. lia.
* exact HGS.
* rewrite (proj1 (proj2 (cl_slot1_some (gcfg_of s GPAL) gs cur1 code bytes Hq1 FL))). exact Hcode.
*
lazymatch goal with |- cl_x2 (mrestrict _ ?m3) _ _ _ _ _ =>
assert (HVK3 : cl_vkept (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) m3) s1 N)
by (apply (cl_vkept_trans _ _ _ _ _ HVK2); exact (cl_vkept_stretch B LAWS ly2 S2 W2 mem2 md2 _ g s1 N _ HAR2 HPerm2s UN3)) end.
exact (cl_x2_of_flush1 _ _ s s1 N GPAL gs f cur1 gen' code bytes (cg_cur s1) (cg_cur s1) Hlen1 Hfi HGC XL HVK3 Rrc Hq1 FL).
Qed.
Theorem cl_IT1X : CL_B_stmtX B hw CTX path pf K MT XN -> CL_IT1_stmtX B hw CTX path pf K MT XN.
Proof. intros HB. exact (cl_IT1_okX HB (cl_IT2_okX HB)). Qed.
End h.
End d.
End c.
