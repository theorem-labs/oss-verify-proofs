(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC81 YC4b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCjp.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8h.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCh9 YChc YCha.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Definition cl_set_cur (s1 : cgif_st) (c : Z) : cgif_st :=
mkCgif (cg_frames s1) (cg_pal s1) (cg_attr s1) (cg_gen s1) (cg_W s1) (cg_H s1) (cg_ngp s1) (cg_loops s1) (cg_raw s1) c (cg_ihead s1)
(rw_gct s1) (rw_attr s1) (rw_loops s1) (rw_cur s1).
Lemma tcgif_vals_set_cur_nth : forall {hw : Z} s1 c j, j <> 15%nat -> nth_error (tcgif_vals hw (cl_set_cur s1 c)) j = nth_error (tcgif_vals hw s1) j.
Proof.
intros hw s1 c j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; lia] |]). reflexivity.
Qed.
Lemma obj_cgif_setcur : forall {hw : Z} (m m' : word -> option byte) g s1 c,
obj_at SEGS m g LAY_CGIF (tcgif_vals hw s1) ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS m' (g + i) = mbyte SEGS m (g + i)) ->
val_mem SEGS m' (g + 88) 4 c -> 0 <= c < 2 ^ 32 ->
obj_at SEGS m' g LAY_CGIF (tcgif_vals hw (cl_set_cur s1 c)).
Proof.
intros hw m m' g s1 c HO HK Vc Rc.
apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct (Nat.eq_dec j 15) as [-> | Hne].
- cbn in Hf. injection Hf as <-. cbn in Hv. injection Hv as <-. split; [exact Vc | cbn; lia].
- rewrite (tcgif_vals_set_cur_nth s1 c j Hne) in Hv.
pose proof (obj_at_nth SEGS _ _ _ _ j f v HO Hf Hv) as [V R]. split; [|exact R].
assert (HIN : In f LAY_CGIF) by (eapply nth_error_In; exact Hf).
assert (Hoff : 0 <= fst f /\ fst f + Z.of_N (snd f) <= 96 /\ (fst f + Z.of_N (snd f) <= 88 \/ 92 <= fst f)).
{ assert (Hj : (j < 17)%nat) by (apply (proj1 (nth_error_Some LAY_CGIF j)); rewrite Hf; discriminate).
do 17 (destruct j as [|j]; [cbn in Hf; injection Hf as <-; cbn; lia|]). lia. }
intros kk Hkk. rewrite <- (V kk Hkk). pose proof (N_nat_Z (snd f)).
replace (g + fst f + Z.of_nat kk) with (g + (fst f + Z.of_nat kk)) by lia. apply HK; lia.
Qed.
Lemma denot_shx' : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hc0 Hc Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))))). f_equal.
change (U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (YP0m.zcanon_small (v + c)) by lia. rewrite (YP0m.zcanon_small ((v + c) / 8)) by lia. rewrite (YP0m.zcanon_small sb) by lia. rewrite YP0m.zcanon_small by lia. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Variable hw : Z.
Variable CTX : list (list Z).
Hypothesis HUfc : In [pc_free_ra0 (as_code B); BASE + 0x76c] (as_universe B).
Hypothesis HUff1 : In [pc_free_ra0 (as_code B); BASE + 0x2e1c] (as_universe B).
Hypothesis HUff2 : In [pc_free_ra0 (as_code B); BASE + 0x2e54] (as_universe B).
Hypothesis HUrfc : In [pc_free_ra0 (as_code B); BASE + CL_RET_FREECGIF] (as_universe B).
Hypothesis HUrff : In [pc_free_ra0 (as_code B); BASE + CL_RET_FREEFRAME] (as_universe B).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Variable rctrace : list Z.
Hypothesis HUrc : In rctrace (as_universe B).
Hypothesis RAWCLOSE : trawclose_spec SEGS B (SIGMA AS_cgif_raw_close) rctrace WFN_ADDR hw.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Definition CL_RC_stmt : Prop :=
forall ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1,
cl_cx B hw CTX ly S W regs mem md ch g s N rest ->
cl_mid B (tcgif_atI hw 0) ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (fr_blocks g s N 0) -> k <= 2 * EV_FLUSH + 1 ->
cl_regs_at B regs regs1 g ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_RET_RAWCLOSE)) memc (seg_rom SEGS)) mdc) (cl_post B ly S W regs mem md g s N rest (k + 15)).
Lemma frames_blocks_map : forall N (fs fs' : list (option frame_st)),
map (option_map (frame_blocks N)) fs = map (option_map (frame_blocks N)) fs' -> frames_blocks N fs = frames_blocks N fs'.
Proof.
intros N fs. induction fs as [|o fs IH]; intros [|o' fs'] H; cbn [map] in H; try discriminate; [reflexivity|].
injection H as Ho Hfs.
change (frames_blocks N (o :: fs)) with (match o with Some f => frame_blocks N f | None => [] end ++ frames_blocks N fs).
change (frames_blocks N (o' :: fs')) with (match o' with Some f => frame_blocks N f | None => [] end ++ frames_blocks N fs').
rewrite (IH fs' Hfs). f_equal.
pose proof (f_equal (fun x : option (list (Z * Z)) => match x with Some l => l | None => [] end) Ho) as Ho'. cbn beta iota in Ho'.
destruct o as [f|], o' as [f'|]; cbn [option_map] in Ho'; exact Ho'.
Qed.
Lemma cgif_blocks_obj_ok : forall g s s1 N, cl_obj_ok g s s1 N -> cgif_blocks g s1 N = cgif_blocks g s N.
Proof.
intros g s s1 N (_ & Hraw & Hattr & Hpal & Hngp & Hfrm). unfold cgif_blocks, pal_blocks.
rewrite Hraw, Hattr, Hpal, Hngp, (frames_blocks_map N _ _ Hfrm). reflexivity.
Qed.
Lemma cl_obj_ok_setcur : forall g s s1 N c, cl_obj_ok g s s1 N -> cl_obj_ok g s (cl_set_cur s1 c) N.
Proof. intros g s s1 N c H. exact H. Qed.
Lemma cl_obj_ok_flush : forall g s s1 N i gen' rwcur',
cl_obj_ok g s s1 N -> cgif_wf (flush_upd s1 i gen' rwcur') N -> cl_obj_ok g s (flush_upd s1 i gen' rwcur') N.
Proof.
intros g s s1 N i gen' rwcur' (HWF1 & Hraw & Hattr & Hpal & Hngp & Hfrm) HWF'. split; [exact HWF'|].
cbn [cg_raw cg_attr cg_pal cg_ngp cg_frames flush_upd]. split; [exact Hraw|]. split; [exact Hattr|]. split; [exact Hpal|]. split; [exact Hngp|].
rewrite <- Hfrm. generalize (cg_frames s1) as fs. clear. induction i as [|i IH]; intros [|o fs]; cbn; [reflexivity| |reflexivity|].
- f_equal. destruct o; reflexivity.
- f_equal. apply IH.
Qed.
Lemma tcgif_at_stretchA : forall ly1 S1 (W1 : world SEGS) mem1 md1 (m' : word -> option byte) g s s1 N rest cur',
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (cgif_blocks g s N ++ rest) -> cl_obj_ok g s s1 N ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) mem1) g s1 ->
(forall a, 0 <= a < alloc_ceiling -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) mem1 a) ->
val_mem SEGS (mrestrict (w_H W1) m') (g + 88) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) m') g (cl_set_cur s1 cur').
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
- apply (obj_cgif_setcur _ _ g s1 cur' Hg); [| exact Vc | exact Rc].
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
Lemma tcgif_at_stretch : forall ly1 S1 (W1 : world SEGS) mem1 md1 (m' : word -> option byte) g s s1 N rest cur',
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (cgif_blocks g s N ++ rest) -> cl_obj_ok g s s1 N ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) mem1) g s1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) mem1 a) ->
val_mem SEGS (mrestrict (w_H W1) m') (g + 88) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
tcgif_at SEGS WFN_ADDR hw (mrestrict (w_H W1) m') g (cl_set_cur s1 cur').
Proof.
intros ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK HT UN Vc Rc. pose proof asan_consts as (C1 & _).
apply (tcgif_at_stretchA ly1 S1 W1 mem1 md1 m' g s s1 N rest cur' HAR HPerm HOK HT); [| exact Vc | exact Rc].
intros a Ha Hna. apply UN; [clear - Ha C1; lia | exact Hna].
Qed.
Lemma regsB_ok : forall (regs regs1 : bvmap 5 word) g s1,
cl_regs_at B regs regs1 g ->
4096 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (cl_extra regs g s1))) regsB regs1.
Proof.
intros regs regs1 g s1 (R2 & R3 & R4 & R8 & R9 & R19 & R18 & R20' & _) Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))). assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia); exact R19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; exact R8
| rewrite E38; exact R18
| rewrite E32, unsigned_lit_small by lia; exact R9 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cl_RC_ok : CL_FR_stmt B hw CTX 0 -> CL_RC_stmt.
Proof.
intros FRN ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (cl_seed B LAWS TL hw CL_RET_RAWCLOSE regsB true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsB_ok regs regs1 g s1 HR Hgh Hgceil) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_FR.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
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
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N rest lyc Sc Wc rg mm mdq k s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1)) end.
* intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
* reflexivity.
* exact Vcur.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. exact HPerm1.
+ clear - Hk. lia.
+
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q8. exact E32.
* rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
* rewrite Q18. exact E38.
* rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
* intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q21. apply bv_eq. vm_compute. reflexivity.
+ rewrite Q22. apply bv_eq. vm_compute. reflexivity.
-
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_FR.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
set (cR := bv_unsigned (getr regs1 10) mod 2 ^ 32).
pose proof (field_of_region_any E _ 32 g _ _ _ _ _ 88 4 (SOff 10 0) HRg E32u ltac:(cbn; tauto) ltac:(cbn; lia)) as Vcur.
cbn [sv_denot] in Vcur. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl) in Vcur.
change (N.to_nat 4) with 4%nat in Vcur. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vcur. change (bv_unsigned (getr regs1 10) mod 2 ^ 32) with cR in Vcur.
assert (RcR : 0 <= cR < 2 ^ 32) by (subst cR; apply Z.mod_pos_bound; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 cR) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_setcur (mrestrict (w_H Wc) memc) _ g s1 cR (proj1 HT1)) end.
* intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
* exact Vcur.
* exact RcR.
- intros j f Hj Hfj. cbn [cg_frames cl_set_cur] in Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. exact HPerm1.
+ clear - Hk. lia.
+
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q8. exact E32.
* rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
* rewrite Q18. exact E38.
* rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
* intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q21. apply bv_eq. vm_compute. reflexivity.
+ rewrite Q22. apply bv_eq. vm_compute. reflexivity.
Qed.
Lemma cl_B_ok : CL_RC_stmt -> CL_B_stmt B hw CTX.
Proof.
intros RCN ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
assert (HPr : Permutation (ablocks B lyc Sc) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s) ++ rest)).
{ eapply Permutation_trans; [exact HPerm1|]. unfold cgif_blocks. cbn [app]. rewrite <- app_assoc. apply perm_swap. }
assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPr|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hinr) as Hrh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrh, Hrh_img.
assert (Dgr : g + 96 <= cg_raw s \/ cg_raw s + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (cg_raw s, RAW_SIZE) (g, CGIF_SIZE) _ HAR HPr ltac:(left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D. clear - D. lia. }
destruct (cl_seed B LAWS TL hw CL_B regsB true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsB_ok regs regs1 g s1 HR Hgh Hgceil) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E36 : ew E 36 = Z_to_bv 64 (cg_raw s1)) by (change 36%nat with (32 + 4)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_tok RUN HS HJ SHOK RBspanC.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19; prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
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
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (HTg : obj_at SEGS (mrestrict (w_H Wc) mm) g LAY_CGIF (tcgif_vals hw s1))
by (apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1));
[ intros i Hi Hni; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia | reflexivity | exact Vcur ]);
assert (HTr : obj_at SEGS (mrestrict (w_H Wc) mm) (cg_raw s) LAY_Raw (traw_vals WFN_ADDR g s1))
by (rewrite <- Hraw1; apply (obj_at_kept _ _ (cg_raw s1) LAY_Raw _ 48 (proj1 (proj2 HT1)) lay_inside_Raw); rewrite Hraw1;
intros i Hi; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Dgr Hgh Hgceil Hr4096 Hrceil C1 C3; lia) end.
pose proof (obj_at_nth SEGS _ _ _ _ 11 (56, 8%N) hw HTg eq_refl eq_refl) as [Vwfn _].
pose proof (obj_at_nth SEGS _ _ _ _ 12 (64, 8%N) 0 HTg eq_refl eq_refl) as [Vctx _].
pose proof (obj_at_nth SEGS _ _ _ _ 14 (80, 8%N) 0 HTg eq_refl eq_refl) as [Vfile _].
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) WFN_ADDR HTr eq_refl eq_refl) as [Vrw _].
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) g HTr eq_refl eq_refl) as [Vrg _].
pose proof (obj_at_nth SEGS _ _ _ _ 8 (40, 4%N) (rw_cur s1) HTr eq_refl eq_refl) as [Vrc Rrc].
cbn [fst snd] in Vwfn, Vctx, Vfile, Vrw, Vrg, Vrc, Rrc. rewrite Z.add_0_r in Vrw.
change (N.to_nat 8) with 8%nat in Vwfn, Vctx, Vfile, Vrw, Vrg. change (N.to_nat 4) with 4%nat in Vrc.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 (cg_raw s)) by (rewrite Q10, E36, Hraw1; reflexivity);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u; clear - Hgceil; lia);
assert (HEVc : st_nev Sc + EV_RAWCLOSE <= EV_MAX) by (unfold EV_RAWCLOSE; clear - Hnev Hk Hev Hk0; lia)
end.
pose proof HUrc as HU1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k TRAWCLOSE_STK
(ablocks_fp [(cg_raw s, RAW_SIZE)]) EV_RAWCLOSE (-80) (Z_to_bv 64 (BASE + CL_RET_RAWCLOSE)) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s) ++ rest)) HJ Qsp);
[ reflexivity | lia | unfold TRAWCLOSE_STK, ASTACK; lia | rewrite HTS; unfold TRAWCLOSE_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | unfold CL_RET_RAWCLOSE; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (RAWCLOSE lyc Sc Wc rg mm _ [] (cg_raw s) g (rw_cur s1) 0 _ HPRE1 Q10' HPr
Vrw Vrg Vrc ltac:(clear - Rrc; lia) Vwfn Vctx ltac:(lia) Vfile HEVc HU1)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; left; destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa);
destruct Hpn as [Hpn | []]; injection Hpn as <- <-; split;
[ unfold FPc; replace a with (cg_raw s + (a - cg_raw s)) by lia; apply (inFP_ablocks_fp _ (cg_raw s) RAW_SIZE (a - cg_raw s)); [| clear - Hpa; lia];
unfold cgif_blocks; right; left; reflexivity
| exists (cg_raw s), RAW_SIZE; split; [exact Hinr | exact Hpa] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HPerm2).
pose proof (proj1 HJ2) as HAR2.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFg : forall i, 0 <= i < 96 -> ~ inFP (ablocks_fp [(cg_raw s, RAW_SIZE)]) (g + i)).
{ intros i Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa). destruct Hpn as [Hpn | []]. injection Hpn as <- <-.
change (req_size RAW_SIZE) with 48 in Hpa. clear - Hi Hpa Dgr. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm2 _) _) _ =>
lazymatch type of HTg with obj_at _ (mrestrict _ ?mm) _ _ _ =>
assert (Kg : blk_kept (w_H Wc) (w_H W2) mm mm2 g 96)
by (eapply (blk_kept_call B); [exact HJc2 | exact Hing | exact Hing2 | change (req_size CGIF_SIZE) with 96; exact HnFg]) end end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm2 _) ?md2) _ =>
eapply SRr_mono; [apply (RCN ly S W regs mem md ch g s N rest ly2 S2 W2 rg2 mm2 md2 (k + EV_RAWCLOSE) s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); unfold EV_RAWCLOSE; clear; lia] end.
-
split; [exact HJ2|]. split; [unfold EV_RAWCLOSE; clear - Hk0; lia|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (unfold TRAWCLOSE_STK, ASTACK; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- exact (obj_at_blk_kept (w_H Wc) (w_H W2) _ _ g LAY_CGIF _ 96 HTg lay_inside_CGIF Kg).
- intros j f Hj Hfj. change (Z.to_nat 0) with 0%nat in Hj.
assert (Hinf : In (Some f) (cg_frames s1)) by (eapply nth_error_In; exact Hfj).
pose proof (proj2 (proj2 HT1) f Hinf) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
cbn [skipn] in Hfin.
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPr|]. right. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Hf2 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Drf : cg_raw s + 48 <= fr_ptr f \/ fr_ptr f + 40 <= cg_raw s).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (cg_raw s, RAW_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPr) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
lazymatch type of HTg with obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_at_blk_kept (w_H Wc) (w_H W2) mm _ (fr_ptr f) LAY_Frame _ 40); [| exact lay_inside_Frame |] end.
+ apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia.
+ pose proof (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc2 Hfc Hf2) as Kf.
apply Kf. intros ii Hii HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa). destruct Hpn as [Hpn | []]. injection Hpn as <- <-.
change (req_size RAW_SIZE) with 48 in Hpa. unfold FRAME_SIZE in Hii. clear - Hii Hpa Drf. lia. }
split; [exact HOK |]. unfold fr_blocks. cbn [skipn app]. rewrite <- app_assoc. exact HPerm2.
- unfold EV_RAWCLOSE. clear - Hk. lia.
-
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
+ rewrite (CS 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite (CS 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q3'.
+ rewrite (CS 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q4'.
+ rewrite (CS 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q8. exact E32.
+ rewrite (CS 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite (CS 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q19.
exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ rewrite (CS 18%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q18. exact E38.
+ rewrite (CS 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
+ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
Qed.
End h.
End e.
End d.
