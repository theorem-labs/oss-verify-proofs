(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2h UI24 UI2c UI2d UI2e UI2f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2q UI2r.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0d YI0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma zcanon_add_mulm1 : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> zcanon (a + zcanon (b * zcanon 18446744073709551615)) = a - b.
Proof using.
intros a b Hb Ha. unfold zcanon, M64. change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615. nia.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma af_frames_blocks_img_in : forall N fs f, In (Some f) fs -> In (fr_img f, N) (frames_blocks N fs).
Proof using. intros N fs f H. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact H | right; left; reflexivity]. Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Lemma af_imgs_sep : forall L A m md g s N rest j1 j2 f1 f2,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
nth_error (cg_frames s) j1 = Some (Some f1) -> nth_error (cg_frames s) j2 = Some (Some f2) -> j1 <> j2 ->
fr_img f1 + N <= fr_img f2 \/ fr_img f2 + N <= fr_img f1.
Proof using LAWS.
intros L A m md g s N rest j1 j2 f1 f2 HH HB H1 H2 Hne.
destruct (nth_error_split _ _ H1) as (l1 & l2 & Hfr & Hl1).
assert (Hf2 : In (Some f2) (l1 ++ l2)).
{ rewrite Hfr in H2. destruct (Nat.lt_ge_cases j2 (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in H2 by exact Hlt. eapply nth_error_In. exact H2.
- apply in_app_iff. right. rewrite nth_error_app2 in H2 by exact Hge.
destruct (j2 - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in H2. eapply nth_error_In. exact H2. }
assert (HP : Permutation (cgif_blocks0 g s N ++ rest)
((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (fr_img f1, N) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f1, FRAME_SIZE) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest)).
{ unfold cgif_blocks0. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_img_front. }
assert (HP' : Permutation (blocks L A) ((fr_img f1, N) :: (cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f1, FRAME_SIZE) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest)).
{ eapply Permutation_trans; [exact (Permutation_trans HB HP)|].
eapply Permutation_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap. }
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_img f1, N) _ (fr_img f2, N) HH HP') as Hs.
cbn [fst snd] in Hs. apply Hs. right. right. apply in_app_iff. left. apply in_app_iff. right.
apply in_app_iff in Hf2 as [Hf2|Hf2].
- apply in_app_iff. left. apply af_frames_blocks_img_in. exact Hf2.
- apply in_app_iff. right. right. apply in_app_iff. right. apply af_frames_blocks_img_in. exact Hf2.
Qed.
Definition dv_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z) : Prop :=
let sp0 := spZ regs0 in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
nth_error (cg_frames s) (i - 1) = Some (Some b) /\
fl_fp FP s f /\
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ rest) /\ 0 <= tv < 2 ^ 64 /\ 0 <= np <= 65535 /\
0 <= u23 < 2 ^ 64 /\ 0 <= u24 < 2 ^ 64 /\ 0 <= u25 < 2 ^ 64 /\
fl_saved_ok memc sp0 regs0 /\
word_mem ubs0segs memc (sp0 - 272 + 112) g /\ word_mem ubs0segs memc (sp0 - 272 + 120) (fr_ptr f) /\
word_mem ubs0segs memc (sp0 - 272 + 72) tv /\ word_mem ubs0segs memc (sp0 - 272 + 80) (cg_H s) /\
word_mem ubs0segs memc (sp0 - 272 + 104) (cg_W s) /\ word_mem ubs0segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) /\
word_mem ubs0segs memc (sp0 - 272 + 32) u23 /\ word_mem ubs0segs memc (sp0 - 272 + 16) u24 /\
word_mem ubs0segs memc (sp0 - 272 + 24) u25 /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ getr regs1 9 = Z_to_bv 64 (fr_img f) /\
getr regs1 18 = Z_to_bv 64 (fr_ptr b) /\ getr regs1 27 = Z_to_bv 64 (cg_W s) /\ getr regs1 20 = Z_to_bv 64 np /\
getr regs1 19 = Z_to_bv 64 (cg_H s) /\
fl_untouched regs0 regs1.
Lemma dv_ctx : forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
exists ctcur ctbef,
dctx memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N (spZ regs0 - 272)
(cgif_vals s) (firstn 7 (frame_vals (set_fr_gen f gen1))) (firstn 7 (frame_vals b))
(fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_lpal f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (fr_lpal b) (cg_ngp s) (cg_pal s) ctcur ctbef /\
In (fr_img f, N) (blocks Lc Ac) /\ In (fr_img b, N) (blocks Lc Ac).
Proof using.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G27 & G20 & G19 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ b HH0 HB Hbin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Hbi0 Hbi1].
pose proof (af_frames_sep0 API Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HB Hf Hb ltac:(lia)) as Hfb.
pose proof (af_imgs_sep Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HB Hf Hb ltac:(lia)) as Dfb.
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (Hfrs b Hb1in) as Hbobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf. pose proof (obj_at_range _ _ _ _ _ Hbobj) as Rb.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp. cbn [nth snd LAY_CGIF Z.of_N] in Rngp.
pose proof (Rf 5%nat (fr_nlp f) eq_refl) as Rfnlp. pose proof (Rb 5%nat (fr_nlp b) eq_refl) as Rbnlp.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfnlp, Rbnlp.
assert (M16 : forall fr, In (Some fr) (cg_frames s) -> fr_ptr fr mod 8 = 0).
{ intros fr Hfr.
pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fr) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N fr); [exact Hfr | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
assert (CTB : forall fr, In (Some fr) (cg_frames s) -> 0 <= fr_nlp fr ->
In (ct_sel (fr_attr fr) (fr_lpal fr) (cg_pal s), 3 * ct_sel (fr_attr fr) (fr_nlp fr) (cg_ngp s)) (cgif_blocks0 g s N) /\
0 <= 3 * ct_sel (fr_attr fr) (fr_nlp fr) (cg_ngp s)).
{ intros fr Hfr Hnl. unfold ct_sel. destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0) as [Hz|Hz].
- split; [| clear - Rngp; lia]. unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks.
rewrite (proj1 (Hfwf fr Hfr) Hz). cbn. left. reflexivity.
- split; [| clear - Hnl; lia]. apply (frame_blocks_in_cgif0 g s N fr _ _ Hfr). unfold frame_blocks. right. right.
destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0); [lia|]. left. reflexivity. }
destruct (CTB f Hfin ltac:(clear - Rfnlp; lia)) as [CTf Sf0]. destruct (CTB b Hbin ltac:(clear - Rbnlp; lia)) as [CTb Sb0]. clear CTB.
assert (CTf' : In (ct_sel (fr_attr f) (fr_lpal f) (cg_pal s), 3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s)) (blocks Lc Ac))
by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact CTf).
assert (CTb' : In (ct_sel (fr_attr b) (fr_lpal b) (cg_pal s), 3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s)) (blocks Lc Ac))
by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact CTb).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTf') as [Sc0 Sc1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTb') as [Sd0 Sd1].
destruct (rdn_of_present ubs0_msyms memc (Z.to_nat (3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s))) (ct_sel (fr_attr f) (fr_lpal f) (cg_pal s))
ltac:(intros k Hk; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ k HH0 CTf' ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
destruct (rdn_of_present ubs0_msyms memc (Z.to_nat (3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s))) (ct_sel (fr_attr b) (fr_lpal b) (cg_pal s))
ltac:(intros k Hk; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ k HH0 CTb' ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (Oc1 : obj_at ubs0segs memc (fr_ptr f) LAY_FrameConfig (firstn 7 (frame_vals f1))).
{ rewrite LAY_Frame_split in Hfobj.
apply (proj1 (obj_at_app ubs0segs _ (fr_ptr f) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals f1)) (skipn 7 (frame_vals f1)) eq_refl)). exact Hfobj. }
assert (Ob1 : obj_at ubs0segs memc (fr_ptr b) LAY_FrameConfig (firstn 7 (frame_vals b))).
{ pose proof Hbobj as Hbobj'. rewrite LAY_Frame_split in Hbobj'.
apply (proj1 (obj_at_app ubs0segs _ (fr_ptr b) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals b)) (skipn 7 (frame_vals b)) eq_refl)). exact Hbobj'. }
destruct (af_frame_geom0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin) as (_ & Hfimgin & _).
destruct (af_frame_geom0 API Lc Ac memc mdc g s N _ b HH0 HB Hbin) as (_ & Hbimgin & _).
exists ctcur, ctbef. split; [| split; [exact Hfimgin | exact Hbimgin]].
unfold dctx.
repeat match goal with |- _ /\ _ => split end;
first [ exact Hobj | exact Oc1 | exact Ob1 | exact Rct | exact Rbt | reflexivity | exact Hg0 | exact Hg1 | exact Hg16 | exact Hp0 | exact Hq0
| exact (M16 f Hfin) | exact (M16 b Hbin) | exact Sc0 | exact Sc1 | exact Sd0 | exact Sd1 | exact Sf0 | exact Sb0
| exact Him0 | exact Him1 | exact Hbi0 | exact Hbi1 | exact Dfb | exact HN | exact HNle | exact W80 | exact W104 | exact W112 | exact W120
| clear - Hp1 HFRv; lia | clear - Hq1 HFRv; lia | clear - Hpg HGSv HFRv; lia | clear - Hqg HGSv HFRv; lia | clear - Hfb HFRv; lia
| clear - HW1 RW; lia | clear - HH1 RH; lia | clear - Hceil HFSv; lia | clear - Hsp063; lia
| replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| idtac ].
all: fail "dctx leaf".
Qed.
Lemma dv_HD : forall memc g s N i f b gen1 spv ctcur ctbef GPAL cur befr,
cgif_wf s N -> nth_error (cg_frames s) i = Some (Some f) -> nth_error (cg_frames s) (i - 1) = Some (Some b) ->
dctx memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv (cgif_vals s) (firstn 7 (frame_vals (set_fr_gen f gen1))) (firstn 7 (frame_vals b))
(fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_lpal f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (fr_lpal b) (cg_ngp s) (cg_pal s) ctcur ctbef ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
YO07.flag (YO07.f_attr befr) 1 || YO07.flag (YO07.f_attr cur) 1 || YO07.flag (YO07.f_attr befr) 4 || YO07.flag (YO07.f_attr cur) 4 = true ->
forall p, 0 <= p < cg_W s * cg_H s ->
(CMPp memc (fr_img f) (fr_img b) (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef p <> 0 <->
YO07.px_ne (gcfg_of s GPAL) cur befr (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img befr) 0) = true).
Proof using.
intros memc g s N i f b gen1 spv ctcur ctbef GPAL cur befr Hwf Hf Hb HC HVALS Hslow p Hp.
pose proof Hwf as (Hlen & HW1 & HH1 & _ & _ & Hngp & _ & Hfwf).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
dctx_open HC.
pose proof HVALS as (HVg & HVf & HVb & _). pose proof HVf as (XA1 & _ & XA3 & XA4 & XA5 & XA6 & XA7 & XVI & XVIl & HVlp).
cbn [oframe_relb] in HVb. pose proof HVb as (XB1 & _ & XB3 & XB4 & XB5 & XB6 & XB7 & XBI & XBIl & HBlp).
rewrite (px_ne_slow (gcfg_of s GPAL) cur befr Hslow).
unfold CMPp.
rewrite (byte_at_garr8 memc (fr_img f) (YO07.f_img cur) p XVI) by (rewrite XVIl, HN; exact Hp).
rewrite (byte_at_garr8 memc (fr_img b) (YO07.f_img befr) p XBI) by (rewrite XBIl, HN; exact Hp).
pose proof (garr8_nthZ ubs0segs memc (fr_img f) (YO07.f_img cur) p XVI ltac:(lia) ltac:(rewrite <- (Nat2Z.id (length _)), XVIl, HN; lia)) as [_ Ric].
pose proof (garr8_nthZ ubs0segs memc (fr_img b) (YO07.f_img befr) p XBI ltac:(lia) ltac:(rewrite <- (Nat2Z.id (length _)), XBIl, HN; lia)) as [_ Rib].
assert (PALc : map bv_unsigned ctcur = firstn (Z.to_nat (3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s))) (if YO07.flag (fr_attr f) 1 then YO07.f_lpal cur else YO07.g_gpal (gcfg_of s GPAL))).
{ unfold YO07.flag. cbn [YO07.g_gpal gcfg_of]. unfold ct_sel in Rct |- *.
destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0) as [Hz|Hz]; cbn [negb].
- destruct (HVg (proj1 (Hfwf f Hfin) Hz)) as [HG HGl].
apply (rdn_garr8_prefix memc (cg_pal s)); [exact Rct | exact HG | rewrite <- (Nat2Z.id (length GPAL)), HGl; lia].
- destruct (HVlp Hz) as [HL HLl].
apply (rdn_garr8_prefix memc (fr_lpal f)); [exact Rct | exact HL | rewrite <- (Nat2Z.id (length (YO07.f_lpal cur))), HLl; lia]. }
assert (PALb : map bv_unsigned ctbef = firstn (Z.to_nat (3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s))) (if YO07.flag (fr_attr b) 1 then YO07.f_lpal befr else YO07.g_gpal (gcfg_of s GPAL))).
{ unfold YO07.flag. cbn [YO07.g_gpal gcfg_of]. unfold ct_sel in Rbt |- *.
destruct (Z.eqb_spec (Z.land (fr_attr b) 1) 0) as [Hz|Hz]; cbn [negb].
- destruct (HVg (proj1 (Hfwf b Hbin) Hz)) as [HG HGl].
apply (rdn_garr8_prefix memc (cg_pal s)); [exact Rbt | exact HG | rewrite <- (Nat2Z.id (length GPAL)), HGl; lia].
- destruct (HBlp Hz) as [HL HLl].
apply (rdn_garr8_prefix memc (fr_lpal b)); [exact Rbt | exact HL | rewrite <- (Nat2Z.id (length (YO07.f_lpal befr))), HLl; lia]. }
assert (CM : (cmpPixel_fn (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef
(nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img befr) 0) =? 0)
= negb (YO07.cmp_pixel (gcfg_of s GPAL) cur befr (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img befr) 0))).
{ apply (cmpPixel_model (gcfg_of s GPAL) cur befr); try assumption.
- intros F4. apply XA5. unfold YO07.flag in F4. intros H6. apply (f_equal (fun x => Z.land x 4)) in H6. rewrite <- Z.land_assoc in H6.
change (Z.land 6 4) with 4 in H6. rewrite Z.land_0_l in H6. rewrite H6 in F4. discriminate F4.
- intros F4. apply XB5. unfold YO07.flag in F4. intros H6. apply (f_equal (fun x => Z.land x 4)) in H6. rewrite <- Z.land_assoc in H6.
change (Z.land 6 4) with 4 in H6. rewrite Z.land_0_l in H6. rewrite H6 in F4. discriminate F4.
- reflexivity.
- unfold ct_sel, YO07.flag. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0) as [Hz|Hz]; cbn [negb].
+ destruct (HVg (proj1 (Hfwf f Hfin) Hz)) as [HG HGl]. cbn [YO07.g_gpal gcfg_of]. rewrite HGl. lia.
+ destruct (HVlp Hz) as [HL HLl]. rewrite HLl. lia.
- unfold ct_sel, YO07.flag. destruct (Z.eqb_spec (Z.land (fr_attr b) 1) 0) as [Hz|Hz]; cbn [negb].
+ destruct (HVg (proj1 (Hfwf b Hbin) Hz)) as [HG HGl]. cbn [YO07.g_gpal gcfg_of]. rewrite HGl. lia.
+ destruct (HBlp Hz) as [HL HLl]. rewrite HLl. lia. }
rewrite <- (Bool.negb_involutive (YO07.cmp_pixel _ _ _ _ _)), <- CM. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.
Definition ss_slow : sstate :=
mkSS FL_SLOW sr_atoms [ YP09.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))] ; YP09.mkRegion (Some 2%nat) 48 56 48 56 [] ;
YP09.mkRegion (Some 2%nat) 88 112 88 96 [mkChunk 104 (CVal 8 (SOff 27 0))] ] None
(mkFacts [ (19%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 (CEIL_MAX - 40) 3); (2%nat, mkAF (CEIL_MIN + 8192) (2^63) 4) ] [] []).
Definition ss_ident : sstate :=
mkSS FL_IDENT sr_atoms [ YP09.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))] ] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_s4f : sstate :=
mkSS FL_S4F sr_atoms [ YP09.mkRegion (Some 2%nat) 48 112 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma fl_dgo :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st)
(rest FP FPw : list (Z * Z)) (tv np u23 u24 u25 : Z) (S GPAL : list Z) (cur befr : YO07.frame) (brb bc : rbound),
let gen1 := fl_gen3 (gcfg_of s GPAL) cur (Some befr) in
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
fl_sink g s N rest FP FPw S L A mem md (spZ regs0) ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
u23 = fr_disp f -> u24 = Z.land (fr_attr f) 4 -> u25 = (if fl_hasAlpha (gcfg_of s GPAL) cur then 1 else 0) ->
np = fl_npal (gcfg_of s GPAL) cur -> tv mod 256 = YO07.f_trans cur ->
YO07.flag (fl_gen3 (gcfg_of s GPAL) cur (Some befr)) 2 = true ->
(forall n, 0 < n <= N -> room bc n /\ rawadd_room (rb_malloc bc n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc bc n)) n) (flush_rb brb)) -> res_ok Ac bc ->
forall (regsF : bvmap 5 word) (memF : word -> option byte) w h top left,
journal ubs0_msyms MR FLUSH_STK (spZ regs0) FP L A mem md Lc Ac memF mdc -> KD memc (spZ regs0 - 272) memF ->
word_mem ubs0segs memF (spZ regs0 - 272 + 96) top ->
1 <= w -> 0 <= left -> left + w <= cg_W s -> 1 <= h -> 0 <= top -> top + h <= cg_H s ->
getr regsF 2 = Z_to_bv 64 (spZ regs0 - 272) -> getr regsF 9 = Z_to_bv 64 (fr_img f) ->
getr regsF 18 = Z_to_bv 64 (fr_ptr b) -> getr regsF 27 = Z_to_bv 64 (cg_W s) -> getr regsF 20 = Z_to_bv 64 np ->
getr regsF 26 = Z_to_bv 64 left -> getr regsF 19 = Z_to_bv 64 w -> getr regsF 22 = Z_to_bv 64 h ->
getr regsF 3 = getr regs0 3 -> getr regsF 4 = getr regs0 4 ->
fl_dims (gcfg_of s GPAL) cur (Some befr) = (w, h, top, left) ->
SR ubs0segs (mkCfg (mkst regsF (Z_to_bv 64 FL_DT) memF (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md).
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np u23 u24 u25 S GPAL cur befr brb bc gen1 PRE
HSINK HVALS Xu23 Xu24 Xu25 Xnp Xtv0 XG2 HNUM HRq.
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G27 & G20 & G19 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & _ & _ & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in *. set (f1 := set_fr_gen f gen1) in *.
dctx_open HC.
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (Hfrs b Hb1in) as Hbobj.
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & _).
assert (KB : forall m, KD memc spv m -> forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros m K bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsp0 Hac; lia. }
assert (CGAT : forall m, (forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)) -> cgif_at m g s1).
{ intros m KBm. split; [| split].
- eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KBm g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw s1) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KBm (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KBm (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KBm (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N x _ _ Hin). left. reflexivity. }
assert (SVK : forall m, KD memc spv m -> fl_saved_ok m sp0 regs0).
{ intros m K. apply (fl_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply K; clear - Ha Hsp0 Hsp1 Hac; lia. }
intros regsF memF w h top left HJF KF V96 Hw Hl0 Hlw Hh Ht0 Hth R2 R9 R18 R27 R20 R26 R19 R22 R3 R4 XD.
assert (WF : forall off v, word_mem ubs0segs memc (sp0 - 272 + off) v -> 0 <= off -> off + 8 <= 272 ->
(off + 8 <= 8 \/ (16 <= off /\ off + 8 <= 40) \/ (56 <= off /\ off + 8 <= 64) \/ (72 <= off /\ off + 8 <= 88) \/ 104 <= off) ->
word_mem ubs0segs memF (sp0 - 272 + off) v).
{ intros off v Hw' H1 H2 H3 k Hk. rewrite <- (Hw' k Hk). apply KF; clear - H1 H2 H3 Hk Hsp0 Hsp1 Hac; subst spv; lia. }
assert (Hwh : 0 < h * w <= N) by (rewrite HN; clear - Hw Hl0 Hlw Hh Ht0 Hth; nia).
destruct (HNUM (h * w) Hwh) as (HRM & HRR & HRB).
apply (fl_dt API IMG RAWADDX L A mem md regs0 regsF Lc Ac memF mdc g N s i f b rest FP FPw tv np u23 u24 u25 w h top left S GPAL cur befr brb bc);
[| exact HSINK
| eapply fl_vals_kept; [| exact HVALS]; intros a0 n0 k Hin Hk;
assert (Hbn' : In (a0, n0) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact (fl_vblocks_sub g s N f (Some b) i Hf ltac:(right; exists (i - 1)%nat; exact Hb) _ Hin));
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a0 n0 HH0 Hbn') as [R0 R1]; apply KF; clear - R0 R1 Hk Hsp0 Hac; subst spv; lia
| exact Xu23 | exact Xu24 | exact Xu25 | exact Xnp | exact Xtv0 | exact XG2 | exact XD | exact HRq | exact HRM | exact HRR | exact HRB ].
split; [exact HJF|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ apply CGAT. intros bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply KF; clear - R0 R1 Hk Hsp0 Hac; subst spv; lia. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact Hb|]. split; [exact HFP|]. split; [exact HB|].
split; [exact Htv|]. split; [exact Hnp|]. split; [exact Hu23|]. split; [exact Hu24|]. split; [exact Hu25|].
split; [exact Hw|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh|]. split; [exact Ht0|]. split; [exact Hth|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF; clear - Ha Hsp0 Hsp1 Hac; subst spv; lia]|].
split; [apply WF; [exact W112 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W120 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W72 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W80 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W104 | clear; lia | clear; lia | clear; lia]|].
split; [exact V96|].
split; [apply WF; [exact W56 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W32 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W16 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W24 | clear; lia | clear; lia | clear; lia]|].
split; [exact R2|]. split; [exact R9|]. split; [exact R18|]. split; [exact R27|]. split; [exact R20|].
split; [exact R26|]. split; [exact R19|]. split; [exact R22|]. split; [exact R3 | exact R4].
Qed.
Lemma fl_slow :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st)
(rest FP FPw : list (Z * Z)) (tv np u23 u24 u25 : Z) (S GPAL : list Z) (cur befr : YO07.frame) (brb bc : rbound),
let gen1 := fl_gen3 (gcfg_of s GPAL) cur (Some befr) in
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
fl_sink g s N rest FP FPw S L A mem md (spZ regs0) ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
u23 = fr_disp f -> u24 = Z.land (fr_attr f) 4 -> u25 = (if fl_hasAlpha (gcfg_of s GPAL) cur then 1 else 0) ->
np = fl_npal (gcfg_of s GPAL) cur -> tv mod 256 = YO07.f_trans cur ->
YO07.flag (fl_gen3 (gcfg_of s GPAL) cur (Some befr)) 2 = true ->
(forall n, 0 < n <= N -> room bc n /\ rawadd_room (rb_malloc bc n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc bc n)) n) (flush_rb brb)) -> res_ok Ac bc ->
YO07.flag (YO07.f_attr befr) 1 || YO07.flag (YO07.f_attr cur) 1 || YO07.flag (YO07.f_attr befr) 4 || YO07.flag (YO07.f_attr cur) 4 = true ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md).
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np u23 u24 u25 S GPAL cur befr brb bc gen1 PRE
HSINK HVALS Xu23 Xu24 Xu25 Xnp Xtv0 XG2 HNUM HRq Hslow.
pose proof PRE as (_ & _ & _ & _ & _ & _ & HwfX & _ & HfX & HbX & _).
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G27 & G20 & G19 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & _ & _ & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in *. set (f1 := set_fr_gen f gen1) in *.
dctx_open HC.
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (Hfrs b Hb1in) as Hbobj.
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & _).
assert (KB : forall m, KD memc spv m -> forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros m K bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsp0 Hac; lia. }
assert (CGAT : forall m, (forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)) -> cgif_at m g s1).
{ intros m KBm. split; [| split].
- eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KBm g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw s1) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KBm (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KBm (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KBm (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N x _ _ Hin). left. reflexivity. }
assert (SVK : forall m, KD memc spv m -> fl_saved_ok m sp0 regs0).
{ intros m K. apply (fl_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply K; clear - Ha Hsp0 Hsp1 Hac; lia. }
pose proof (fl_dgo L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np u23 u24 u25 S GPAL cur befr brb bc PRE HSINK HVALS Xu23 Xu24 Xu25 Xnp Xtv0 XG2 HNUM HRq) as GO.
fold sp0 in GO. fold spv in GO.
pose proof (dv_HD memc g s N i f b gen1 spv ctcur ctbef GPAL cur befr HwfX HfX HbX HC HVALS Hslow) as HD.
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW HH; nia).
destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
assert (WRS : forall m', journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv <= a < spv + 272 -> writable_at ubs0segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha HFSv. subst spv. lia. }
assert (XS4 : forall (regs5 : bvmap 5 word) (mem5 : word -> option byte) xr left top h,
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac mem5 mdc -> KD memc spv mem5 ->
word_mem ubs0segs mem5 (spv + 48) np -> word_mem ubs0segs mem5 (spv + 64) h -> word_mem ubs0segs mem5 (spv + 96) top ->
0 <= left <= xr -> xr < cg_W s -> 1 <= h -> 0 <= top -> top + h <= cg_H s ->
getr regs5 2 = Z_to_bv 64 spv -> getr regs5 9 = Z_to_bv 64 (fr_img f) -> getr regs5 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs5 25 = Z_to_bv 64 xr -> getr regs5 26 = Z_to_bv 64 left ->
getr regs5 3 = getr regs0 3 -> getr regs5 4 = getr regs0 4 ->
fl_dims (gcfg_of s GPAL) cur (Some befr) = (xr + 1 - left, h, top, left) ->
SR ubs0segs (mkCfg (mkst regs5 (Z_to_bv 64 FL_S4F) mem5 (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md)).
{ intros regs5 mem5 xr left top h HJ5 K5 V48 V64 V96 Hlx Hxr Hh Ht0 Hth R2 R9 R18 R25 R26 R3 R4 XD.
assert (V104 : word_mem ubs0segs mem5 (spv + 104) (cg_W s)).
{ intros k Hk. rewrite <- (W104 k Hk). apply K5; clear - Hk Hsp0 Hsp1 Hac; lia. }
set (E5 := Ereg regs5 (map (Z_to_bv 64) [np; h; cg_W s] ++ [])).
assert (HE5 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E5 m = getr regs5 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (HE5_32 : ew E5 32 = Z_to_bv 64 np) by (subst E5; apply (Ereg_vals regs5 [np; h; cg_W s] [] 0%nat); reflexivity).
assert (HE5_33 : ew E5 33 = Z_to_bv 64 h) by (subst E5; apply (Ereg_vals regs5 [np; h; cg_W s] [] 1%nat); reflexivity).
assert (HE5_34 : ew E5 34 = Z_to_bv 64 (cg_W s)) by (subst E5; apply (Ereg_vals regs5 [np; h; cg_W s] [] 2%nat); reflexivity).
assert (HU5_2 : bv_unsigned (ew E5 2) = spv) by (rewrite (HE5 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR5 : region_ok ubs0segs E5 mem5 (YP09.mkRegion (Some 2%nat) 48 112 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU5_2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ np); [cbn [sv_denot]; rewrite Z.add_0_r, HE5_32, unsigned_lit_small by (clear - Hnp; lia); reflexivity | cbn; clear - Hnp; lia | cbn; lia | apply val_mem_word_mem; exact V48].
- eapply (chunk_ok_val _ _ _ _ _ _ _ h); [cbn [sv_denot]; rewrite Z.add_0_r, HE5_33, unsigned_lit_small by (clear - Hh Hth Ht0 HH; lia); reflexivity | cbn; clear - Hh Hth Ht0 HH; lia | cbn; lia | apply val_mem_word_mem; exact V64].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s)); [cbn [sv_denot]; rewrite Z.add_0_r, HE5_34, unsigned_lit_small by (clear - HW; lia); reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact V104]. }
assert (HFA5 : atoms_ok E5 [ (2%nat, mkAF CEIL_MIN (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU5_2. change (2 ^ 4) with 16. clear - Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HS5 : st_ok ubs0segs E5 ss_s4f (mkst regs5 (Z_to_bv 64 FL_S4F) mem5 (seg_rom ubs0segs))).
{ unfold ss_s4f. subst E5. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR5 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA5]. }
clear HR5 HFA5.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 FL_S4F) mem5 (seg_rom ubs0segs))) in HJ5.
jrun_to LAWS ubs0tbl_ok HS5 HJ5 FL_DT. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K5). intros a Ha _ _ _ _. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. lia. }
assert (V96' : word_mem ubs0segs (ms_mem ms) (spv + 96) top).
{ intros k Hk. rewrite <- (V96 k Hk). apply (mbyte_of_frame _ _ _ _ _ HF); [clear - Hk Hsp0 Hsp1 Hac; lia|]. intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. lia. }
clear HF HG.
lazymatch type of HS5 with st_ok _ _ ?ssx ?msx =>
pose proof (regs_kept_of_st_ok ubs0segs E5 ssx msx regs5 _ [2; 3; 4; 9; 18; 26]%bv HS5 ltac:(subst E5; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E5 nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs0segs E5 ssx msx r HS5), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E5 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E5 ssx msx r HS5), Hr; reflexivity) end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS5 eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) (ms_mem ms) (xr + 1 - left) h top left HJ5 KF V96');
[ clear - Hlx; lia | clear - Hlx; lia | clear - Hlx Hxr; lia | exact Hh | exact Ht0 | exact Hth
| rewrite (HKR 2%bv ltac:(cbv; auto 50)); exact R2
| rewrite (HKR 9%bv ltac:(cbv; auto 50)); exact R9
| rewrite (HKR 18%bv ltac:(cbv; auto 50)); exact R18
| apply (RG 27%bv 34%nat _ eq_refl); exact HE5_34
| apply (RG 20%bv 32%nat _ eq_refl); exact HE5_32
| rewrite (HKR 26%bv ltac:(cbv; auto 50)); exact R26
|
| apply (RG 22%bv 33%nat _ eq_refl); exact HE5_33
| rewrite (HKR 3%bv ltac:(cbv; auto 50)); exact R3
| rewrite (HKR 4%bv ltac:(cbv; auto 50)); exact R4
| exact XD ].
rewrite (RGX 19%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom_off E5 25 xr 1), (U_atom E5 26 left)
by first [rewrite (HE5 25%nat 25%bv eq_refl); exact R25 | rewrite (HE5 26%nat 26%bv eq_refl); exact R26 | clear - Hlx Hxr HW; lia].
apply zcanon_add_mulm1; clear - Hlx Hxr HW; lia. }
assert (XID : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte),
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac mem2 mdc -> KD memc spv mem2 ->
word_mem ubs0segs mem2 (spv + 48) np ->
getr regs2 2 = Z_to_bv 64 spv -> getr regs2 9 = Z_to_bv 64 (fr_img f) -> getr regs2 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs2 10 = Z_to_bv 64 (cg_W s) -> getr regs2 3 = getr regs0 3 -> getr regs2 4 = getr regs0 4 ->
(forall p, 0 <= p < N -> CMPp memc (fr_img f) (fr_img b) (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef p = 0) ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 FL_IDENT) mem2 (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md)).
{ intros regs2 mem2 HJ2 K2 V48 R2 R9 R18 R10 R3 R4 VID.
set (E2 := Ereg regs2 (map (Z_to_bv 64) [np] ++ [])).
assert (HE2 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs2 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HE2_32 : ew E2 32 = Z_to_bv 64 np) by (subst E2; apply (Ereg_vals regs2 [np] [] 0%nat); reflexivity).
assert (HU2_2 : bv_unsigned (ew E2 2) = spv) by (rewrite (HE2 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR2 : region_ok ubs0segs E2 mem2 (YP09.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2_2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ2); lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ np); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_32, unsigned_lit_small by (clear - Hnp; lia); reflexivity | cbn; clear - Hnp; lia | cbn; lia | apply val_mem_word_mem; exact V48]. }
assert (HFA2 : atoms_ok E2 [ (2%nat, mkAF CEIL_MIN (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2_2. change (2 ^ 4) with 16. clear - Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HS2 : st_ok ubs0segs E2 ss_ident (mkst regs2 (Z_to_bv 64 FL_IDENT) mem2 (seg_rom ubs0segs))).
{ unfold ss_ident. subst E2. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR2 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA2]. }
clear HR2 HFA2.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_IDENT) mem2 (seg_rom ubs0segs))) in HJ2.
jrun_to LAWS ubs0tbl_ok HS2 HJ2 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU2_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K2). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2_2. clear - Hna4; lia. }
clear HF HG.
lazymatch type of HS2 with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs0segs E2 ssx msx 0 _ 2%nat spv HS2 eq_refl eq_refl HU2_2) as Hcs;
pose proof (regs_kept_of_st_ok ubs0segs E2 ssx msx regs2 _ [2; 3; 4; 9; 18]%bv HS2 ltac:(subst E2; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E2 nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs0segs E2 ssx msx r HS2), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E2 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E2 ssx msx r HS2), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (V96' : word_mem ubs0segs (ms_mem ms) (spv + 96) 0).
{ apply (chunk_word E2 _ _ 96 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SLit 0))) ltac:(cbn [In]; tauto))); [reflexivity | clear; lia]. }
assert (XD : fl_dims (gcfg_of s GPAL) cur (Some befr) = (1, 1, 0, 0)).
{ unfold fl_dims. rewrite XG2.
rewrite (diff_area_ident (gcfg_of s GPAL) cur befr (cg_W s) (cg_H s) _ (proj1 HW) (proj1 HH) eq_refl ltac:(pose proof HVALS as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & XL & _) & _ & _); rewrite XL; exact HN)
ltac:(pose proof HVALS as (_ & _ & HVb & _); cbn [oframe_relb] in HVb; pose proof HVb as (_ & _ & _ & _ & _ & _ & _ & _ & XL & _); rewrite XL; exact HN)
HD); [reflexivity|].
intros p Hp Hd. apply Hd. apply VID. rewrite HN. exact Hp. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS2 eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) (ms_mem ms) 1 1 0 0 HJ2 KF V96');
[ clear; lia | clear; lia | clear - HW; lia | clear; lia | clear; lia | clear - HH; lia
| rewrite (HKR 2%bv ltac:(cbv; auto 50)); exact R2
| rewrite (HKR 9%bv ltac:(cbv; auto 50)); exact R9
| rewrite (HKR 18%bv ltac:(cbv; auto 50)); exact R18
| apply (RG 27%bv 10%nat _ eq_refl); rewrite (HE2 10%nat 10%bv eq_refl); exact R10
| apply (RG 20%bv 32%nat _ eq_refl); exact HE2_32
| rewrite (RGX 26%bv (SLit 0) eq_refl); reflexivity
| rewrite (RGX 19%bv (SLit 1) eq_refl); reflexivity
| rewrite (RGX 22%bv (SLit 1) eq_refl); reflexivity
| rewrite (HKR 3%bv ltac:(cbv; auto 50)); exact R3
| rewrite (HKR 4%bv ltac:(cbv; auto 50)); exact R4
| exact XD ]. }
assert (XS3 : forall (regs3 : bvmap 5 word) (mem3 : word -> option byte) top hrow c0,
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac mem3 mdc -> KD memc spv mem3 ->
word_mem ubs0segs mem3 (spv + 48) np -> word_mem ubs0segs mem3 (spv + 96) top ->
0 <= top <= hrow -> hrow < cg_H s -> 0 <= c0 < cg_W s -> CMPp memc (fr_img f) (fr_img b) (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef (top * cg_W s + c0) <> 0 ->
(forall p, 0 <= p < top * cg_W s -> CMPp memc (fr_img f) (fr_img b) (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef p = 0) ->
(exists c, 0 <= c < cg_W s /\ CMPp memc (fr_img f) (fr_img b) (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef (hrow * cg_W s + c) <> 0) ->
(forall p, (hrow + 1) * cg_W s <= p < N -> CMPp memc (fr_img f) (fr_img b) (fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (cg_ngp s) ctcur ctbef p = 0) ->
getr regs3 2 = Z_to_bv 64 spv -> getr regs3 8 = Z_to_bv 64 (fr_img b) -> getr regs3 9 = Z_to_bv 64 (fr_img f) ->
getr regs3 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs3 21 = Z_to_bv 64 (2 ^ 64 - 1 - fr_img f) -> getr regs3 23 = Z_to_bv 64 (2 ^ 64 - 1 - fr_img b) ->
getr regs3 12 = Z_to_bv 64 (cg_W s) -> getr regs3 13 = Z_to_bv 64 top -> getr regs3 26 = Z_to_bv 64 (hrow + 1) ->
getr regs3 3 = getr regs0 3 -> getr regs3 4 = getr regs0 4 ->
SR ubs0segs (mkCfg (mkst regs3 (Z_to_bv 64 FL_S3) mem3 (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md)).
{ intros regs3 mem3 top hrow c0 HJ3 K3 V48 V96 Htop Hhr Hc0 Hne VT0 VH1 VH2 R2 R8 R9 R18 R21 R23 R12 R13 R26 R3 R4.
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= cg_H s) by (subst h; clear - Hhr Htop; lia).
eapply SR_bind.
{ eapply (fl_s3V API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs3 mem3 top hrow c0 HJ3 K3 Hfi Hbi eq_refl ltac:(clear - HFSv; lia) Htop Hhr Hc0 Hne V96
R2 R8 R9 R18 R21 R23 R12 R13 R26). }
cbv beta. intros c' (regs4 & mem4 & left & -> & HJ4 & K4 & V64 & F4 & V96' & Hleft & Q26 & Q25 & Q20 & Q19 & Q24 & Q10 & HK4 & (VL1 & VL2)).
eapply SR_bind.
{ eapply (fl_s4lV API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Datatypes.S (Z.to_nat ((cg_W s - 1 - c0) * h + h))) top (cg_W s - 1) FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs4 mem4 top h c0 HJ4 K4 Hfi Hbi
ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hne ltac:(clear - Hh; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0 Hh; nia) V96'
ltac:(rewrite (HK4 2%bv ltac:(cbv; auto 20)); exact R2) ltac:(rewrite (HK4 8%bv ltac:(cbv; auto 20)); exact R8)
ltac:(rewrite (HK4 9%bv ltac:(cbv; auto 20)); exact R9) ltac:(rewrite (HK4 18%bv ltac:(cbv; auto 20)); exact R18)
ltac:(rewrite (HK4 21%bv ltac:(cbv; auto 20)); exact R21) ltac:(rewrite (HK4 23%bv ltac:(cbv; auto 20)); exact R23)
Q20 Q25 Q10 Q19 ltac:(rewrite Q24; f_equal; subst h; clear; lia)).
intros i2 x2 Hi2 Hx2. exfalso. clear - Hi2 Hx2. lia. }
cbv beta. intros c' (regs5 & mem5 & xr & -> & HJ5 & M5 & Hxr & Q25' & HK5 & (VR1 & VR2)).
assert (XD : fl_dims (gcfg_of s GPAL) cur (Some befr) = (xr + 1 - left, h, top, left)).
{ unfold fl_dims. rewrite XG2.
rewrite (diff_area_scan (gcfg_of s GPAL) cur befr (cg_W s) (cg_H s) _ (proj1 HW) (proj1 HH) eq_refl ltac:(pose proof HVALS as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & XL & _) & _ & _); rewrite XL; exact HN)
ltac:(pose proof HVALS as (_ & _ & HVb & _); cbn [oframe_relb] in HVb; pose proof HVb as (_ & _ & _ & _ & _ & _ & _ & _ & XL & _); rewrite XL; exact HN)
HD top hrow left xr ltac:(clear - Htop Hhr; lia) ltac:(clear - Hhr; lia) ltac:(clear - Hleft Hxr Hc0; lia) ltac:(clear - Hxr; lia)).
- subst h. reflexivity.
- exists c0. split; [exact Hc0 | exact Hne].
- intros p Hp Hd. apply Hd. apply VT0. exact Hp.
- exact VH1.
- intros p Hp Hd. apply Hd. apply VH2. rewrite HN. exact Hp.
- destruct VL1 as (i2 & Hi2 & Hd). exists i2. split; [exact Hi2 | exact Hd].
- intros i2 x2 Hi2 Hx2 Hd. apply Hd. apply (VL2 i2 x2 Hi2 Hx2).
- destruct VR1 as (i2 & Hi2 & Hd). exists i2. split; [subst h; exact Hi2 | exact Hd].
- intros i2 x2 Hi2 Hx2 Hd. apply Hd. apply (VR2 i2 x2); [subst h; exact Hi2 | exact Hx2]. }

apply (XS4 regs5 mem5 xr left top h HJ5 (KD_eq _ _ _ _ K4 M5)).
- intros k Hk. rewrite (mbyte_of_eq _ _ _ _ M5), F4 by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (V48 k Hk).
- intros k Hk. rewrite (mbyte_of_eq _ _ _ _ M5). exact (V64 k Hk).
- intros k Hk. rewrite (mbyte_of_eq _ _ _ _ M5). exact (V96' k Hk).
- clear - Hleft Hxr; lia.
- clear - Hxr; lia.
- exact (proj1 Hh).
- clear - Htop; lia.
- exact (proj2 Hh).
- rewrite (HK5 2%bv ltac:(cbv; auto 50)), (HK4 2%bv ltac:(cbv; auto 20)). exact R2.
- rewrite (HK5 9%bv ltac:(cbv; auto 50)), (HK4 9%bv ltac:(cbv; auto 20)). exact R9.
- rewrite (HK5 18%bv ltac:(cbv; auto 50)), (HK4 18%bv ltac:(cbv; auto 20)). exact R18.
- exact Q25'.
- rewrite (HK5 26%bv ltac:(cbv; auto 50)). exact Q26.
- rewrite (HK5 3%bv ltac:(cbv; auto 50)), (HK4 3%bv ltac:(cbv; auto 20)). exact R3.
- rewrite (HK5 4%bv ltac:(cbv; auto 50)), (HK4 4%bv ltac:(cbv; auto 20)). exact R4.
- exact XD. }
set (E := Ereg regs1 (map (Z_to_bv 64) [fr_img b] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fr_img b)) by (subst E; apply (Ereg_vals regs1 [fr_img b] [] 0%nat); reflexivity).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hq0 Hq1 Hac HFRv; lia).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; subst spv; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [clear - Hq1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_img b)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Hbimg0 Hbimg1 Hac HN1; lia); reflexivity | cbn; clear - Hbimg0 Hbimg1 Hac HN1; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs0segs memc (fr_ptr b) LAY_Frame (frame_vals b) 1 (8, 8%N) (fr_img b) Hbobj eq_refl eq_refl)). }
assert (HRa : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 48 56 48 56 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ); lia | constructor]. }
assert (HRb : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 88 112 88 96 [mkChunk 104 (CVal 8 (SOff 27 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ); lia |].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE 27%nat 27%bv eq_refl), G27, unsigned_lit_small by (clear - HW; lia); reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact W104]. }
assert (HFA : atoms_ok E [ (19%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 (CEIL_MAX - 40) 3); (2%nat, mkAF (CEIL_MIN + 8192) (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU18, HU2, (HE 19%nat 19%bv eq_refl), G19, unsigned_lit_small by (clear - HH; lia).
change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. clear - HH Hq0 Hq1 B8 Hac HFRv Hsp0 Hsp1 Hsp16. repeat split; lia. }
assert (HPD : pairwise_disjoint E (ss_mem ss_slow)).
{ cbn [ss_mem ss_slow pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU18, HU2.
clear - Hq1 Hsp0 Hac HFRv. repeat split; try exact I; lia. }
assert (HS : st_ok ubs0segs E ss_slow (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs0segs))).
{ unfold ss_slow. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HRa | constructor; [exact HRb | constructor]]] | exact HPD | exact HFA]. }
clear HR0 HRa HRb HFA HPD.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ FL_S1O.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (K1 : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ (KD_refl memc spv)). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [r_base r_wlo r_whi base_val]; rewrite ?HU18, ?HU2; clear - Hna2 Hna4; lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs0segs E ssx msx 1 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs48;
pose proof (st_region_chunks ubs0segs E ssx msx 2 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs88;
pose proof (regs_kept_of_st_ok ubs0segs E ssx msx regs1 _ [2; 3; 4; 9; 18; 19]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs0segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs48, Hcs88.
assert (V48 : word_mem ubs0segs (ms_mem ms) (spv + 48) np).
{ apply (chunk_word E _ _ 48 _ _ (proj1 (Forall_forall _ _) Hcs48 (mkChunk 48 (CVal 8 (SOff 20 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE 20%nat 20%bv eq_refl), G20, Z_to_bv_bv_unsigned; reflexivity | clear - Hnp; lia]. }
assert (U32 : U E (SOff 32 0) = fr_img b) by (apply (U_atom E 32 (fr_img b) HE32); clear - Hbimg0 Hbimg1 Hac HN1; lia).
assert (U9 : U E (SOff 9 0) = fr_img f) by (apply (U_atom E 9 (fr_img f)); [rewrite (HE 9%nat 9%bv eq_refl); exact G9 | clear - Hfimg0 Hfimg1 Hac HN1; lia]).
assert (V88 : word_mem ubs0segs (ms_mem ms) (spv + 88) 1).
{ apply (chunk_word E _ _ 88 _ _ (proj1 (Forall_forall _ _) Hcs88 (mkChunk 88 (CVal 8 (SAlu ALU_SLTU (SLit 0) (SOff 32 0)))) ltac:(cbn [In]; tauto))); [| clear; lia].
apply denot_of_U'. rewrite U_SAlu, U_SLit, U32. cbn [zalu_raw]. replace (zcanon 0) with 0 by reflexivity. rewrite (proj2 (Z.ltb_lt 0 (fr_img b))) by (clear - Hbimg0; lia). reflexivity. }
assert (A1_2 : getr (ms_regs ms) 2 = Z_to_bv 64 spv) by (rewrite (HKR0 2%bv ltac:(cbv; auto 20)); exact G2).
assert (A1_3 : getr (ms_regs ms) 3 = getr regs0 3) by (rewrite (HKR0 3%bv ltac:(cbv; auto 20)); exact G3).
assert (A1_4 : getr (ms_regs ms) 4 = getr regs0 4) by (rewrite (HKR0 4%bv ltac:(cbv; auto 20)); exact G4).
assert (A1_9 : getr (ms_regs ms) 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HKR0 9%bv ltac:(cbv; auto 20)); exact G9).
assert (A1_18 : getr (ms_regs ms) 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HKR0 18%bv ltac:(cbv; auto 20)); exact G18).
assert (A1_19 : getr (ms_regs ms) 19 = Z_to_bv 64 (cg_H s)) by (rewrite (HKR0 19%bv ltac:(cbv; auto 20)); exact G19).
assert (A1_8 : getr (ms_regs ms) 8 = Z_to_bv 64 (fr_img b)) by (apply (RG 8%bv 32%nat _ eq_refl); exact HE32).
assert (A1_20 : getr (ms_regs ms) 20 = Z_to_bv 64 (fr_img b)) by (apply (RG 20%bv 32%nat _ eq_refl); exact HE32).
assert (A1_27 : getr (ms_regs ms) 27 = Z_to_bv 64 (fr_img b)) by (apply (RG 27%bv 32%nat _ eq_refl); exact HE32).
assert (A1_24 : getr (ms_regs ms) 24 = Z_to_bv 64 (fr_img f)) by (apply (RG 24%bv 9%nat _ eq_refl); rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (A1_25 : getr (ms_regs ms) 25 = Z_to_bv 64 (fr_img f)) by (apply (RG 25%bv 9%nat _ eq_refl); rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (A1_10 : getr (ms_regs ms) 10 = Z_to_bv 64 (cg_W s)) by (apply (RG 10%bv 27%nat _ eq_refl); rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (A1_11 : getr (ms_regs ms) 11 = Z_to_bv 64 0) by (rewrite (RGX 11%bv (SLit 0) eq_refl); reflexivity).
assert (A1_22 : getr (ms_regs ms) 22 = Z_to_bv 64 1) by (rewrite (RGX 22%bv (SLit 1) eq_refl); reflexivity).
assert (A1_23 : getr (ms_regs ms) 23 = Z_to_bv 64 1).
{ rewrite (RGX 23%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_SAlu, U_SLit, U9. cbn [zalu_raw].
replace (zcanon 0) with 0 by reflexivity. rewrite (proj2 (Z.ltb_lt 0 (fr_img f))) by (clear - Hfimg0; lia). reflexivity. }
clear HKR0 RG RGX Hcs48 Hcs88 U32 U9.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc ss_slow].
eapply SR_bind.
{ eapply (fl_s1oV API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Z.to_nat (cg_H s)) 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) HJ K1 Hfi Hbi eq_refl ltac:(clear - HFSv; lia)
ltac:(clear; lia) ltac:(clear - HH; lia) ltac:(clear - HH; lia) V88 A1_2 A1_8 A1_9 A1_18
ltac:(rewrite A1_24; f_equal; clear; lia) ltac:(rewrite A1_25; f_equal; clear; lia)
ltac:(rewrite A1_27; f_equal; clear; lia) ltac:(rewrite A1_20; f_equal; clear; lia)
A1_23 A1_11 A1_10).
intros p Hp. exfalso. clear - Hp. lia. }
cbv beta. intros c' (regs2 & mem2 & pc2 & -> & HJ2 & K2 & F2 & Hpc2 & HK2).
assert (V48b : word_mem ubs0segs mem2 (spv + 48) np).
{ intros k Hk. rewrite F2 by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (V48 k Hk). }
assert (P2 : getr regs2 2 = Z_to_bv 64 spv) by (rewrite (HK2 2%bv ltac:(cbv; auto 20)); exact A1_2).
assert (P3 : getr regs2 3 = getr regs0 3) by (rewrite (HK2 3%bv ltac:(cbv; auto 20)); exact A1_3).
assert (P4 : getr regs2 4 = getr regs0 4) by (rewrite (HK2 4%bv ltac:(cbv; auto 20)); exact A1_4).
assert (P8 : getr regs2 8 = Z_to_bv 64 (fr_img b)) by (rewrite (HK2 8%bv ltac:(cbv; auto 20)); exact A1_8).
assert (P9 : getr regs2 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK2 9%bv ltac:(cbv; auto 20)); exact A1_9).
assert (P18 : getr regs2 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK2 18%bv ltac:(cbv; auto 20)); exact A1_18).
clear HK2.
destruct Hpc2 as [[-> (top & c0 & Htop & Hc0 & Hne & Q12 & Q13 & Q26 & V96 & VT0)] | (-> & Q10 & VID)].
- eapply SR_bind.
{ eapply (fl_s2V API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs2 mem2 top HJ2 K2 Hfi Hbi eq_refl ltac:(clear - HFSv; lia) Htop V96 P2 P8 P9 P18 Q12 Q13 Q26).
exists c0. split; [exact Hc0 | exact Hne]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & K3 & F3 & (hrow & Hhr & Q26' & (VH1 & VH2)) & Q12' & Q13' & V96' & Q21 & Q23 & HK3).
apply (XS3 regs3 mem3 top hrow c0 HJ3 K3).
+ intros k Hk. unfold s2_frame in F3. rewrite F3 by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (V48b k Hk).
+ exact V96'.
+ clear - Htop Hhr; lia.
+ exact (proj2 Hhr).
+ exact Hc0.
+ exact Hne.
+ exact VT0.
+ exact VH1.
+ exact VH2.
+ rewrite (HK3 2%bv ltac:(cbv; auto 20)). exact P2.
+ rewrite (HK3 8%bv ltac:(cbv; auto 20)). exact P8.
+ rewrite (HK3 9%bv ltac:(cbv; auto 20)). exact P9.
+ rewrite (HK3 18%bv ltac:(cbv; auto 20)). exact P18.
+ exact Q21.
+ exact Q23.
+ exact Q12'.
+ exact Q13'.
+ exact Q26'.
+ rewrite (HK3 3%bv ltac:(cbv; auto 20)). exact P3.
+ rewrite (HK3 4%bv ltac:(cbv; auto 20)). exact P4.
- exact (XID regs2 mem2 HJ2 K2 V48b P2 P9 P18 Q10 P3 P4 VID).
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
