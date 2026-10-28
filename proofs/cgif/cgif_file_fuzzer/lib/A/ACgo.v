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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
unfold w64; apply (shq_word Ex n 38 c _ SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGVE-ALU" r; fail
| |- _ =>
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| idtac "REGVE-FAIL" r; fail ]
end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
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
Section e.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition af_preX (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N fattr : Z) (E : env) (ms1 : machine_state) md1 : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPn g) ly S W mem md [] ly S W (ms_mem ms1) md1 0 /\
af_side (mrestrict (w_H W) (ms_mem ms1)) g s /\
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms1)) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)) /\
(cg_cur s = 0 \/ cg_cur s = R_PENDING) /\
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) /\
ew E 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0) /\
(cg_ihead s = 1 \/ cg_ihead s = 2).
Definition af_xc (s : cgif_st) (fattr fgen delay nlp tidx : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) : Prop :=
cgif_live gs /\ gsF = YI0b.af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs.
Definition af_xok (s : cgif_st) (fattr fgen delay nlp tidx : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) : Prop :=
cgif_live gs /\ gsF = YI0b.af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs.
Definition af_xnums : Prop :=
(forall N, 1 <= N <= 100000000 -> xm_flush XN N + 3 * mo_free MT + mo_malloc MT 40 + mo_malloc MT N + mo_malloc MT 196605 <= xm_addframe XN N) /\
(forall N, 1 <= N <= 100000000 -> xn_flush XN N + 3 * mo_free MT + mo_malloc MT 40 + mo_malloc MT N + mo_malloc MT 196605 <= xn_addframe XN N) /\
(forall N, 1 <= N <= 100000000 -> 0 <= xn_flush XN N <= xm_flush XN N).
Definition AF_C_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_preX B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
st_ok_pi SEGS VAL E (xs_C (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_B_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_preX B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E (xs_B (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_OK_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_preX B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
st_ok_pi SEGS VAL E (xs_OK (cg_ihead s)) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
End e.
Section h.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Lemma af_liftN : forall ly S W (regs : bvmap 5 word) mem md ch g s N own ly' S' W' mem' md' k,
afn_pre SEGS B TADDFRAME_STK ly S W regs mem md ch ->
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPn g) ly S W mem md own ly' S' W' mem' md' k ->
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPb g s N) ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros ly S W regs mem md ch g s N own ly' S' W' mem' md' k HPRE HJ.
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low TADDFRAME_STK (spZ regs) (FPb g s N) ly S W mem md [] ly S W mem md 0
TADDFRAME_STK (spZ regs) (FPn g) own ly' S' W' mem' md' k
(ajournal_init SEGS B TADDFRAME_STK _ ly S W regs mem md ch HPRE) HJ ltac:(lia) ltac:(lia)
ltac:(intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; left; unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left;
unfold ablocks_fp, cgif_blocks; cbn [map fst snd app]; exists (g, g + req_size CGIF_SIZE);
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia])) as HJ'.
rewrite app_nil_r in HJ'. exact HJ'.
Qed.
Lemma af_xrel_N : forall sp0 ly S W mem md own W' mem' md' k g s N img lpa fattr nlp rest GPAL IMG LPAL gs,
ajournal SEGS B TADDFRAME_STK sp0 (FPn g) ly S W mem md own ly S W' mem' md' k ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ af_cblocks img N fattr lpa nlp rest) -> In (pf, FILE_BLOCK) rest -> cgif_wf s N ->
af_xrel K (mrestrict (w_H W) mem) md s N img lpa fattr nlp GPAL IMG LPAL gs -> af_xrel K (mrestrict (w_H W') mem') md' s N img lpa fattr nlp GPAL IMG LPAL gs.
Proof.
intros sp0 ly S W mem md own W' mem' md' k g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HP Hpf Hwf (XR & XGI & XGIL & XGL).
set (cb := af_cblocks img N fattr lpa nlp rest) in *.
assert (HP' : Permutation (ablocks B ly S) (af_wblocks g s ++ (af_xvblocks s N ++ cb))).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_tail; apply cgif_blocks_wv|]. rewrite <- app_assoc. apply Permutation_refl. }
assert (KL : forall a n j, In (a, n) (af_xvblocks s N ++ cb) -> 0 <= j < n -> mbyte SEGS (mrestrict (w_H W') mem') (a + j) = mbyte SEGS (mrestrict (w_H W) mem) (a + j)).
{ apply (af_subj_kept B TADDFRAME_STK sp0 (FPn g) ly S W mem md own ly S W' mem' md' k _ HJ).
- intros x Hx. assert (Hl : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; right; exact Hx). split; exact Hl.
- intros p n j Hin Hj (r & [<- | []] & Hr). cbn [fst snd] in Hr.
pose proof (asep_app B LAWS ly S W' mem' md' _ _ (g, CGIF_SIZE) (p, n) (proj1 HJ) HP' ltac:(left; reflexivity) Hin) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. lia. }
assert (Hpfl : In (pf, FILE_BLOCK) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. apply in_app_iff. right. apply in_app_iff. right. unfold cb, af_cblocks. right. apply in_app_iff. right. exact Hpf. }
split; [| split; [| split; [exact XGIL|]]].
- apply (proj1 (cgif_relA_split SEGS K _ _ s pf N GPAL gs)) in XR as (X1 & XS & XL). apply (proj2 (cgif_relA_split SEGS K _ _ s pf N GPAL gs)).
split; [exact X1|]. split.
+ eapply (asink_at_kept SEGS B K AIL); [exact HJ | apply sink_closed_pos; constructor; [cbn [fst]; pose proof (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJ) ltac:(eapply Permutation_in; [apply Permutation_sym; exact HP'|]; left; reflexivity)) as (_ & Hg & _); lia | constructor] | exact Hpfl | exact Hpfl | | exact XS].
intros j Hj (r & [<- | []] & Hr). cbn [fst snd] in Hr.
pose proof (asep_app B LAWS ly S W' mem' md' _ _ (g, CGIF_SIZE) (pf, FILE_BLOCK) (proj1 HJ) HP' ltac:(left; reflexivity)
ltac:(apply in_app_iff; right; unfold cb, af_cblocks; right; apply in_app_iff; right; exact Hpf)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. unfold FILE_BLOCK in Hj. lia.
+ intros Hl. apply (af_xlive_kept SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') s N GPAL gs Hwf); [| exact (XL Hl)].
intros a n j Hin Hj. apply (KL a n j); [apply in_app_iff; left; exact Hin | exact Hj].
- eapply garr8_frame; [exact XGI|]. intros a Ha. replace a with (img + (a - img)) by lia. apply (KL img N); [apply in_app_iff; right; left; reflexivity | lia].
- intros Hz. destruct (XGL Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (lpa + (a - lpa)) by lia. apply (KL lpa (3 * nlp)); [| lia]. apply in_app_iff. right. unfold cb, af_cblocks. right. apply in_app_iff. left.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
Qed.
Lemma af_xrel_d : forall (m : word -> option byte) md s N (i : Z) img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs,
(i = 1 \/ i = 2) -> cgif_wf s N -> cgif_live gs ->
af_xrel K m md s N img lpa fattr nlp GPAL IMG LPAL gs ->
nth (Z.to_nat i) (cg_frames s) None = None -> (i = 2 -> nth 1 (cg_frames s) None <> None) ->
af_xdv K m md s s N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs (YI0b.af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs).
Proof.
intros m md s N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs Hi Hwf XLV (XR & XGI & XGIL & XGL) Hnone Hs1.
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as ((_ & XOCC) & XS & XL).
pose proof (proj1 (af_xlive_iff SEGS m s N GPAL gs) (XL XLV)) as [XH XSL]. pose proof XH as (_ & _ & XHih & _).
pose proof (proj1 (cgif_occ_iff s gs) XOCC) as XO.
pose proof Hwf as (_ & HW1 & HH1 & HN & _ & _ & Hq & _).
assert (Xi0 : YI0b.af_i0 gs = i).
{ unfold YI0b.af_i0, YO07.q_get. rewrite <- XHih.
pose proof (XO 1%nat ltac:(lia)) as O1. pose proof (XO 2%nat ltac:(lia)) as O2. cbn [qslot] in O1, O2.
destruct Hi as [-> | ->]; change (Z.to_nat 1) with 1%nat in Hnone; change (Z.to_nat 2) with 2%nat in Hnone.
- assert (E1 : cg_ihead s = 1) by (destruct Hq as [E | [_ Hn]]; [exact E | exfalso; exact (Hn Hnone)]).
rewrite E1. cbn. rewrite (proj1 O1 Hnone). reflexivity.
- pose proof (Hs1 eq_refl) as Hn1. destruct Hq as [E | [E _]]; rewrite E; cbn.
+ destruct (YO07.s_q1 gs) as [F|] eqn:Eq1; [| exfalso; exact (Hn1 (proj2 O1 eq_refl))]. rewrite (proj1 O2 Hnone). reflexivity.
+ rewrite (proj1 O2 Hnone). reflexivity. }
rewrite (YI0b.af_rest_free (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs ltac:(rewrite Xi0; destruct Hi as [-> | ->]; discriminate)), Xi0.
assert (Hin : (Z.to_nat i = 1 \/ Z.to_nat i = 2)%nat) by (destruct Hi as [-> | ->]; [left | right]; reflexivity).
pose proof (YI0b.af_tail_facts (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs (Z.to_nat i) Hin) as TF. cbv zeta in TF.
rewrite (Z2Nat.id i ltac:(destruct Hi as [-> | ->]; lia)) in TF. destruct TF as (TF1 & TF2 & TF3 & TF4 & TF5 & TF6 & TF7).
unfold af_xdv.
split; [rewrite TF3; exact XS|]. split; [exact XH|]. split; [exact TF2|]. split; [exact TF4|].
split; [exact (af_xslots_mono SEGS m s N gs _ _ (fun k _ => I) XSL)|].
split; [exact TF7|].
split; [rewrite TF6; unfold af_fb2, af_fb3; cbn [gcfg_of YO07.g_attr]; destruct (YO07.flag fattr 2), (YO07.flag (cg_attr s) 8); reflexivity|].
split; [exact TF1|]. split; [exact TF5|]. split; [exact XGI|]. split; [exact XGIL|]. split; [exact XGL|].
unfold af_xout. rewrite TF3. unfold FRAME_OUT. clear - HW1 HH1 HN. nia.
Qed.
Lemma af_xmtr0 : forall S N nlp, af_xnums MT XN -> 1 <= N <= 100000000 -> 0 <= nlp < 65536 ->
af_xmtr MT XN S S N (xm_flush XN N + af_needF MT N nlp) (xn_flush XN N + af_needF MT N nlp) /\
af_xmtr MT XN S S N (af_need1 MT N nlp) (af_need1 MT N nlp).
Proof.
intros S N nlp (HXM & HXN & HXMN) HN Hnlp.
pose proof (HXM N HN) as BM. pose proof (HXN N HN) as BN. pose proof (HXMN N HN) as BMN. pose proof (mo_free_nonneg MT MLAW) as Hf0.
pose proof (mo_malloc_mono MT MLAW (3 * nlp) 196605 ltac:(lia)) as Hm.
unfold af_needF, af_need1, af_need2, af_need3.
split; exists 0; (split; [lia|]); (split; [exact (mle_start MT S MLAW)|]); split; lia.
Qed.
Lemma af_preX_agree : forall ly S W regs mem md g cfp s N fattr E E' ms1 md1,
af_preX B ly S W regs mem md g cfp s N fattr E ms1 md1 -> (forall n, (n < 512)%nat -> ew E' n = ew E n) ->
af_preX B ly S W regs mem md g cfp s N fattr E' ms1 md1.
Proof.
intros ly S W regs mem md g cfp s N fattr E E' ms1 md1 (H1 & H2 & H3 & H4 & H5 & H6 & H7) HA.
repeat (split; [assumption|]). split; [|exact H7]. rewrite HA by lia. exact H6.
Qed.
Lemma af_xok_c : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF,
cgif_relA SEGS K m md s pf N GPAL gs -> nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = None -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF -> af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XR Hnone Hih [XLV XGF]. split; [exact XLV|]. rewrite XGF.
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as ((_ & XOCC) & _ & XL).
destruct (XL XLV) as (_ & _ & XHih & _). pose proof (proj1 (cgif_occ_iff s gs) XOCC) as XO.
unfold YI0b.af_from_merge, YI0b.af_merged. rewrite <- XHih.
assert (Hk : (Z.to_nat (cg_ihead s) < 3)%nat) by (destruct Hih as [-> | ->]; cbv; lia).
rewrite <- (Z2Nat.id (cg_ihead s)) at 1 by (destruct Hih as [-> | ->]; lia).
rewrite (YI0b.qslot_get gs _ Hk), (proj1 (XO _ Hk) Hnone). reflexivity.
Qed.
Lemma af_xlive_cur : forall s gs, (cg_cur s = 0 \/ cg_cur s = R_PENDING) -> rc_int (cg_cur s) = YO07.s_cur gs -> cgif_live gs.
Proof. intros s gs [E | E] H; rewrite E in H; [left | right]; rewrite <- H; reflexivity. Qed.
Lemma af_xleaf_dead : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs,
cgif_relA SEGS K m md s pf N GPAL gs -> 0 <= cg_cur s < 2 ^ 32 -> cg_cur s <> 0 -> cg_cur s <> 6 -> 1 <= N ->
cgif_relA SEGS K m md (cl_set_cur s (cg_cur s)) pf N GPAL (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) /\
af_xout gs (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) N.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs XR Rc H0 H6 HN.
assert (XCUR : rc_int (cg_cur s) = YO07.s_cur gs) by (exact (proj1 (proj1 (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs) XR)))).
assert (E : YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG = gs).
{ rewrite YI0b.add_frame_split. rewrite <- XCUR. unfold rc_int, YO07.C_OK, YO07.C_PENDING.
destruct (Z.ltb_spec (cg_cur s) (2 ^ 31));
[ rewrite (proj2 (Z.eqb_neq _ _)) by lia; rewrite (proj2 (Z.eqb_neq (cg_cur s) 6)) by lia
| rewrite (proj2 (Z.eqb_neq _ _)) by lia; rewrite (proj2 (Z.eqb_neq (cg_cur s - 2 ^ 32) 6)) by lia ]; reflexivity. }
rewrite E. replace (cl_set_cur s (cg_cur s)) with s by (destruct s; reflexivity).
split; [exact XR | unfold af_xout, FRAME_OUT; lia].
Qed.
Lemma af_xleaf_err : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs cv,
cgif_relA SEGS K m md s pf N GPAL gs -> cgif_live gs -> YI0b.af_err (gcfg_of s GPAL) fattr = true -> rc_int cv = YO07.C_ERROR -> 1 <= N ->
cgif_relA SEGS K m md (cl_set_cur s cv) pf N GPAL (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) /\
af_xout gs (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) N.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs cv XR XLV XE Hcv HN.
assert (E : YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG = YO07.with_cur gs YO07.C_ERROR).
{ rewrite YI0b.add_frame_split, XE.
destruct XLV as [E0 | E0]; rewrite E0; reflexivity. }
rewrite E. split; [| unfold af_xout, FRAME_OUT; cbn [YO07.with_cur YO07.s_out]; lia].
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as ((_ & XOCC) & XS & _).
apply (proj2 (cgif_relA_split SEGS K m md (cl_set_cur s cv) pf N GPAL (YO07.with_cur gs YO07.C_ERROR))).
split; [split; [exact Hcv | apply (proj2 (cgif_occ_set_cur s cv _)); exact XOCC]|].
split; [exact XS|]. intros [HL | HL]; cbn [YO07.with_cur YO07.s_cur] in HL; discriminate HL.
Qed.
Lemma af_xleaf_ok : forall s fattr fgen delay nlp tidx GPAL IMG LPAL gs,
cgif_live gs -> YI0b.af_err (gcfg_of s GPAL) fattr = false ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG).
Proof.
intros s fattr fgen delay nlp tidx GPAL IMG LPAL gs XLV XE. split; [exact XLV|].
rewrite YI0b.add_frame_split, XE. destruct XLV as [E0 | E0]; rewrite E0; reflexivity.
Qed.
Lemma af_xmle0 : forall S N, af_xnums MT XN -> 1 <= N <= 100000000 -> mo_le MT S S (xn_addframe XN N).
Proof.
intros S N (_ & HXN & HXMN) HN. pose proof (HXN N HN) as BN. pose proof (HXMN N HN) as BMN. pose proof (mo_free_nonneg MT MLAW) as Hf0.
pose proof (mo_malloc_nonneg MT MLAW 40 ltac:(lia)). pose proof (mo_malloc_nonneg MT MLAW N ltac:(lia)). pose proof (mo_malloc_nonneg MT MLAW 196605 ltac:(lia)).
exact (mle_weaken MT S S 0 (xn_addframe XN N) MLAW (mle_start MT S MLAW) ltac:(lia)).
Qed.
Lemma af_land6 : forall x, 0 <= x -> (Z.land x 6 = 6 <-> (Z.land x 2 <> 0 /\ Z.land x 4 <> 0)).
Proof.
intros x Hx.
assert (E : forall m, Z.land 7 m = m -> Z.land x m = Z.land (x mod 8) m).
{ intros m Hm. change 8 with (2 ^ 3). rewrite <- (Z.land_ones x 3) by lia. change (Z.ones 3) with 7. rewrite <- Z.land_assoc, Hm. reflexivity. }
rewrite (E 6 eq_refl), (E 2 eq_refl), (E 4 eq_refl).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hr. set (r := x mod 8) in *. clearbody r.
assert (Hc : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn; (split; [intros H; first [discriminate H | split; discriminate] | intros [H2 H4]; first [reflexivity | exfalso; first [apply H2; reflexivity | apply H4; reflexivity]]]).
Qed.
End h.
End d.
End b.
