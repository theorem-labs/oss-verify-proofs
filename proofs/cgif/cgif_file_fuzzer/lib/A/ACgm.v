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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
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
Section h.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition af_needF (N nlp : Z) : Z := 3 * mo_free MT + af_need1 MT N nlp.
Definition af_xrel (m : word -> option byte) (md : Model) (s1 : cgif_st) (N img lpa fattr nlp : Z) (GPAL IMG LPAL : list Z) (gs : YO07.gif_st) : Prop :=
cgif_relA SEGS K m md s1 pf N GPAL gs /\
garr8 SEGS m img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 SEGS m lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp).
Definition af_xfl (S Sc : astate) (m : word -> option byte) (md : Model) (s s1 : cgif_st) (N img lpa fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) : Prop :=
af_xrel m md s1 N img lpa fattr nlp GPAL IMG LPAL gs /\ cgif_live gs /\
gsF = YI0b.af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs /\
af_xmtr MT XN S Sc N (xm_flush XN N + af_needF N nlp) (xn_flush XN N + af_needF N nlp).
Definition af_xq (m : word -> option byte) (md : Model) (s2 : cgif_st) (N : Z) (f1' f2 : frame_st) (F1 F2 : YO07.frame)
(img lpa fattr nlp : Z) (GPAL IMG LPAL Sg : list Z) : Prop :=
asink_at SEGS K m md pf Sg /\
(Z.land (cg_attr s2) 4 = 0 -> garr8 SEGS m (cg_pal s2) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s2) /\
frame_relbA SEGS false m N f1' F1 /\ frame_relbA SEGS true m N f2 F2 /\
garr8 SEGS m img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 SEGS m lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp).
Definition AF_FL_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (f1 : frame_st) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= 1 ->
blocks_bytes Sc <= blocks_bytes S ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
nth 1 (cg_frames s1) None = Some f1 -> nth 2 (cg_frames s1) None <> None ->
af_xfl S Sc (rdW Wc memc) mdc s s1 N img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_FL)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
End h.
Section i.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Lemma rc_int_range : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= rc_int v < 2 ^ 31.
Proof. intros v Hv. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma rc_int_mod32 : forall c, - 2 ^ 31 <= c < 2 ^ 31 -> rc_int (c mod 2 ^ 32) = c.
Proof.
intros c Hc. unfold rc_int. destruct (Z_lt_le_dec c 0).
- replace (c mod 2 ^ 32) with (c + 2 ^ 32) by (symmetry; rewrite <- (Z.mod_add c 1 (2 ^ 32)) by lia; apply Z.mod_small; lia).
destruct (Z.ltb_spec (c + 2 ^ 32) (2 ^ 31)); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec c (2 ^ 31)); lia.
Qed.
Lemma af_code_reg : forall r code, 0 <= r < 2 ^ 64 -> Z_to_bv 64 r = Z_to_bv 64 code -> - 2 ^ 31 <= code < 2 ^ 31 ->
(r = 0 <-> code = 0) /\ rc_int (r mod 2 ^ 32) = code.
Proof.
intros r code Hr He Hc.
assert (Hr64 : r = code mod 2 ^ 64).
{ rewrite <- (unsigned_lit_small r) by lia. rewrite He, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
destruct (Z_lt_le_dec code 0) as [Hn | Hp].
- assert (E : code mod 2 ^ 64 = code + 2 ^ 64) by (rewrite <- (Z.mod_add code 1 (2 ^ 64)) by lia; apply Z.mod_small; lia).
rewrite E in Hr64. split; [lia|]. rewrite Hr64.
replace ((code + 2 ^ 64) mod 2 ^ 32) with (code mod 2 ^ 32); [apply rc_int_mod32; exact Hc|].
change (2 ^ 64) with (4294967296 * 2 ^ 32). rewrite Z.mod_add by lia. reflexivity.
- rewrite Z.mod_small in Hr64 by lia. subst r. split; [tauto|]. apply rc_int_mod32. exact Hc.
Qed.
Lemma af_rest_flushed : forall (G : YO07.gcfg) fattr fgen delay tidx nlp LPAL IMG gs F1 F2 code bytes,
YO07.s_q1 gs = Some F1 -> YO07.s_q2 gs = Some F2 -> (YO07.s_ihead gs = 1 \/ YO07.s_ihead gs = 2) ->
YO07.flush_frame G (YO07.s_rcur gs) F1 (YO07.s_q0 gs) = (code, bytes) ->
YI0b.af_rest G fattr fgen delay tidx nlp LPAL IMG gs =
if code =? YO07.C_OK
then YI0b.af_tail G fattr fgen delay tidx nlp LPAL IMG (YO07.mkS (Some F1) (Some F2) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2
else YO07.mkS None (Some F1) (Some F2) (YO07.s_ihead gs) code code (YO07.s_out gs).
Proof.
intros G fattr fgen delay tidx nlp LPAL IMG gs F1 F2 code bytes Hq1 Hq2 Hih Hff.
assert (Xi0 : YI0b.af_i0 gs = 3).
{ unfold YI0b.af_i0, YO07.q_get. destruct Hih as [E | E]; rewrite E; cbn; rewrite ?Hq1, ?Hq2; reflexivity. }
rewrite (YI0b.af_rest_full G fattr fgen delay tidx nlp LPAL IMG gs F1 Xi0 Hq1), Hff, Hq1, Hq2. cbv beta iota zeta.
assert (Hrc' : (if negb (YO07.s_rcur gs =? YO07.R_OK) && negb (YO07.s_rcur gs =? YO07.R_PENDING) then YO07.s_rcur gs else code) = code).
{ destruct (negb (YO07.s_rcur gs =? YO07.R_OK) && negb (YO07.s_rcur gs =? YO07.R_PENDING)) eqn:ED; [| reflexivity].
pose proof (YI0b.flush_frame_dead G (YO07.s_rcur gs) F1 (YO07.s_q0 gs) ED) as D. rewrite Hff in D. injection D as D1 D2. symmetry. exact D1. }
rewrite Hrc'. reflexivity.
Qed.
Lemma af_flush_code : forall (G : YO07.gcfg) rcur F1 b code bytes,
YO07.flush_frame G rcur F1 b = (code, bytes) -> - 2 ^ 31 <= rcur < 2 ^ 31 ->
- 2 ^ 31 <= code < 2 ^ 31 /\ (code <> YO07.C_OK -> code <> YO07.C_PENDING) /\ (code <> YO07.C_OK -> bytes = []).
Proof.
intros G rcur F1 b code bytes Hff Rrc.
split; [| split; [| intros Hc; exact (flush_frame_fail_nil G rcur F1 b code bytes Hff Hc)]];
(destruct (negb (rcur =? YO07.R_OK) && negb (rcur =? YO07.R_PENDING)) eqn:ED;
[ pose proof (YI0b.flush_frame_dead G rcur F1 b ED) as D; rewrite Hff in D; injection D as Ec Eb;
apply andb_prop in ED as [E1 E2]; unfold YO07.R_OK, YO07.R_PENDING, YO07.C_OK, YO07.C_PENDING in *;
destruct (Z.eqb_spec rcur 0); [discriminate E1|]; destruct (Z.eqb_spec rcur 6); [discriminate E2|]; clear - Rrc Ec n n0; lia
| destruct (YI0b.flush_frame_code_live G _ _ _ _ _ Hff ED) as [Ec|[Ec|Ec]]; rewrite Ec; unfold YO07.R_ERROR, YO07.R_EINDEX, YO07.R_OK, YO07.C_OK, YO07.C_PENDING; lia ]).
Qed.
Lemma af_unz_kept : forall H (m m' : word -> option byte) (L : list (Z * Z)) (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) L -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
forall a n k, In (a, n) L -> 0 <= k < n -> mbyte SEGS (mrestrict H m') (a + k) = mbyte SEGS (mrestrict H m) (a + k).
Proof.
intros H m m' L Zs UN XZb a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k Hin ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn).
Qed.
Lemma af_subj_kept : forall STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 (L : list (Z * Z)),
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 ->
(forall x, In x L -> In x (ablocks B lyc Sc) /\ In x (ablocks B ly2 S2)) ->
(forall p n k, In (p, n) L -> 0 <= k < req_size n -> ~ inFP FP1 (p + k)) ->
forall a n k, In (a, n) L -> 0 <= k < n -> mbyte SEGS (mrestrict (w_H W2) mem2) (a + k) = mbyte SEGS (mrestrict (w_H W) memT) (a + k).
Proof.
intros STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 L HJ HL HnF a n k Hin Hk. apply (mbyte_of_aview SEGS).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). destruct (HL _ Hin) as [Hl1 Hl2].
assert (Hk' : 0 <= k < req_size n) by (pose proof (req_size_pos n); lia).
exact (F2 a n k Hl1 Hl2 Hk' (HnF a n k Hin Hk')).
Qed.
Lemma af_xq_keptL : forall (m m' : word -> option byte) md md' s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg Sg' (L : list (Z * Z)),
(forall a n k, In (a, n) L -> 0 <= k < n -> mbyte SEGS m' (a + k) = mbyte SEGS m (a + k)) ->
In (img, N) L -> (Z.land fattr 1 <> 0 -> In (lpa, 3 * nlp) L) ->
(Z.land (cg_attr s2) 4 = 0 -> In (cg_pal s2, 3 * cg_ngp s2) L) ->
(forall b, In b (af_xfvb N (Some f1')) -> In b L) -> (forall b, In b (af_xfvb N (Some f2)) -> In b L) ->
asink_at SEGS K m' md' pf Sg' ->
af_xq K m md s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg -> af_xq K m' md' s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg'.
Proof.
intros m m' md md' s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg Sg' L KL Hi Hl Hp Hf1 Hf2 XS' (XS & XP & XR1 & XR2 & XGI & XGIL & XGL).
assert (KF : forall wg f F, (forall b, In b (af_xfvb N (Some f)) -> In b L) -> frame_relbA SEGS wg m N f F -> frame_relbA SEGS wg m' N f F).
{ intros wg f F Hf HR. apply (frame_relb_kept SEGS wg m m' N f F); [| | exact HR].
- intros k Hk. apply (KL (fr_img f) N k); [apply Hf; left; reflexivity | exact Hk].
- intros Hz k Hk. apply (KL (fr_lpal f) (3 * fr_nlp f) k); [| exact Hk]. apply Hf. cbn [af_xfvb]. right.
destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]. }
split; [exact XS'|]. split; [| split; [exact (KF false f1' F1 Hf1 XR1) | split; [exact (KF true f2 F2 Hf2 XR2) | split; [| split; [exact XGIL|]]]]].
- intros Hz. destruct (XP Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s2 + (a - cg_pal s2)) by lia. apply (KL (cg_pal s2) (3 * cg_ngp s2)); [exact (Hp Hz) | lia].
- eapply garr8_frame; [exact XGI|]. intros a Ha. replace a with (img + (a - img)) by lia. apply (KL img N); [exact Hi | lia].
- intros Hz. destruct (XGL Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (lpa + (a - lpa)) by lia. apply (KL lpa (3 * nlp)); [exact (Hl Hz) | lia].
Qed.
Lemma af_xrel_unz : forall H (m m' : word -> option byte) md md' s1 N img lpa fattr nlp GPAL IMG LPAL gs cb (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> In (img, N) cb -> (Z.land fattr 1 <> 0 -> In (lpa, 3 * nlp) cb) -> cgif_wf s1 N ->
m_fs md' = m_fs md -> m_fds md' = m_fds md ->
af_xrel K (mrestrict H m) md s1 N img lpa fattr nlp GPAL IMG LPAL gs -> af_xrel K (mrestrict H m') md' s1 N img lpa fattr nlp GPAL IMG LPAL gs.
Proof.
intros H m m' md md' s1 N img lpa fattr nlp GPAL IMG LPAL gs cb Zs UN XZb XZi Hpf Hi Hl Hwf Efs Efd (XR & XGI & XGIL & XGL).
pose proof (af_unz_kept H m m' _ Zs UN XZb) as KL.
split; [exact (cgif_relA_unz B K AIL H m m' md md' s1 N cb GPAL gs Zs UN XZb XZi Hpf Hwf Efs Efd XR)|].
split; [| split; [exact XGIL|]].
- eapply garr8_frame; [exact XGI|]. intros a Ha. replace a with (img + (a - img)) by lia. apply (KL img N); [apply in_app_iff; right; exact Hi | lia].
- intros Hz. destruct (XGL Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (lpa + (a - lpa)) by lia. apply (KL lpa (3 * nlp)); [apply in_app_iff; right; exact (Hl Hz) | lia].
Qed.
Lemma af_xq_intro : forall (m : word -> option byte) md s1 N o0 f1 f2 F1 F2 gen' rwcur' img lpa fattr nlp GPAL IMG LPAL gs,
cg_frames s1 = [o0; Some f1; Some f2] -> YO07.s_q1 gs = Some F1 -> YO07.s_q2 gs = Some F2 -> cgif_live gs ->
af_xrel K m md s1 N img lpa fattr nlp GPAL IMG LPAL gs ->
af_xq K m md (flush_upd s1 1 gen' rwcur') N (set_fr_gen f1 gen') f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL (concat (YO07.s_out gs)).
Proof.
intros m md s1 N o0 f1 f2 F1 F2 gen' rwcur' img lpa fattr nlp GPAL IMG LPAL gs Hfr Hq1 Hq2 XLV (XR & XGI & XGIL & XGL).
apply (proj1 (cgif_relA_split SEGS K m md s1 pf N GPAL gs)) in XR as (_ & XS & XL).
destruct (XL XLV) as (_ & _ & _ & XP & _ & R1 & R2). rewrite Hfr in R1, R2. cbn [nth] in R1, R2. rewrite Hq1 in R1. rewrite Hq2 in R2. cbn [oframe_relbA] in R1, R2.
split; [exact XS|]. split; [exact XP|]. split; [| split; [exact R2 | split; [exact XGI | split; [exact XGIL | exact XGL]]]].
pose proof (frame_relbA_weaken SEGS true m N f1 F1 R1) as R1'. exact R1'.
Qed.
Lemma af_xq_d : forall (m : word -> option byte) md s s2 N f1' f2 F1 F2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs code bytes ih cur,
af_xq K m md s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL (concat (YO07.s_out gs) ++ bytes) ->
rc_int (rw_cur s2) = code -> rw_attr s2 = raw_attr_of (cg_attr s2) -> cg_ihead s2 = ih ->
Z.of_nat (length bytes) <= FRAME_OUT N ->
af_xdv K m md s (set_frames s2 [Some f1'; Some f2; None]) N 2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs
(YO07.mkS (Some F1) (Some F2) None ih cur code (YO07.s_out gs ++ [bytes]))
(YI0b.af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG (YO07.mkS (Some F1) (Some F2) None ih cur code (YO07.s_out gs ++ [bytes])) 2).
Proof.
intros m md s s2 N f1' f2 F1 F2 img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs code bytes ih cur (XS & XP & XR1 & XR2 & XGI & XGIL & XGL) Hrc Hra Hih Hlb.
pose proof (YI0b.af_tail_facts (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG (YO07.mkS (Some F1) (Some F2) None ih cur code (YO07.s_out gs ++ [bytes])) 2%nat (or_intror eq_refl)) as TF.
cbv zeta in TF. change (Z.of_nat 2) with 2 in TF. destruct TF as (TF1 & TF2 & TF3 & TF4 & TF5 & TF6 & TF7).
unfold af_xdv. change (Z.to_nat 2) with 2%nat.
split; [rewrite TF3; cbn [YO07.s_out]; rewrite concat_app; cbn [concat]; rewrite app_nil_r; exact XS|].
split; [unfold af_xhdr; cbn [set_frames rw_cur rw_attr cg_attr cg_ihead cg_pal cg_ngp YO07.s_rcur YO07.s_ihead]; split; [exact Hrc | split; [exact Hra | split; [exact Hih | exact XP]]]|].
split; [exact TF2|]. split; [exact TF4|].
split; [intros k Hk HP; destruct k as [|[|[|k]]]; cbn [set_frames cg_frames nth qslot YO07.s_q0 YO07.s_q1 YO07.s_q2 wgk oframe_relbA];
[exact XR1 | exact XR2 | exfalso; exact (HP eq_refl) | exfalso; clear - Hk; lia]|].
split; [exact TF7|].
split; [rewrite TF6; unfold af_fb2, af_fb3; cbn [gcfg_of YO07.g_attr]; destruct (YO07.flag fattr 2), (YO07.flag (cg_attr s) 8); reflexivity|].
split; [exact TF1|]. split; [exact TF5|]. split; [exact XGI|]. split; [exact XGIL|]. split; [exact XGL|].
unfold af_xout. rewrite TF3. cbn [YO07.s_out]. rewrite concat_app. cbn [concat]. rewrite app_nil_r, length_app. clear - Hlb. lia.
Qed.
Lemma af_xq_retc : forall S Sc (m : word -> option byte) md s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL gs code ih v rM rN,
af_xq K m md s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL (concat (YO07.s_out gs)) ->
rc_int v = code -> code <> YO07.C_OK -> code <> YO07.C_PENDING -> 0 <= N ->
af_xmtr MT XN S Sc N rM rN -> 0 <= rM -> 0 <= rN ->
af_xretc K MT XN S Sc m md (set_frames s2 [None; Some f1'; Some f2]) N GPAL gs (YO07.mkS None (Some F1) (Some F2) ih code code (YO07.s_out gs)) v.
Proof.
intros S Sc m md s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL gs code ih v rM rN (XS & _) Hv Hc0 Hc6 HN XM HrM HrN.
unfold af_xretc. cbn [YO07.s_cur YO07.s_out].
split; [exact Hv|].
split; [unfold cgif_occ; cbn [set_frames cg_frames nth YO07.s_q0 YO07.s_q1 YO07.s_q2]; repeat split; intros HH; first [reflexivity | discriminate HH]|].
split; [exact XS|].
split; [intros [HL | HL]; cbn [YO07.s_cur] in HL; [exfalso; exact (Hc0 HL) | exfalso; exact (Hc6 HL)]|].
split; [unfold af_xout; cbn [YO07.s_out]; unfold FRAME_OUT; clear - HN; lia|].
exact (af_xmtr_weaken MT XN S Sc N rM rN 0 0 XM HrM HrN).
Qed.
Lemma af_perm_file : forall (A : list (Z * Z)) img N fattr lpa nlp r1 r2,
Permutation (A ++ af_cblocks img N fattr lpa nlp (r1 ++ (pf, FILE_BLOCK) :: r2)) (A ++ (pf, FILE_BLOCK) :: af_cblocks img N fattr lpa nlp (r1 ++ r2)).
Proof.
intros A img N fattr lpa nlp r1 r2. apply Permutation_app_head. unfold af_cblocks.
set (L := if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]).
change ((img, N) :: L ++ r1 ++ (pf, FILE_BLOCK) :: r2) with (((img, N) :: L) ++ r1 ++ (pf, FILE_BLOCK) :: r2).
change ((pf, FILE_BLOCK) :: (img, N) :: L ++ r1 ++ r2) with ((pf, FILE_BLOCK) :: ((img, N) :: L) ++ r1 ++ r2).
rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma af_fp1_sep : forall ly S W mem md g s1 N img fattr lpa nlp rest f1 p n k,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) ->
In (pf, FILE_BLOCK) rest -> In (Some f1) (cg_frames s1) ->
In (p, n) (af_xvblocks s1 N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) -> 0 <= k < req_size n ->
~ inFP ((fr_ptr f1 + 20, fr_ptr f1 + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) (p + k).
Proof.
intros ly S W mem md g s1 N img fattr lpa nlp rest f1 p n k HAR HP Hpf Hf1 Hin Hk.
set (CB1 := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) in *.
assert (HP' : Permutation (ablocks B ly S) ((af_wblocks g s1 ++ rest) ++ (af_xvblocks s1 N ++ CB1))).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_tail; apply cgif_blocks_wv|].
unfold af_cblocks. change ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) with (CB1 ++ rest).
rewrite <- !app_assoc. apply Permutation_app_head. rewrite (app_assoc (af_xvblocks s1 N) CB1 rest). apply Permutation_app_comm. }
assert (Hlive : In (p, n) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; right; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hlive) as (_ & Hp4096 & _).
assert (SEP : forall b m, In (b, m) (af_wblocks g s1 ++ rest) -> ~ (b <= p + k < b + req_size m)).
{ intros b m Hb Hc. pose proof (asep_app B LAWS ly S W mem md _ _ (b, m) (p, n) HAR HP' Hb Hin) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia. }
intros (r & Hr & Hrg). cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hrg.
- apply (SEP (fr_ptr f1) FRAME_SIZE); [apply in_app_iff; left; exact (af_wblocks_frame g s1 f1 Hf1) | change (req_size FRAME_SIZE) with 40; lia].
- apply (SEP (cg_raw s1) RAW_SIZE); [apply in_app_iff; left; right; left; reflexivity | change (req_size RAW_SIZE) with 48; lia].
- unfold asink_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrg.
+ apply (SEP pf FILE_BLOCK); [apply in_app_iff; right; exact Hpf | change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Hrg; lia].
+ unfold sink_token in Hrg. cbn [fst snd] in Hrg. lia.
Qed.
Lemma xcgif_vals_set_frames : forall pth hwv pfv s fr,
xcgif_vals pth hwv pfv (set_frames s fr) = frame_ptr (nth 0 fr None) :: frame_ptr (nth 1 fr None) :: frame_ptr (nth 2 fr None) :: skipn 3 (xcgif_vals pth hwv pfv s).
Proof. intros. reflexivity. Qed.
Lemma af_xvcb_in : forall g s1 N img fattr lpa nlp rest x,
In x (af_xvblocks s1 N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) ->
In x (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest).
Proof.
intros g s1 N img fattr lpa nlp rest x Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx | Hx].
- left. eapply Permutation_in; [apply Permutation_sym; apply (cgif_blocks_wv g s1 N)|]. apply in_app_iff. right. exact Hx.
- right. unfold af_cblocks. change ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) with (((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) ++ rest).
apply in_app_iff. left. exact Hx.
Qed.
Lemma af_xq_flush : forall STK1 sp1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 g s1 N o0 f1 f2 F1 F2 gen' rwcur' img lpa fattr nlp rest GPAL IMG LPAL gs Sg',
ajournal SEGS B STK1 sp1 ((fr_ptr f1 + 20, fr_ptr f1 + 24) :: (cg_raw s1 + 40, cg_raw s1 + 44) :: asink_fp pf) lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 ->
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) ->
Permutation (ablocks B ly2 S2) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) ->
In (pf, FILE_BLOCK) rest -> cg_frames s1 = [o0; Some f1; Some f2] ->
YO07.s_q1 gs = Some F1 -> YO07.s_q2 gs = Some F2 -> cgif_live gs ->
af_xrel K (mrestrict (w_H W) memT) mdc s1 N img lpa fattr nlp GPAL IMG LPAL gs ->
asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf Sg' ->
af_xq K (mrestrict (w_H W2) mem2) md2 (flush_upd s1 1 gen' rwcur') N (set_fr_gen f1 gen') f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg'.
Proof.
intros STK1 sp1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 g s1 N o0 f1 f2 F1 F2 gen' rwcur' img lpa fattr nlp rest GPAL IMG LPAL gs Sg'
HJ HP1 HP2 Hpf Hfr Hq1 Hq2 XLV XREL XS'.
set (L := af_xvblocks s1 N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])).
assert (Hf1 : In (Some f1) (cg_frames s1)) by (rewrite Hfr; right; left; reflexivity).
assert (Hf2 : In (Some f2) (cg_frames s1)) by (rewrite Hfr; right; right; left; reflexivity).
assert (KL : forall a n k, In (a, n) L -> 0 <= k < n -> mbyte SEGS (mrestrict (w_H W2) mem2) (a + k) = mbyte SEGS (mrestrict (w_H W) memT) (a + k)).
{ apply (af_subj_kept STK1 sp1 _ lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 L HJ).
- intros x Hx. pose proof (af_xvcb_in g s1 N img fattr lpa nlp rest x Hx) as Hl.
split; (eapply Permutation_in; [apply Permutation_sym; eassumption | exact Hl]).
- intros p n k Hin Hk. exact (af_fp1_sep ly2 S2 W2 mem2 md2 g s1 N img fattr lpa nlp rest f1 p n k (proj1 HJ) HP2 Hpf Hf1 Hin Hk). }
assert (HfL : forall f, In (Some f) (cg_frames s1) -> forall b, In b (af_xfvb N (Some f)) -> In b L).
{ intros f Hf b Hb. unfold L. apply in_app_iff. left. rewrite af_xvblocks_eq. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hf | exact Hb]. }
apply (af_xq_keptL (mrestrict (w_H W) memT) (mrestrict (w_H W2) mem2) mdc md2 _ N _ f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL (concat (YO07.s_out gs)) Sg' L KL).
- unfold L. apply in_app_iff. right. left. reflexivity.
- intros Hz. unfold L. apply in_app_iff. right. right. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
- cbn [flush_upd cg_attr cg_pal cg_ngp]. intros Hz. unfold L. apply in_app_iff. left. rewrite af_xvblocks_eq. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
- exact (HfL f1 Hf1).
- exact (HfL f2 Hf2).
- exact XS'.
- exact (af_xq_intro (mrestrict (w_H W) memT) mdc s1 N o0 f1 f2 F1 F2 gen' rwcur' img lpa fattr nlp GPAL IMG LPAL gs Hfr Hq1 Hq2 XLV XREL).
Qed.
Lemma af_xq_unz : forall H (m m' : word -> option byte) md md' sx s2 N f1' f2 F1 F2 img lpa fattr nlp rest GPAL IMG LPAL Sg (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks sx N ++ af_cblocks img N fattr lpa nlp rest) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) rest ->
cg_attr sx = cg_attr s2 -> cg_pal sx = cg_pal s2 -> cg_ngp sx = cg_ngp s2 -> In (Some f1') (cg_frames sx) -> In (Some f2) (cg_frames sx) ->
m_fs md' = m_fs md -> m_fds md' = m_fds md ->
af_xq K (mrestrict H m) md s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg -> af_xq K (mrestrict H m') md' s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg.
Proof.
intros H m m' md md' sx s2 N f1' f2 F1 F2 img lpa fattr nlp rest GPAL IMG LPAL Sg Zs UN XZb XZi Hpf Eat Epal Engp Hf1 Hf2 Efs Efd XQ.
pose proof (af_unz_kept H m m' _ Zs UN XZb) as KL.
assert (HfL : forall f, In (Some f) (cg_frames sx) -> forall b, In b (af_xfvb N (Some f)) -> In b (af_xvblocks sx N ++ af_cblocks img N fattr lpa nlp rest)).
{ intros f Hf b Hb. apply in_app_iff. left. rewrite af_xvblocks_eq. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hf | exact Hb]. }
apply (af_xq_keptL (mrestrict H m) (mrestrict H m') md md' s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg Sg _ KL); [| | | exact (HfL f1' Hf1) | exact (HfL f2 Hf2) | | exact XQ].
- apply in_app_iff. right. left. reflexivity.
- intros Hz. apply in_app_iff. right. right. apply in_app_iff. left. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
- intros Hz. apply in_app_iff. left. rewrite af_xvblocks_eq. apply in_app_iff. left. unfold pal_blocks. rewrite Eat, Hz, Epal, Engp. left. reflexivity.
- destruct XQ as (XS & _). apply (asink_at_kept_mm SEGS K (mrestrict H m) (mrestrict H m') md md' pf _); [| exact Efs | exact Efd | exact XS].
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS).
+ replace a with (pf + (a - pf)) by lia.
destruct (XZb pf FILE_BLOCK (a - pf) ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hpf) ltac:(change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Ha; lia)) as [Hr Hn].
exact (UN _ Hr Hn).
+ destruct (XZi a (proj1 (ail_env _ _ _ AIL a Ha))) as [Hr Hn]. exact (UN _ Hr Hn).
Qed.
Lemma af_xq_subj : forall STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 (L : list (Z * Z)) s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 -> ~ YI16.sink_open_fp FP1 ->
(forall x, In x L -> In x (ablocks B lyc Sc) /\ In x (ablocks B ly2 S2)) ->
(forall p n k, In (p, n) L -> 0 <= k < req_size n -> ~ inFP FP1 (p + k)) ->
In (pf, FILE_BLOCK) L -> In (img, N) L -> (Z.land fattr 1 <> 0 -> In (lpa, 3 * nlp) L) ->
(Z.land (cg_attr s2) 4 = 0 -> In (cg_pal s2, 3 * cg_ngp s2) L) ->
(forall b, In b (af_xfvb N (Some f1')) -> In b L) -> (forall b, In b (af_xfvb N (Some f2)) -> In b L) ->
af_xq K (mrestrict (w_H W) memT) mdc s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg ->
af_xq K (mrestrict (w_H W2) mem2) md2 s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg.
Proof.
intros STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 L s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg HJ Hcl HL HnF Hpf Hi Hl Hp Hf1 Hf2 XQ.
pose proof (af_subj_kept STK1 sp1 FP1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 L HJ HL HnF) as KL.
apply (af_xq_keptL (mrestrict (w_H W) memT) (mrestrict (w_H W2) mem2) mdc md2 s2 N f1' f2 F1 F2 img lpa fattr nlp GPAL IMG LPAL Sg Sg L KL Hi Hl Hp Hf1 Hf2); [| exact XQ].
destruct XQ as (XS & _). destruct (HL _ Hpf) as [Hl1 Hl2].
eapply (asink_at_kept SEGS B K AIL); [exact HJ | exact Hcl | exact Hl1 | exact Hl2 | | exact XS].
intros j Hj. apply (HnF pf FILE_BLOCK j Hpf). change (req_size FILE_BLOCK) with 1264. unfold FILE_BLOCK in Hj. lia.
Qed.
Lemma af_lk_in : forall g s2 N f1' f2 img fattr lpa nlp rest, In (pf, FILE_BLOCK) rest ->
let LK := (g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest in
In (pf, FILE_BLOCK) LK /\ In (img, N) LK /\ (Z.land fattr 1 <> 0 -> In (lpa, 3 * nlp) LK) /\ (Z.land (cg_attr s2) 4 = 0 -> In (cg_pal s2, 3 * cg_ngp s2) LK) /\
(forall b, In b (af_xfvb N (Some f1')) -> In b LK) /\ (forall b, In b (af_xfvb N (Some f2)) -> In b LK).
Proof.
intros g s2 N f1' f2 img fattr lpa nlp rest Hpf LK. subst LK.
assert (HC : forall x, In x (af_cblocks img N fattr lpa nlp rest) -> In x ((g, CGIF_SIZE) :: (cg_raw s2, RAW_SIZE) :: pal_blocks s2 ++ frame_blocks N f1' ++ frame_blocks N f2 ++ af_cblocks img N fattr lpa nlp rest))
by (intros x Hx; right; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Hx).
split; [apply HC; unfold af_cblocks; right; apply in_app_iff; right; exact Hpf|].
split; [apply HC; left; reflexivity|].
split; [intros Hz; apply HC; unfold af_cblocks; right; apply in_app_iff; left; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]|].
split; [intros Hz; right; right; apply in_app_iff; left; unfold pal_blocks; rewrite Hz; left; reflexivity|].
split; intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; [left | right; apply in_app_iff; left]; right; exact Hb.
Qed.
End i.
End e.
End d.
