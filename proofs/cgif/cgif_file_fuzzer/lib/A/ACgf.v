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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk.
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
Ltac mresX Hnz Ebl HK Hres :=
lazymatch type of HK with acall_kept ?sg ?Bq ?lyc ?Sc ?Wc ?memT ?W2 ?mem2 ?slo ?shi (fun a => ?res <= a < _) =>
lazymatch type of Ebl with ablocks _ ?ly ?S = _ =>
pose proof (@or_intror (res = 0 /\ ablocks Bq ly S = ablocks Bq lyc Sc /\ acall_kept sg Bq lyc Sc Wc memT W2 mem2 slo shi (fun _ => False)) _
(conj Hnz (conj Ebl HK))) as Hres end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
#[local] Abbreviation NF s GPAL fattr fgen delay tidx nlp LPAL IMG := (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG).
Definition af_xdv (m : word -> option byte) (md : Model) (s s1 : cgif_st) (N i : Z) (pimg ppal : Z) (fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gs gs1 gsF : YO07.gif_st) : Prop :=
asink_at SEGS K m md pf (concat (YO07.s_out gsF)) /\
af_xhdr SEGS m s1 GPAL gs1 /\ YO07.s_rcur gsF = YO07.s_rcur gs1 /\ YO07.s_ihead gsF = i /\
af_xslots SEGS m s1 N gs1 (fun k => k <> Z.to_nat i) /\
(forall k, (k < 3)%nat -> k <> Z.to_nat i -> k <> (Z.to_nat i - 1)%nat -> qslot gsF k = qslot gs1 k) /\
qslot gsF (Z.to_nat i - 1)%nat = af_fb2 fattr (af_fb3 (cg_attr s) (qslot gs1 (Z.to_nat i - 1)%nat)) /\
YO07.s_cur gsF = YO07.C_OK /\ qslot gsF (Z.to_nat i) = Some (NF s GPAL fattr fgen delay tidx nlp LPAL IMG) /\
garr8 SEGS m pimg IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 SEGS m ppal LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) /\
af_xout gs gsF N.
Definition af_xd (S Sc : astate) (m : word -> option byte) (md : Model) (s s1 : cgif_st) (N i : Z) (pimg ppal : Z) (fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gs gs1 gsF : YO07.gif_st) (needM needN : Z) : Prop :=
af_xdv m md s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF /\ af_xmtr MT XN S Sc N needM needN.
Lemma af_xd_e1 : forall S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
af_xd S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF 0 0 ->
af_xe1 K MT XN S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF.
Proof.
intros S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13) & XM).
unfold af_xe1. repeat (split; [assumption|]). exact XM.
Qed.
Lemma af_xmtr_ok : forall S Sc N c nM nN, ameter_laws MT -> mo_ok MT S (xm_addframe XN N) -> 0 <= c ->
af_xmtr MT XN S Sc N nM nN -> c <= nM -> mo_ok MT Sc c.
Proof.
intros S Sc N c nM nN MLAW HOK Hc (acc & Ha & HLE & HM & HN) HcM.
exact (mok_station MT S Sc (xm_addframe XN N) acc c MLAW HOK HLE Hc ltac:(lia)).
Qed.
Lemma af_xmtr_step : forall S Sc S2 N c nM nN rM rN, ameter_laws MT -> 0 <= c ->
af_xmtr MT XN S Sc N nM nN -> mo_le MT Sc S2 c -> rM + c <= nM -> rN + c <= nN -> af_xmtr MT XN S S2 N rM rN.
Proof.
intros S Sc S2 N c nM nN rM rN MLAW Hc (acc & Ha & HLE & HM & HN) H2 H3 H4. exists (acc + c).
split; [lia|]. split; [exact (mle_station MT S Sc S2 acc c MLAW HLE H2)|]. split; lia.
Qed.
Lemma af_xmtr_weaken : forall S Sc N rM rN rM' rN', af_xmtr MT XN S Sc N rM rN -> rM' <= rM -> rN' <= rN -> af_xmtr MT XN S Sc N rM' rN'.
Proof. intros S Sc N rM rN rM' rN' (acc & Ha & HLE & HM & HN) H1 H2. exists acc. repeat split; try assumption; lia. Qed.
Definition af_need3 (nlp : Z) : Z := mo_malloc MT (3 * nlp).
Definition af_need2 (N nlp : Z) : Z := mo_malloc MT N + af_need3 nlp.
Definition af_need1 (N nlp : Z) : Z := mo_malloc MT 40 + af_need2 N nlp.
Definition AF_D_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (gs1 : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_FLUSH + 4 ->
blocks_bytes Sc <= blocks_bytes S ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
af_xd S Sc (rdW Wc memc) mdc s s1 N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (af_need1 N nlp) (af_need1 N nlp) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_D)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_D2_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (gs1 : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 [(nw, FRAME_SIZE)] -> k <= EV_FLUSH + 5 ->
blocks_bytes Sc <= blocks_bytes S + FRAME_SIZE ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 N ->
getr regs1 21 = w64 (cfp + 8) -> getr regs1 25 = w64 (SB + (cfp + 8) / 8) ->
getr regs1 26 = w64 (g + 48) -> getr regs1 19 = w64 (SB + (g + 48) / 8) ->
getr regs1 27 = w64 (g + 50) -> getr regs1 20 = w64 (SB + (g + 50) / 8) ->
af_locsD2 (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) nw ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
In (nw, FRAME_SIZE) (ablocks B lyc Sc) ->
af_newcfg (mrestrict (w_H Wc) memc) nw lpal fattr fgen delay nlp tidx ->
af_xd S Sc (rdW Wc memc) mdc s s1 N i img lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (af_need2 N nlp) (af_need2 N nlp) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_D2)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_D3_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw nimg : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (gs1 : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 [(nw, FRAME_SIZE); (nimg, N)] -> k <= EV_FLUSH + 6 ->
blocks_bytes Sc <= blocks_bytes S + FRAME_SIZE + N ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
getr regs1 19 = w64 (cfp + 26) -> getr regs1 10 = w64 nlp ->
af_locsD3 (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) nw ->
Z.land fattr 1 <> 0 ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
In (nw, FRAME_SIZE) (ablocks B lyc Sc) -> In (nimg, N) (ablocks B lyc Sc) ->
af_newcfg (mrestrict (w_H Wc) memc) nw lpal fattr fgen delay nlp tidx ->
val_mem SEGS (mrestrict (w_H Wc) memc) (nw + 8) 8 nimg ->
af_xd S Sc (rdW Wc memc) mdc s s1 N i nimg lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (af_need3 nlp) (af_need3 nlp) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_D3)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
End h.
Section l.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Lemma af_xdv_unz : forall H (m m' : word -> option byte) md md' s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Xv cb (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ Xv ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> In (pimg, N) (Xv ++ cb) -> (Z.land fattr 1 <> 0 -> In (ppal, 3 * nlp) (Xv ++ cb)) ->
m_fs md' = m_fs md -> m_fds md' = m_fds md -> length (cg_frames s1) = 3%nat ->
af_xdv K (mrestrict H m) md s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xdv K (mrestrict H m') md' s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF.
Proof.
intros H m m' md md' s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Xv cb Zs UN XZb XZi Hpf Hni Hnp Efs Efd Hlen
(XS & XH & X1 & X2 & XSL & X3 & X4 & X5 & X6 & XGI & XGIL & XGL & XO).
assert (KV : forall a n k, In (a, n) (af_xvblocks s1 N) -> 0 <= k < n -> mbyte SEGS (mrestrict H m') (a + k) = mbyte SEGS (mrestrict H m) (a + k)).
{ intros a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k ltac:(apply in_app_iff; left; exact Hin) ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn). }
assert (KX : forall a n k, In (a, n) (Xv ++ cb) -> 0 <= k < n -> mbyte SEGS (mrestrict H m') (a + k) = mbyte SEGS (mrestrict H m) (a + k)).
{ intros a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k ltac:(apply in_app_iff; right; exact Hin) ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn). }
split; [| split; [| split; [exact X1 | split; [exact X2 | split; [| split; [exact X3 | split; [exact X4 | split; [exact X5 | split; [exact X6 | split; [| split; [exact XGIL | split; [| exact XO]]]]]]]]]]]].
- apply (asink_at_kept_mm SEGS K (mrestrict H m) (mrestrict H m') md md' pf _); [| exact Efs | exact Efd | exact XS].
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS).
+ replace a with (pf + (a - pf)) by lia.
destruct (XZb pf FILE_BLOCK (a - pf) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hpf) ltac:(change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Ha; lia)) as [Hr Hn].
exact (UN _ Hr Hn).
+ destruct (XZi a (proj1 (ail_env _ _ _ AIL a Ha))) as [Hr Hn]. exact (UN _ Hr Hn).
- apply (af_xhdr_kept SEGS (mrestrict H m)); [| exact XH].
intros Hz k Hk. apply (KV (cg_pal s1) (3 * cg_ngp s1) k); [| exact Hk]. rewrite af_xvblocks_eq. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
- apply (af_xslots_kept SEGS (mrestrict H m)); [| exact XSL].
intros k f Hk _ Hn a n j Hin Hj. apply (KV a n j); [| exact Hj]. rewrite af_xvblocks_eq. apply in_app_iff. right.
apply in_flat_map. exists (Some f). split; [rewrite <- Hn; apply nth_In; rewrite Hlen; exact Hk | exact Hin].
- eapply garr8_frame; [exact XGI|]. intros a Ha. replace a with (pimg + (a - pimg)) by lia. apply (KX pimg N); [exact Hni | lia].
- intros Hz. destruct (XGL Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (ppal + (a - ppal)) by lia. apply (KX ppal (3 * nlp)); [exact (Hnp Hz) | lia].
Qed.
Lemma af_xdv_subj : forall STK1 sp1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 g s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF X cb,
ajournal SEGS B STK1 sp1 [] lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 ->
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ X ++ cb) -> (forall x, In x (ablocks B lyc Sc) -> In x (ablocks B ly2 S2)) ->
In (pf, FILE_BLOCK) cb -> In (pimg, N) (X ++ cb) -> (Z.land fattr 1 <> 0 -> In (ppal, 3 * nlp) (X ++ cb)) -> length (cg_frames s1) = 3%nat ->
af_xdv K (mrestrict (w_H W) memT) mdc s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xdv K (mrestrict (w_H W2) mem2) md2 s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF.
Proof.
intros STK1 sp1 lyc Sc W memT mdc nf ly2 S2 W2 mem2 md2 k1 g s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF X cb HJ HP Hsub Hpf Hni Hnp Hlen
(XS & XH & X1 & X2 & XSL & X3 & X4 & X5 & X6 & XGI & XGIL & XGL & XO).
assert (LIVE : forall x, In x (cgif_blocks g s1 N ++ X ++ cb) -> In x (ablocks B lyc Sc)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hx]).
assert (KB : forall a n, In (a, n) (cgif_blocks g s1 N ++ X ++ cb) -> forall k, 0 <= k < n -> mbyte SEGS (mrestrict (w_H W2) mem2) (a + k) = mbyte SEGS (mrestrict (w_H W) memT) (a + k)).
{ intros a n Hin k Hk. apply (mbyte_of_aview SEGS). pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 a n k (LIVE _ Hin) (Hsub _ (LIVE _ Hin))); [pose proof (req_size_pos n); lia | intros HF; exact (inFP_nil _ HF)]. }
assert (KV : forall a n k, In (a, n) (af_xvblocks s1 N) -> 0 <= k < n -> mbyte SEGS (mrestrict (w_H W2) mem2) (a + k) = mbyte SEGS (mrestrict (w_H W) memT) (a + k)).
{ intros a n k Hin Hk. apply (KB a n); [| exact Hk]. apply in_app_iff. left.
eapply Permutation_in; [apply Permutation_sym; apply (cgif_blocks_wv g s1 N)|]. apply in_app_iff. right. exact Hin. }
split; [| split; [| split; [exact X1 | split; [exact X2 | split; [| split; [exact X3 | split; [exact X4 | split; [exact X5 | split; [exact X6 | split; [| split; [exact XGIL | split; [| exact XO]]]]]]]]]]]].
- assert (Hpfl : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (apply LIVE; apply in_app_iff; right; apply in_app_iff; right; exact Hpf).
eapply (asink_at_kept SEGS B K AIL); [exact HJ | exact sink_closed_nil | exact Hpfl | exact (Hsub _ Hpfl) | intros j Hj HF; exact (inFP_nil _ HF) | exact XS].
- apply (af_xhdr_kept SEGS (mrestrict (w_H W) memT)); [| exact XH].
intros Hz k Hk. apply (KV (cg_pal s1) (3 * cg_ngp s1) k); [| exact Hk]. rewrite af_xvblocks_eq. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
- apply (af_xslots_kept SEGS (mrestrict (w_H W) memT)); [| exact XSL].
intros k f Hk _ Hn a n j Hin Hj. apply (KV a n j); [| exact Hj]. rewrite af_xvblocks_eq. apply in_app_iff. right.
apply in_flat_map. exists (Some f). split; [rewrite <- Hn; apply nth_In; rewrite Hlen; exact Hk | exact Hin].
- eapply garr8_frame; [exact XGI|]. intros a Ha. replace a with (pimg + (a - pimg)) by lia. apply (KB pimg N); [apply in_app_iff; right; exact Hni | lia].
- intros Hz. destruct (XGL Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (ppal + (a - ppal)) by lia. apply (KB ppal (3 * nlp)); [apply in_app_iff; right; exact (Hnp Hz) | lia].
Qed.
Lemma af_xdv_set_img : forall m md s s1 N i pimg ppal d fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
af_xdv K m md s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF -> garr8 SEGS m d IMG ->
af_xdv K m md s s1 N i d ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF.
Proof.
intros m md s s1 N i pimg ppal d fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (XS & XH & X1 & X2 & XSL & X3 & X4 & X5 & X6 & XGI & XGIL & XGL & XO) HG.
unfold af_xdv. repeat (split; [assumption|]). assumption.
Qed.
Lemma af_xdv_set_pal : forall m md s s1 N i pimg ppal d fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
af_xdv K m md s s1 N i pimg ppal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF -> (Z.land fattr 1 <> 0 -> garr8 SEGS m d LPAL) ->
af_xdv K m md s s1 N i pimg d fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF.
Proof.
intros m md s s1 N i pimg ppal d fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (XS & XH & X1 & X2 & XSL & X3 & X4 & X5 & X6 & XGI & XGIL & XGL & XO) HG.
unfold af_xdv. repeat (split; [assumption|]). split; [| exact XO]. intros Hz. split; [exact (HG Hz) | exact (proj2 (XGL Hz))].
Qed.
End l.
End e.
End b.
