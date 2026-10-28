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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs.
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
#[local] Abbreviation NF s GPAL fattr fgen delay tidx nlp LPAL IMG := (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG).
Definition af_xcore (m : word -> option byte) (md : Model) (s1 : cgif_st) (N i : Z) (fn : frame_st) (fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gsH gsS gsF : YO07.gif_st) (disp tcur : Z) : Prop :=
asink_at SEGS K m md pf (concat (YO07.s_out gsF)) /\
af_xhdr SEGS m s1 GPAL gsH /\ af_xslots SEGS m s1 N gsS (fun k => k <> Z.to_nat i) /\
af_xnewf SEGS m N fn fattr fgen delay nlp tidx IMG LPAL disp tcur.
Definition af_xfin (S Sc : astate) (m : word -> option byte) (md : Model) (s s1 : cgif_st) (N i : Z) (fn : frame_st) (fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (tcur : Z) : Prop :=
af_xcore m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsF gsF gsF (YO07.f_disp (NF s GPAL fattr fgen delay tidx nlp LPAL IMG)) tcur /\
YO07.s_cur gsF = YO07.C_OK /\ qslot gsF (Z.to_nat i) = Some (NF s GPAL fattr fgen delay tidx nlp LPAL IMG) /\
af_xout gs gsF N /\ af_xmtr MT XN S Sc N 0 0.
Lemma af_xfin_ret : forall S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> nth (Z.to_nat i) (cg_frames s1) None = Some fn ->
af_xfin S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (YO07.f_trans (NF s GPAL fattr fgen delay tidx nlp LPAL IMG)) ->
af_xret K MT XN S Sc m md (cl_set_cur s1 0) N GPAL gs gsF.
Proof.
intros S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF Hi Hlen Hfn ((XS & XH & XSL & XNF) & XC & XI & XO & XM).
split; [| split; [exact XO | exact XM]].
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (XSa : af_xslots SEGS m s1 N gsF (fun _ => True)).
{ eapply (af_xslots_fill SEGS m s1 N gsF (Z.to_nat i) fn _ (fun _ => True)); [eapply af_xslots_mono; [| exact XSL]; cbv beta; intros k [Hk _]; exact Hk | exact Hfn | exact XI |].
intros _. apply af_xnewf_rel. exact XNF. }
apply (proj2 (cgif_relA_split SEGS K m md (cl_set_cur s1 0) pf N GPAL gsF)). split; [| split].
- split; [cbn [cl_set_cur cg_cur]; rewrite XC; reflexivity | apply (proj2 (cgif_occ_set_cur s1 0 gsF)); exact (af_xslots_occ SEGS m s1 N gsF XSa)].
- exact XS.
- intros _. apply (proj2 (af_xlive_set_cur SEGS m s1 N GPAL gsF 0)). apply (proj2 (af_xlive_iff SEGS m s1 N GPAL gsF)). split; [exact XH | exact XSa].
Qed.
Definition af_fb2 (fattr : Z) (o : option YO07.frame) : option YO07.frame :=
if YO07.flag fattr 2 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 2)) 8) o else o.
Definition af_fb3 (gattr : Z) (o : option YO07.frame) : option YO07.frame :=
if YO07.flag gattr 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) o else o.
Definition af_xe2 (S Sc : astate) (m : word -> option byte) (md : Model) (s s1 : cgif_st) (N i : Z) (fn : frame_st) (fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gs gs4 gsF : YO07.gif_st) : Prop :=
af_xcore m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsF gs4 gsF (YO07.f_disp (NF s GPAL fattr fgen delay tidx nlp LPAL IMG)) 0 /\
(forall k, (k < 3)%nat -> k <> Z.to_nat i -> k <> (Z.to_nat i - 1)%nat -> qslot gsF k = qslot gs4 k) /\
qslot gsF (Z.to_nat i - 1)%nat = af_fb2 fattr (qslot gs4 (Z.to_nat i - 1)%nat) /\
YO07.s_cur gsF = YO07.C_OK /\ qslot gsF (Z.to_nat i) = Some (NF s GPAL fattr fgen delay tidx nlp LPAL IMG) /\
af_xout gs gsF N /\ af_xmtr MT XN S Sc N 0 0.
Definition af_xe1 (S Sc : astate) (m : word -> option byte) (md : Model) (s s1 : cgif_st) (N i : Z) (nimg npal : Z) (fattr fgen delay nlp tidx : Z)
(GPAL IMG LPAL : list Z) (gs gs1 gsF : YO07.gif_st) : Prop :=
asink_at SEGS K m md pf (concat (YO07.s_out gsF)) /\
af_xhdr SEGS m s1 GPAL gs1 /\ YO07.s_rcur gsF = YO07.s_rcur gs1 /\ YO07.s_ihead gsF = i /\
af_xslots SEGS m s1 N gs1 (fun k => k <> Z.to_nat i) /\
(forall k, (k < 3)%nat -> k <> Z.to_nat i -> k <> (Z.to_nat i - 1)%nat -> qslot gsF k = qslot gs1 k) /\
qslot gsF (Z.to_nat i - 1)%nat = af_fb2 fattr (af_fb3 (cg_attr s) (qslot gs1 (Z.to_nat i - 1)%nat)) /\
YO07.s_cur gsF = YO07.C_OK /\ qslot gsF (Z.to_nat i) = Some (NF s GPAL fattr fgen delay tidx nlp LPAL IMG) /\
garr8 SEGS m nimg IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 SEGS m npal LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) /\
af_xout gs gsF N /\ af_xmtr MT XN S Sc N 0 0.
Definition AF_RET0_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at0 B regs regs1 ->
af_xret K MT XN S Sc (rdW Wc memc) mdc s1 N GPAL gs gsF ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_RET)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_E3_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at0 B regs regs1 -> getr regs1 8 = w64 (g + 88) -> getr regs1 22 = w64 SB -> af_s1_at regs1 g -> getr regs1 16 = w64 cfp ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw ->
af_xfin S Sc (rdW Wc memc) mdc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (if YO07.flag fattr 2 then tidx else 0) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E3)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_E2_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (gs4 : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
getr regs1 16 = w64 cfp -> getr regs1 17 = w64 (cfp + 16) ->
getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw -> cg_ihead s1 = i ->
af_xe2 S Sc (rdW Wc memc) mdc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E2)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_E_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw nimg npal : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (gs1 : YO07.gif_st),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 (af_newblocks N fattr nlp nw nimg npal) -> k <= EV_FLUSH + 8 ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
In (nw, FRAME_SIZE) (ablocks B lyc Sc) ->
af_newcfg (mrestrict (w_H Wc) memc) nw (if Z.land fattr 1 =? 0 then lpal else npal) fattr fgen delay nlp tidx ->
val_mem SEGS (mrestrict (w_H Wc) memc) (nw + 8) 8 nimg ->
af_xe1 S Sc (rdW Wc memc) mdc s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E)) memc (seg_rom SEGS)) mdc)
(af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
End e.
Section h.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_xcore_unz : forall H (m m' : word -> option byte) md md' s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur cb (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> m_fs md' = m_fs md -> m_fds md' = m_fds md ->
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> nth (Z.to_nat i) (cg_frames s1) None = Some fn ->
af_xcore K (mrestrict H m) md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur ->
af_xcore K (mrestrict H m') md' s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur.
Proof.
intros H m m' md md' s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur cb Zs UN XZb XZi Hpf Efs Efd Hi Hlen Hfn
(XS & XH & XSL & XNF).
assert (KV : forall a n k, In (a, n) (af_xvblocks s1 N) -> 0 <= k < n -> mbyte SEGS (mrestrict H m') (a + k) = mbyte SEGS (mrestrict H m) (a + k)).
{ intros a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k ltac:(apply in_app_iff; left; exact Hin) ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn). }
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (Hfin : In (Some fn) (cg_frames s1)) by (rewrite <- Hfn; apply nth_In; rewrite Hlen; exact Hi3).
split; [| split; [| split]].
- apply (asink_at_kept_mm SEGS K (mrestrict H m) (mrestrict H m') md md' pf _); [| exact Efs | exact Efd | exact XS].
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS).
+ replace a with (pf + (a - pf)) by lia.
destruct (XZb pf FILE_BLOCK (a - pf) ltac:(apply in_app_iff; right; exact Hpf) ltac:(change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Ha; lia)) as [Hr Hn].
exact (UN _ Hr Hn).
+ destruct (XZi a (proj1 (ail_env _ _ _ AIL a Ha))) as [Hr Hn]. exact (UN _ Hr Hn).
- apply (af_xhdr_kept SEGS (mrestrict H m)); [| exact XH].
intros Hz k Hk. apply (KV (cg_pal s1) (3 * cg_ngp s1) k); [| exact Hk]. rewrite af_xvblocks_eq. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
- apply (af_xslots_kept SEGS (mrestrict H m)); [| exact XSL].
intros k f Hk _ Hn a n j Hin Hj. apply (KV a n j); [| exact Hj]. rewrite af_xvblocks_eq. apply in_app_iff. right.
apply in_flat_map. exists (Some f). split; [rewrite <- Hn; apply nth_In; rewrite Hlen; exact Hk | exact Hin].
- destruct XNF as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hgi & Hgil & Hgl).
apply (af_xnewf_kept SEGS (mrestrict H m)); [| | repeat (split; [assumption|]); assumption].
+ intros j Hj. apply (KV (fr_img fn) N j); [| exact Hj]. rewrite af_xvblocks_eq. apply in_app_iff. right.
apply in_flat_map. exists (Some fn). split; [exact Hfin | left; reflexivity].
+ intros Hz j Hj. apply (KV (fr_lpal fn) (3 * nlp) j); [| exact Hj]. rewrite af_xvblocks_eq. apply in_app_iff. right.
apply in_flat_map. exists (Some fn). split; [exact Hfin|]. cbn [af_xfvb]. right. rewrite A1, A4.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
Qed.
Lemma af_xcore_tidx : forall m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur t',
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat ->
af_xcore K m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur ->
af_xcore K m md (upd_frame s1 (Z.to_nat i) (set_fr_tidx fn t')) N i (set_fr_tidx fn t') fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp t'.
Proof.
intros m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gsH gsS gsF disp tcur t' Hi Hlen (XS & XH & XSL & XNF).
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
split; [exact XS|]. split; [exact (af_xhdr_ext SEGS m s1 _ GPAL gsH gsH eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl XH)|].
split; [apply (af_xslots_upd_skip SEGS m s1 N gsS (Z.to_nat i) _ _ Hi3 Hlen XSL); intros k Hk; exact Hk|].
pose proof XNF as (_ & _ & _ & _ & _ & A6 & _).
exact (af_xnewf_fields SEGS m N fn (set_fr_tidx fn t') fattr fgen delay nlp tidx IMG LPAL _ tcur _ t' XNF eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl A6 eq_refl).
Qed.
Lemma af_xfin_unz : forall H (m m' : word -> option byte) md md' S Sc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur cb (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> m_fs md' = m_fs md -> m_fds md' = m_fds md ->
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> nth (Z.to_nat i) (cg_frames s1) None = Some fn ->
af_xfin K MT XN S Sc (mrestrict H m) md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur ->
af_xfin K MT XN S Sc (mrestrict H m') md' s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur.
Proof.
intros H m m' md md' S Sc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur cb Zs UN XZb XZi Hpf Efs Efd Hi Hlen Hfn (XC & XR).
split; [| exact XR]. exact (af_xcore_unz H m m' md md' s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL _ _ _ _ tcur cb Zs UN XZb XZi Hpf Efs Efd Hi Hlen Hfn XC).
Qed.
Lemma af_xfin_tidx : forall S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur t',
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat ->
af_xfin K MT XN S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur ->
af_xfin K MT XN S Sc m md s (upd_frame s1 (Z.to_nat i) (set_fr_tidx fn t')) N i (set_fr_tidx fn t') fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF t'.
Proof.
intros S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF tcur t' Hi Hlen (XC & XR).
split; [| exact XR]. exact (af_xcore_tidx m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL _ _ _ _ tcur t' Hi Hlen XC).
Qed.
Lemma af_xe2_unz : forall H (m m' : word -> option byte) md md' S Sc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF cb (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> m_fs md' = m_fs md -> m_fds md' = m_fds md ->
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> nth (Z.to_nat i) (cg_frames s1) None = Some fn ->
af_xe2 K MT XN S Sc (mrestrict H m) md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF ->
af_xe2 K MT XN S Sc (mrestrict H m') md' s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF.
Proof.
intros H m m' md md' S Sc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF cb Zs UN XZb XZi Hpf Efs Efd Hi Hlen Hfn (XC & XR).
split; [| exact XR]. exact (af_xcore_unz H m m' md md' s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL _ _ _ _ 0 cb Zs UN XZb XZi Hpf Efs Efd Hi Hlen Hfn XC).
Qed.
Lemma nf_trans_noset : forall G fattr fgen delay tidx nlp LPAL IMG, Z.land fattr 4 = 0 ->
YO07.f_trans (YO07.new_frame G fattr fgen delay tidx nlp LPAL IMG) = (if YO07.flag fattr 2 then tidx else 0).
Proof. intros G fattr fgen delay tidx nlp LPAL IMG H4. cbn [YO07.f_trans YO07.new_frame]. replace (YO07.flag fattr 4) with false by (unfold YO07.flag; rewrite H4; reflexivity). rewrite Bool.orb_false_r. reflexivity. Qed.
Lemma nf_trans_set : forall G fattr fgen delay tidx nlp LPAL IMG, Z.land fattr 4 <> 0 ->
YO07.f_trans (YO07.new_frame G fattr fgen delay tidx nlp LPAL IMG) = tidx.
Proof.
intros G fattr fgen delay tidx nlp LPAL IMG H4. cbn [YO07.f_trans YO07.new_frame].
replace (YO07.flag fattr 4) with true by (unfold YO07.flag; destruct (Z.eqb_spec (Z.land fattr 4) 0); [exfalso; exact (H4 ltac:(assumption)) | reflexivity]).
rewrite Bool.orb_true_r. reflexivity.
Qed.
Lemma land_not64 : forall v c, 0 <= v < 2 ^ 64 -> Z.land v ((Z.lnot c) mod 2 ^ 64) = YO07.clr v c.
Proof.
intros v c Hv. unfold YO07.clr. rewrite <- (Z.land_ones (Z.lnot c) 64) by lia.
rewrite Z.land_assoc, (Z.land_comm v (Z.lnot c)), <- Z.land_assoc, (Z.land_ones v 64) by lia. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma frame_relbA_fb : forall wg m N fp fpm c gen',
frame_relbA SEGS wg m N fp fpm -> 0 <= fr_gen fp < 2 ^ 64 -> gen' = Z.land (fr_gen fp) ((Z.lnot c) mod 2 ^ 64) ->
frame_relbA SEGS wg m N (set_fr_gen_disp fp gen' 8) (YO07.set_disp (YO07.set_gen fpm (YO07.clr (YO07.f_gen fpm) c)) 8).
Proof.
intros wg m N fp fpm c gen' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl) Rg ->. unfold frame_relbA, set_fr_gen_disp, YO07.set_disp, YO07.set_gen.
cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal YO07.f_attr YO07.f_gen YO07.f_delay YO07.f_nlp YO07.f_ctrans YO07.f_disp YO07.f_trans YO07.f_img YO07.f_lpal].
split; [exact A1|]. split; [destruct wg; [rewrite (land_not64 _ c Rg), A2; reflexivity | exact I]|].
split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|]. split; [exact A7|]. split; [exact Hi|]. split; [exact Hil | exact Hl].
Qed.
Lemma af_xe2_fin_noalpha : forall S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF,
Z.land fattr 2 = 0 ->
af_xe2 K MT XN S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF ->
af_xfin K MT XN S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (if YO07.flag fattr 2 then tidx else 0).
Proof.
intros S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF H2 ((XS & XH & XSL & XNF) & X1 & X2 & XR).
assert (Hfl : YO07.flag fattr 2 = false) by (unfold YO07.flag; rewrite H2; reflexivity). rewrite Hfl.
split; [| exact XR]. split; [exact XS|]. split; [exact XH|]. split; [| exact XNF].
apply (af_xslots_qext SEGS m s1 N gs4 gsF); [| exact XSL]. intros k Hk Hki.
destruct (Nat.eq_dec k (Z.to_nat i - 1)) as [-> | Hne]; [rewrite X2; unfold af_fb2; rewrite Hfl; reflexivity | exact (X1 k Hk Hki Hne)].
Qed.
Lemma af_xe2_fin_alpha_none : forall S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> Z.land fattr 2 <> 0 ->
nth (Z.to_nat i - 1) (cg_frames s1) None = None ->
af_xe2 K MT XN S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF ->
af_xfin K MT XN S Sc m md s (upd_frame s1 (Z.to_nat i) (set_fr_tidx fn tidx)) N i (set_fr_tidx fn tidx) fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (if YO07.flag fattr 2 then tidx else 0).
Proof.
intros S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF Hi Hlen H2 Hop (XC & X1 & X2 & XR).
assert (Hfl : YO07.flag fattr 2 = true) by (unfold YO07.flag; destruct (Z.eqb_spec (Z.land fattr 2) 0); [exfalso; exact (H2 ltac:(assumption)) | reflexivity]). rewrite Hfl.
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (Hi1 : (Z.to_nat i - 1 < 3)%nat /\ (Z.to_nat i - 1)%nat <> Z.to_nat i) by (destruct Hi as [-> | ->]; cbn; lia).
pose proof XC as (_ & _ & XSL0 & _).
pose proof (oframe_relbA_occ SEGS _ _ _ _ _ (XSL0 (Z.to_nat i - 1)%nat (proj1 Hi1) (proj2 Hi1))) as Hocc. rewrite Hop in Hocc.
pose proof (proj1 Hocc eq_refl) as Hq4.
pose proof (af_xcore_tidx m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL _ _ _ _ 0 tidx Hi Hlen XC) as (XS & XH & XSL & XNF).
split; [| exact XR]. split; [exact XS|]. split; [exact XH|]. split; [| exact XNF].
apply (af_xslots_qext SEGS m _ N gs4 gsF); [| exact XSL]. intros k Hk Hki.
destruct (Nat.eq_dec k (Z.to_nat i - 1)) as [-> | Hne]; [rewrite X2, Hq4; unfold af_fb2; rewrite Hfl; reflexivity | exact (X1 k Hk Hki Hne)].
Qed.
Lemma af_xe2_fin_alpha_some : forall S Sc m md s s1 N i fn fp fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> Z.land fattr 2 <> 0 ->
nth (Z.to_nat i - 1) (cg_frames s1) None = Some fp -> 0 <= fr_gen fp < 2 ^ 64 ->
af_xe2 K MT XN S Sc m md s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF ->
af_xfin K MT XN S Sc m md s (upd_frame (upd_frame s1 (Z.to_nat i) (set_fr_tidx fn tidx)) (Z.to_nat i - 1) (set_fr_gen_disp fp (Z.land (fr_gen fp) 18446744073709551613) 8))
N i (set_fr_tidx fn tidx) fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (if YO07.flag fattr 2 then tidx else 0).
Proof.
intros S Sc m md s s1 N i fn fp fattr fgen delay nlp tidx GPAL IMG LPAL gs gs4 gsF Hi Hlen H2 Hop Rg (XC & X1 & X2 & XR).
assert (Hfl : YO07.flag fattr 2 = true) by (unfold YO07.flag; destruct (Z.eqb_spec (Z.land fattr 2) 0); [exfalso; exact (H2 ltac:(assumption)) | reflexivity]). rewrite Hfl.
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (Hi1 : (Z.to_nat i - 1 < 3)%nat /\ (Z.to_nat i - 1)%nat <> Z.to_nat i) by (destruct Hi as [-> | ->]; cbn; lia).
pose proof (af_xcore_tidx m md s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL _ _ _ _ 0 tidx Hi Hlen XC) as (XS & XH & XSL & XNF).
set (s1' := upd_frame s1 (Z.to_nat i) (set_fr_tidx fn tidx)) in *.
assert (Hlen' : length (cg_frames s1') = 3%nat) by (subst s1'; unfold upd_frame, set_frames; cbn [cg_frames]; rewrite length_list_set; exact Hlen).
assert (Hop' : nth (Z.to_nat i - 1) (cg_frames s1') None = Some fp).
{ subst s1'. rewrite (nth_upd_frame s1 (Z.to_nat i) _ (Z.to_nat i - 1) Hlen Hi3). destruct (Nat.eqb_spec (Z.to_nat i - 1) (Z.to_nat i)) as [Hq | _]; [exfalso; exact (proj2 Hi1 Hq) | exact Hop]. }
pose proof (XSL (Z.to_nat i - 1)%nat (proj1 Hi1) (proj2 Hi1)) as Hrel. rewrite Hop' in Hrel.
destruct (qslot gs4 (Z.to_nat i - 1)) as [fpm|] eqn:Hq4; [| destruct Hrel]. cbn [oframe_relbA] in Hrel.
split; [| exact XR]. split; [exact XS|].
split; [exact (af_xhdr_ext SEGS m s1' _ GPAL gsF gsF eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl XH)|].
split.
- intros k Hk Hki. rewrite (nth_upd_frame s1' (Z.to_nat i - 1) _ k Hlen' (proj1 Hi1)).
destruct (Nat.eqb_spec k (Z.to_nat i - 1)) as [-> | Hne].
+ rewrite X2. unfold af_fb2. rewrite Hfl. cbn [YO07.omap oframe_relbA].
apply (frame_relbA_fb _ m N fp fpm 2 _ Hrel Rg). reflexivity.
+ rewrite (X1 k Hk Hki Hne). exact (XSL k Hk Hki).
- exact XNF.
Qed.
Lemma af_xe1_unz : forall H (m m' : word -> option byte) md md' S Sc s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Xv cb (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ Xv ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> In (nimg, N) Xv -> (Z.land fattr 1 <> 0 -> In (npal, 3 * nlp) Xv) ->
m_fs md' = m_fs md -> m_fds md' = m_fds md -> length (cg_frames s1) = 3%nat ->
af_xe1 K MT XN S Sc (mrestrict H m) md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xe1 K MT XN S Sc (mrestrict H m') md' s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF.
Proof.
intros H m m' md md' S Sc s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Xv cb Zs UN XZb XZi Hpf Hni Hnp Efs Efd Hlen
(XS & XH & X1 & X2 & XSL & X3 & X4 & X5 & X6 & XGI & XGIL & XGL & XR).
assert (KV : forall a n k, In (a, n) (af_xvblocks s1 N) -> 0 <= k < n -> mbyte SEGS (mrestrict H m') (a + k) = mbyte SEGS (mrestrict H m) (a + k)).
{ intros a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k ltac:(apply in_app_iff; left; exact Hin) ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn). }
assert (KX : forall a n k, In (a, n) Xv -> 0 <= k < n -> mbyte SEGS (mrestrict H m') (a + k) = mbyte SEGS (mrestrict H m) (a + k)).
{ intros a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hin) ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn). }
split; [| split; [| split; [exact X1 | split; [exact X2 | split; [| split; [exact X3 | split; [exact X4 | split; [exact X5 | split; [exact X6 | split; [| split; [exact XGIL | split; [| exact XR]]]]]]]]]]]].
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
- eapply garr8_frame; [exact XGI|]. intros a Ha. replace a with (nimg + (a - nimg)) by lia. apply (KX nimg N); [exact Hni | lia].
- intros Hz. destruct (XGL Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (npal + (a - npal)) by lia. apply (KX npal (3 * nlp)); [exact (Hnp Hz) | lia].
Qed.
Definition af_gs4 (gattr : Z) (gs1 : YO07.gif_st) (i : Z) : YO07.gif_st :=
YO07.q_set gs1 (i - 1) (af_fb3 gattr (qslot gs1 (Z.to_nat i - 1))).
Lemma af_gs4_slot : forall gattr gs1 i k, (i = 1 \/ i = 2) -> (k < 3)%nat ->
qslot (af_gs4 gattr gs1 i) k = if (k =? Z.to_nat i - 1)%nat then af_fb3 gattr (qslot gs1 (Z.to_nat i - 1)) else qslot gs1 k.
Proof.
intros gattr gs1 i k Hi Hk. unfold af_gs4. replace (i - 1) with (Z.of_nat (Z.to_nat i - 1)) by (destruct Hi as [-> | ->]; reflexivity).
apply qslot_set; [exact Hk | destruct Hi as [-> | ->]; cbn; lia].
Qed.
Definition af_fnew_ok (s : cgif_st) (fnew : frame_st) (nimg npal fattr fgen delay nlp tidx : Z) : Prop :=
fr_attr fnew = fattr /\ fr_gen fnew = fgen /\ fr_delay fnew = delay /\ fr_nlp fnew = nlp /\ (Z.land fattr 6 <> 0 -> fr_ctidx fnew = tidx) /\
fr_disp fnew = (if Z.land (cg_attr s) 8 =? 0 then 4 else 8) /\ fr_tidx fnew = 0 /\ fr_img fnew = nimg /\ (Z.land fattr 1 <> 0 -> fr_lpal fnew = npal).
Lemma af_xe1_e2 : forall S Sc m md s s1 s2 N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat ->
rw_cur s2 = rw_cur s1 -> rw_attr s2 = rw_attr s1 -> cg_attr s2 = cg_attr s1 -> cg_pal s2 = cg_pal s1 -> cg_ngp s2 = cg_ngp s1 -> cg_ihead s2 = i ->
(forall k, (k < 3)%nat -> k <> Z.to_nat i -> k <> (Z.to_nat i - 1)%nat -> nth k (cg_frames s2) None = nth k (cg_frames s1) None) ->
oframe_relbA SEGS (wgk (Z.to_nat i - 1)) m N (nth (Z.to_nat i - 1) (cg_frames s2) None) (af_fb3 (cg_attr s) (qslot gs1 (Z.to_nat i - 1))) ->
af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx ->
af_xe1 K MT XN S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xe2 K MT XN S Sc m md s s2 N i fnew fattr fgen delay nlp tidx GPAL IMG LPAL gs (af_gs4 (cg_attr s) gs1 i) gsF.
Proof.
intros S Sc m md s s1 s2 N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen E1 E2 E3 E4 E5 E6 Hoth Hprev
(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) (XS & XH & X1 & X2 & XSL & X3 & X4 & X5 & X6 & XGI & XGIL & XGL & XO & XM).
assert (Hi1 : (Z.to_nat i - 1 < 3)%nat /\ (Z.to_nat i - 1)%nat <> Z.to_nat i) by (destruct Hi as [-> | ->]; cbn; lia).
split; [| split; [| split; [| split; [exact X5 | split; [exact X6 | split; [exact XO | exact XM]]]]]].
- split; [exact XS|]. split; [| split].
+ apply (af_xhdr_ext2 SEGS m s1 s2 GPAL gs1 gsF E1 E2 E3 E4 E5 X1); [rewrite E6, X2; reflexivity | exact XH].
+ intros k Hk Hki. rewrite (af_gs4_slot (cg_attr s) gs1 i k Hi Hk).
destruct (Nat.eqb_spec k (Z.to_nat i - 1)) as [-> | Hne]; [exact Hprev | rewrite (Hoth k Hk Hki Hne); exact (XSL k Hk Hki)].
+ unfold af_xnewf. rewrite A1, A2, A3, A4, A6, A7, A8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact A5|]. split; [cbn [YO07.f_disp YO07.new_frame gcfg_of YO07.g_attr]; unfold YO07.flag; destruct (Z.land (cg_attr s) 8 =? 0); reflexivity|].
split; [reflexivity|]. split; [exact XGI|]. split; [exact XGIL|]. intros Hz. rewrite (A9 Hz). exact (XGL Hz).
- intros k Hk Hki Hne. rewrite (af_gs4_slot (cg_attr s) gs1 i k Hi Hk). destruct (Nat.eqb_spec k (Z.to_nat i - 1)) as [Hq | _]; [exfalso; exact (Hne Hq) | exact (X3 k Hk Hki Hne)].
- rewrite (af_gs4_slot (cg_attr s) gs1 i _ Hi (proj1 Hi1)), Nat.eqb_refl. exact X4.
Qed.
Lemma af_xe1_e2_plain : forall S Sc m md s s1 N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> Z.land (cg_attr s) 8 = 0 ->
af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx ->
af_xe1 K MT XN S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xe2 K MT XN S Sc m md s (set_ihead (upd_frame s1 (Z.to_nat i) fnew) i) N i fnew fattr fgen delay nlp tidx GPAL IMG LPAL gs (af_gs4 (cg_attr s) gs1 i) gsF.
Proof.
intros S Sc m md s s1 N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen H8 HF XE.
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (Hi1 : (Z.to_nat i - 1 < 3)%nat /\ (Z.to_nat i - 1)%nat <> Z.to_nat i) by (destruct Hi as [-> | ->]; cbn; lia).
apply (af_xe1_e2 S Sc m md s s1 (set_ihead (upd_frame s1 (Z.to_nat i) fnew) i) N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl); [| | exact HF | exact XE].
- intros k Hk Hki _. cbn [set_ihead cg_frames]. rewrite (nth_upd_frame s1 (Z.to_nat i) fnew k Hlen Hi3). destruct (Nat.eqb_spec k (Z.to_nat i)) as [Hq | _]; [exfalso; exact (Hki Hq) | reflexivity].
- cbn [set_ihead cg_frames]. rewrite (nth_upd_frame s1 (Z.to_nat i) fnew _ Hlen Hi3). destruct (Nat.eqb_spec (Z.to_nat i - 1) (Z.to_nat i)) as [Hq | _]; [exfalso; exact (proj2 Hi1 Hq)|].
unfold af_fb3, YO07.flag. rewrite H8. cbn [Z.eqb negb]. pose proof XE as (_ & _ & _ & _ & XSL & _). exact (XSL _ (proj1 Hi1) (proj2 Hi1)).
Qed.
Lemma af_xe1_e2_tr_none : forall S Sc m md s s1 N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> nth (Z.to_nat i - 1) (cg_frames s1) None = None ->
af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx ->
af_xe1 K MT XN S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xe2 K MT XN S Sc m md s (set_ihead (upd_frame s1 (Z.to_nat i) fnew) i) N i fnew fattr fgen delay nlp tidx GPAL IMG LPAL gs (af_gs4 (cg_attr s) gs1 i) gsF.
Proof.
intros S Sc m md s s1 N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen Hop HF XE.
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (Hi1 : (Z.to_nat i - 1 < 3)%nat /\ (Z.to_nat i - 1)%nat <> Z.to_nat i) by (destruct Hi as [-> | ->]; cbn; lia).
apply (af_xe1_e2 S Sc m md s s1 (set_ihead (upd_frame s1 (Z.to_nat i) fnew) i) N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl); [| | exact HF | exact XE].
- intros k Hk Hki _. cbn [set_ihead cg_frames]. rewrite (nth_upd_frame s1 (Z.to_nat i) fnew k Hlen Hi3). destruct (Nat.eqb_spec k (Z.to_nat i)) as [Hq | _]; [exfalso; exact (Hki Hq) | reflexivity].
- cbn [set_ihead cg_frames]. rewrite (nth_upd_frame s1 (Z.to_nat i) fnew _ Hlen Hi3). destruct (Nat.eqb_spec (Z.to_nat i - 1) (Z.to_nat i)) as [Hq | _]; [exfalso; exact (proj2 Hi1 Hq)|].
pose proof XE as (_ & _ & _ & _ & XSL & _). pose proof (XSL _ (proj1 Hi1) (proj2 Hi1)) as Hrel. rewrite Hop in Hrel |- *.
pose proof (proj1 (oframe_relbA_occ SEGS _ _ _ _ _ Hrel) eq_refl) as Hq1. rewrite Hq1. unfold af_fb3. destruct (YO07.flag (cg_attr s) 8); exact I.
Qed.
Lemma af_xe1_e2_tr_some : forall S Sc m md s s1 N i fnew fp nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF,
(i = 1 \/ i = 2) -> length (cg_frames s1) = 3%nat -> Z.land (cg_attr s) 8 <> 0 ->
nth (Z.to_nat i - 1) (cg_frames s1) None = Some fp -> 0 <= fr_gen fp < 2 ^ 64 ->
af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx ->
af_xe1 K MT XN S Sc m md s s1 N i nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF ->
af_xe2 K MT XN S Sc m md s (set_ihead (upd_frame (upd_frame s1 (Z.to_nat i) fnew) (Z.to_nat i - 1) (set_fr_gen_disp fp (Z.land (fr_gen fp) 18446744073709551612) 8)) i)
N i fnew fattr fgen delay nlp tidx GPAL IMG LPAL gs (af_gs4 (cg_attr s) gs1 i) gsF.
Proof.
intros S Sc m md s s1 N i fnew fp nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen H8 Hop Rg HF XE.
assert (Hi3 : (Z.to_nat i < 3)%nat) by (destruct Hi as [-> | ->]; cbn; lia).
assert (Hi1 : (Z.to_nat i - 1 < 3)%nat /\ (Z.to_nat i - 1)%nat <> Z.to_nat i) by (destruct Hi as [-> | ->]; cbn; lia).
set (s1' := upd_frame s1 (Z.to_nat i) fnew).
assert (Hlen' : length (cg_frames s1') = 3%nat) by (subst s1'; unfold upd_frame, set_frames; cbn [cg_frames]; rewrite length_list_set; exact Hlen).
apply (af_xe1_e2 S Sc m md s s1 (set_ihead (upd_frame s1' (Z.to_nat i - 1) (set_fr_gen_disp fp (Z.land (fr_gen fp) 18446744073709551612) 8)) i) N i fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF Hi Hlen eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl); [| | exact HF | exact XE].
- intros k Hk Hki Hk1. cbn [set_ihead cg_frames]. rewrite (nth_upd_frame s1' (Z.to_nat i - 1) _ k Hlen' (proj1 Hi1)).
destruct (Nat.eqb_spec k (Z.to_nat i - 1)) as [Hq | _]; [exfalso; exact (Hk1 Hq)|]. subst s1'.
rewrite (nth_upd_frame s1 (Z.to_nat i) fnew k Hlen Hi3). destruct (Nat.eqb_spec k (Z.to_nat i)) as [Hq | _]; [exfalso; exact (Hki Hq) | reflexivity].
- cbn [set_ihead cg_frames]. rewrite (nth_upd_frame s1' (Z.to_nat i - 1) _ _ Hlen' (proj1 Hi1)), Nat.eqb_refl.
pose proof XE as (_ & _ & _ & _ & XSL & _). pose proof (XSL _ (proj1 Hi1) (proj2 Hi1)) as Hrel. rewrite Hop in Hrel.
destruct (qslot gs1 (Z.to_nat i - 1)) as [fpm|]; [| destruct Hrel]. cbn [oframe_relbA] in Hrel.
unfold af_fb3. replace (YO07.flag (cg_attr s) 8) with true by (unfold YO07.flag; destruct (Z.eqb_spec (Z.land (cg_attr s) 8) 0); [exfalso; exact (H8 ltac:(assumption)) | reflexivity]).
cbn [YO07.omap oframe_relbA]. apply (frame_relbA_fb _ m N fp fpm 3 _ Hrel Rg). reflexivity.
Qed.
Lemma af_reseedxEX : forall pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 X more,
let a4v := (if Z.land fattr 4 =? 0 then 1 else 0) in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cxS B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 X ->
getr regs1 2 = w64 (spZ regs - 224) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 224 - 0)) lcx ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regionsX 0 true (af_lcE ++ lcx) (cg_ihead s1) wlo whi) = true ->
In (pf, FILE_BLOCK) rest ->
st_ok_pi SEGS VAL E (ss_afX pc sregs 0 true (af_lcE ++ lcx) (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 X more a4v E
CX MID Rsp HL HLX Hwlo Hwhi HREG HWFR Hpfr.
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
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as HFO1.
pose proof HFO1 as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR1 Hfin) as Hfhigh_img.
assert (Hcfp : 0 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (Rsp' : bv_unsigned (getr regs1 2) = sp0 - 224 - 0) by (rewrite Rsp; rewrite unsigned_lit_small by lia; lia).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more)) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67.
cbn [Nat.sub nth af_extra map app firstn repeat] in E32, E38, E46, E67.
assert (Ha4 : 0 <= a4v < 2 ^ 64) by (subst a4v; destruct (Z.land fattr 4 =? 0); lia).
exact (af_seedX B TL LAWS pc sregs 0 true (af_lcE ++ lcx) (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(proj2 (Forall_app _ _ _) (conj (af_lcE_ok E _ sp0 g cfp a4v HL E32 E38 E46 E67 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) Ha4) HLX))
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF Hpfcb)).
Qed.
End h.
End d.
End b.
