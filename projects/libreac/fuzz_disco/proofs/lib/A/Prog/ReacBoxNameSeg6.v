(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntHeardAnything.v, with its module paths and module names changed; 221 of its 255 lines of code are new or changed and 214 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops ReacBoxNameSeg4.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition rbn6_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 22; 24; 27; 29; 30].
Ltac rbn_rget HR r H :=
  pose proof (HR r) as H;
  lazymatch type of H with _ = sv_denot ?E (sr_get ?s ?r') =>
    let e := eval vm_compute in (sr_get s r') in change (sr_get s r') with e in H end.
Ltac rbn_runh pc stop H :=
  let r := eval vm_compute in (sym_run_toN_pi pl_tpi FUEL stop (mkSS pc sr_atoms [] None (mkFacts [] [] []))) in
  lazymatch r with (?ss', ?st) =>
    assert (H : sym_run_toN_pi pl_tpi FUEL stop (mkSS pc sr_atoms [] None (mkFacts [] [] [])) = (ss', st))
      by (vm_compute; reflexivity) end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma rbn_sv_off : forall (regs : bvmap 5 word) n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (Eimg (Ereg regs [])) (SOff n 0) = getr regs r.
Proof.
intros regs n r Hn. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Eimg_Ereg_nat. exact Hn.
Qed.
Lemma rbn_sltu1 : forall E v, sv_denot E (SOff 13 0) = w64 v -> (v = 0 \/ v = 1) ->
  sv_denot E (SAlu Instr.ALU_SLTU (SOff 13 0) (SLit 1)) = w64 (1 - v).
Proof.
intros E v H [-> | ->];
change (sv_denot E (SAlu Instr.ALU_SLTU (SOff 13 0) (SLit 1)))
  with (alu64 Instr.ALU_SLTU (sv_denot E (SOff 13 0)) (Z_to_bv 64 1)); rewrite H; vm_compute; reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn_plain : forall (fq : YK11.FPState) (W : world SEGS) regs memc mdc pc0 n stop ss' st
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sym_run_toN_pi pl_tpi n stop (mkSS pc0 sr_atoms [] None (mkFacts [] [] [])) = (ss', st) ->
  pi_plain_stop st -> ss_resv ss' = None ->
  (forall regs' mat',
     (forall r, getr regs' r = sv_denot (Eimg (Ereg regs [])) (sr_get (ss_regs ss') r)) ->
     (forall r : bv 5, sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0) = true ->
        getr regs' r = getr regs r) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + ss_pc ss') regs' memc (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + pc0) regs memc mdc) Q.
Proof.
intros fq W regs memc mdc pc0 n stop ss' st STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ Hrun Hst Hrv HK.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (HA : env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])))
  by (split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc0 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc0)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply (regs_ok_agree 32 (Ereg regs [])); [exact HA | vm_compute; reflexivity | apply regs_ok_Ereg].
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat split. }
unfold cfg_at. change (w64 (BASE + pc0)) with (Z_to_bv 64 (BASE + pc0)).
eapply (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS W n stop _ _ ss' st _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k Q
  HEI HS Hrun Hst HJ).
- apply awr_ok_nil.
- intros ms' mat' HS' HJ' HF _ _.
  assert (Hm : ms_mem ms' = memc) by exact (frame_of_read_only _ [] _ _ eq_refl HF).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv).
  rewrite Hm in HJ' |- *.
  apply (HK (ms_regs ms') mat'); [| |exact HJ'].
  + intros r. exact (st_ok_pi_restrict_reg _ _ _ _ r HS').
  + intros r Hr. apply (regs_kept_of_st_ok_pi _ _ _ regs [] [r] HS' HA); [|left; reflexivity].
    cbn [forallb]. rewrite Hr. reflexivity.
Qed.
Lemma rbn6_post : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs3 mem2 md3,
  rbn_cx B X -> rbn_st6 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md3 (ri_k X) ->
  (forall r, In r rbn6_keep -> getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  getr regs3 26 = w64 (Z.of_nat (length (rbm_TB X))) ->
  getr regs3 21 = w64 (rbm_tok X) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (rbn_F X pos + 128 <= a < rbn_F X pos + 128 + Z.of_nat (length (rbm_TB X))) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  garr8 SEGS (mrestrict (w_H W1) mem2) (rbn_F X pos + 128) (rbm_TB X) ->
  rbn_st7 B X pos regs3 lyc1 Sc1 W1 mem2 md3.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs3 mem2 md3 HX H6 HJ3 KK G26 G21 HEQ HG.
destruct H6 as (HM & HRB & R18 & R27 & R24 & R30 & R29 & HC & HNB & HA).
destruct (rbn_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
assert (HTB : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
assert (HFrm : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) by (intros a Ha Hf; apply HEQ; lia).
assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) rbn6_keep = true -> getr regs3 r = getr regs1 r).
{ intros r Hr. apply existsb_exists in Hr. destruct Hr as (x & Hx & Hxe). apply Z.eqb_eq in Hxe.
  rewrite <- Hxe in Hx. pose proof (KK _ Hx) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. }
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
unfold rbn_st7. split.
{ apply (rbn_mid_fw B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md3 _ (rbn_F X pos + 128)
    (Z.of_nat (length (rbm_TB X))) HX HM HJ3); [rewrite rbn_sh_len; lia | lia | lia | lia | exact HEQ]. }
split.
{ unfold rbn_rbase.
  split; [rewrite KG by reflexivity; exact B2|]. split; [rewrite KG by reflexivity; exact B3|].
  split; [rewrite KG by reflexivity; exact B4|]. split; [rewrite KG by reflexivity; exact B8|].
  split; [rewrite KG by reflexivity; exact B9|]. split; [rewrite KG by reflexivity; exact B19|].
  rewrite KG by reflexivity; exact B22. }
split; [rewrite KG by reflexivity; exact R18|]. split; [rewrite KG by reflexivity; exact R27|].
split; [rewrite KG by reflexivity; exact R24|]. split; [rewrite KG by reflexivity; exact R30|].
split; [rewrite KG by reflexivity; exact R29|].
split; [exact G26|]. split; [exact G21|].
split.
{ apply (rbn_hi_kept B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem2 HX HM HFrm); [|exact HC].
  intros a n0 v k Hin Hk. pose proof (rbn_locs6_rng X pos a n0 v Hin). lia. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HNB|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HEQ; lia. }
split; [exact HG | exact HA].
Qed.
Lemma rbn6_tail : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' nF ovF wr W2 c2,
  rbn_cx B X -> rbn_st6 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall r, In r rbn6_keep -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  rbn_lpost B (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (ri_k X) regs' RBN_L3X [5; 6; 7; 10; 11; 12; 13; 16; 17; 26; 28]
    (rbn_F X pos + 128) 0 wr [(26, nF); (13, ovF)] W2 c2 ->
  nF = Z.of_nat (length (rbm_TB X)) -> (ovF = 0 \/ ovF = 1) -> 1 - ovF = rbm_tok X -> wr = rbm_TB X ->
  SRr SEGS W2 c2 (rbn_at7 B X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' nF ovF wr W2 c2 HX H6 KK1
  (-> & regs2 & mem2 & md2 & -> & HJ2 & HK2 & HO & HEQ & HG) -> Hov Htok ->.
pose proof (Forall_inv HO) as O26. pose proof (Forall_inv (Forall_inv_tail HO)) as O13.
cbn [fst snd] in O26, O13. rewrite Z.add_0_r in HEQ, HG.
replace (BASE + AF_reac_box_name + RBN_L3X) with (BASE + 15420) by (unfold AF_reac_box_name, RBN_L3X; lia).
rbn_runh 15420 15424 Hrun.
apply (rbn_plain (ri_fq X) W1 regs2 mem2 md2 15420 FUEL 15424 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Hrun I eq_refl).
intros regs3 mat3 HR3 KP3 HJ3.
apply SRr_ret.
exists pos, regs3, lyc1, Sc1, mem2, (with_vm_backing (m_vm_lazy md2) mat3 md2). split.
{ unfold rbn_cfg. cbn [ss_pc].
  replace (BASE + AF_reac_box_name + RBN_P7) with (BASE + 15424) by (unfold AF_reac_box_name, RBN_P7; lia).
  reflexivity. }
assert (KK2 : forall r, In r rbn6_keep -> getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  apply HK2; [lia|]. cbn [In]. lia. }
assert (KK3 : forall r, In r rbn6_keep -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply KP3; vm_compute; reflexivity|]). destruct Hr. }
assert (H13 : sv_denot (Eimg (Ereg regs2 [])) (SOff 13 0) = w64 ovF).
{ rewrite (rbn_sv_off regs2 13 13%bv eq_refl). apply rbn_out_get. exact O13. }
rbn_rget HR3 (21%bv : bv 5) G21. rewrite (rbn_sltu1 _ ovF H13 Hov), Htok in G21.
assert (G26 : getr regs3 26 = w64 (Z.of_nat (length (rbm_TB X)))).
{ rewrite (KP3 26%bv) by (vm_compute; reflexivity). apply rbn_out_get. exact O26. }
apply (rbn6_post X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs3 mem2 _ HX H6 HJ3); [| exact G26 | exact G21 | exact HEQ | exact HG].
intros r Hr. rewrite (KK3 r Hr), (KK2 r Hr). exact (KK1 r Hr).
Qed.
Hypothesis L3F : rbn_L3_fits B.
Hypothesis L3O : rbn_L3_ovf B.
Theorem rbn_seg6 : rbn_seg6_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H6.
pose proof H6 as (HM & HRB & R18 & R27 & R24 & R30 & R29 & HC & HNB & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
pose proof (rbn_NB_ne X) as Hne.
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
destruct (proj1 (garr8_app SEGS _ _ _ _) HNB) as [HNBg _].
pose proof (garr8_bytes_ok SEGS _ _ _ HNBg) as Hby.
pose proof (rbn_lbuf_fr B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ 8 3 HX HM ltac:(lia) ltac:(lia)
  ltac:(rewrite rbn_sh_len; lia) ltac:(lia)
  ltac:(intros i Hi; assert (i = 8 \/ i = 9 \/ i = 10) as [-> | [-> | ->]] by lia; reflexivity)) as Hb64.
destruct Hb64 as (_ & _ & _ & Hra64 & _).
assert (Hsrc : rbn_lsrc W1 memc1 (rbn_F X pos + 64) (rbm_NB X)).
{ split; [exact HNBg|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply (range_addressable_sub _ _ (rbn_F X pos + 8 * 8) (8 * 3)); [exact Hra64 | lia | lia]. }
assert (Hbuf : rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  memc1 (rbn_F X pos + 128) 24).
{ exact (rbn_lbuf_fr B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ 16 3 HX HM ltac:(lia) ltac:(lia)
    ltac:(rewrite rbn_sh_len; lia) ltac:(lia)
    ltac:(intros i Hi; assert (i = 16 \/ i = 17 \/ i = 18) as [-> | [-> | ->]] by lia; reflexivity)). }
assert (Hsep : rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) <= rbn_F X pos + 128 \/
  rbn_F X pos + 128 + 24 <= rbn_F X pos + 64) by lia.
pose proof HM as (HJ1 & _).
unfold rbn_cfg.
replace (BASE + AF_reac_box_name + RBN_P6) with (BASE + 15244) by (unfold AF_reac_box_name, RBN_P6; lia).
rbn_runh 15244 15276 Hrun.
apply (rbn_plain (ri_fq X) W1 regs1 memc1 mdc1 15244 FUEL 15276 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 Hrun I eq_refl).
intros regs' mat' HR KP HJ'.
cbn [ss_pc].
replace (BASE + 15276) with (BASE + AF_reac_box_name + RBN_L3) by (unfold AF_reac_box_name, RBN_L3; lia).
assert (KK1 : forall r, In r rbn6_keep -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply KP; vm_compute; reflexivity|]). destruct Hr. }
rbn_rget HR (12%bv : bv 5) G12. rbn_rget HR (26%bv : bv 5) G26. rbn_rget HR (13%bv : bv 5) G13. rbn_rget HR (14%bv : bv 5) G14.
rbn_rget HR (15%bv : bv 5) G15. rbn_rget HR (16%bv : bv 5) G16. rbn_rget HR (10%bv : bv 5) G10. rbn_rget HR (17%bv : bv 5) G17.
rewrite (rbn_sv_off regs1 27 27%bv eq_refl), R27 in G16, G10.
rewrite (rbn_sv_off regs1 24 24%bv eq_refl), R24 in G17.
assert (G29 : getr regs' 29 = w64 (rbn_F X pos + 128)) by (rewrite (KP 29%bv) by (vm_compute; reflexivity); exact R29).
assert (G22 : getr regs' 22 = w64 SHADOW_OFF) by (rewrite (KP 22%bv) by (vm_compute; reflexivity); exact B22).
destruct (Z_le_gt_dec (Z.of_nat (length (bn_TK (rbm_NB X)))) 23) as [Hf | Ho].
- pose proof (L3F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) (ri_k X) regs' (rbn_F X pos + 64) (rbn_F X pos + 128) (rbm_NB X) Hf)
    as R.
  unfold rbn_L3_run in R.
  eapply SRr_bind; [apply R; first [exact HJ' | exact Hne | exact Hby | exact Hsrc | exact Hbuf | exact Hsep
    | assumption] |].
  intros W2 c2 _ Hp. apply (rbn6_tail X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' _ _ _ W2 c2 HX H6 KK1 Hp).
  + unfold rbm_TB. rewrite firstn_all2 by lia. reflexivity.
  + left; reflexivity.
  + unfold rbm_tok, rbm_ovf. replace (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))) with false
      by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + unfold rbm_TB. rewrite firstn_all2 by lia. reflexivity.
- pose proof (L3O (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) (ri_k X) regs' (rbn_F X pos + 64) (rbn_F X pos + 128) (rbm_NB X) ltac:(lia))
    as R.
  unfold rbn_L3_run in R.
  eapply SRr_bind; [apply R; first [exact HJ' | exact Hne | exact Hby | exact Hsrc | exact Hbuf | exact Hsep
    | assumption] |].
  intros W2 c2 _ Hp. apply (rbn6_tail X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' _ _ _ W2 c2 HX H6 KK1 Hp).
  + unfold rbm_TB. rewrite firstn_length_le by lia. reflexivity.
  + right; reflexivity.
  + unfold rbm_tok, rbm_ovf. replace (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))) with true
      by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  + reflexivity.
Qed.
End h.
End f.
End d.
