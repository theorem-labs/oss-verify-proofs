(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 459 of its 586 lines of code are new or changed and 964 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44 YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition rbn6_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27].
Definition rbn6_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))]].
Definition rbn6_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 1 23 0)] [] [].
Definition ss_rbn6 : sstate := mkSS 0x3b00 sr_atoms rbn6_regions None rbn6_facts.
Ltac rbn6_rget HR r H :=
  pose proof (HR r) as H;
  lazymatch type of H with _ = sv_denot ?E (sr_get ?s ?r') =>
    let e := eval vm_compute in (sr_get s r') in change (sr_get s r') with e in H end.
Ltac rbn6_runh stop H :=
  let r := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_both3_0) FUEL stop ss_rbn6) in
  lazymatch r with (?ss', ?st) =>
    assert (H : sym_run_toN_pi (@pl_tpi _ PL_both3_0) FUEL stop ss_rbn6 = (ss', st)) by (vm_compute; reflexivity) end.
Lemma rbn6_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn6_kg : forall (ra rb : bvmap 5 word) l,
  (forall r, In r l -> getr ra (Z_to_bv 5 r) = getr rb (Z_to_bv 5 r)) ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) l = true -> getr ra r = getr rb r.
Proof.
intros ra rb l KK r Hr. apply existsb_exists in Hr. destruct Hr as (x & Hx & Hxe). apply Z.eqb_eq in Hxe.
rewrite <- Hxe in Hx. pose proof (KK _ Hx) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn6_lit : forall E v, 0 <= v < 2 ^ 64 -> sv_denot E (SLit v) = w64 v.
Proof. intros E v Hv. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition ERB6 (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs [Z_to_bv 64 n]).
Lemma rbn6_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbn6_cells_app : forall m l1 l2, rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|]. rewrite IH. tauto.
Qed.
Lemma rbn6_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn6_locs_rng : forall X pos n1 o1 n2 o2 a n v,
  In (a, n, v) ((rbn_argc X ++ rbn_rw X pos n1 o1) ++ rbn_rn X pos n2 o2) ->
  (rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64) \/ (rbn_A X + 152 <= a /\ a + Z.of_nat n <= rbn_A X + 212).
Proof.
intros X pos n1 o1 n2 o2 a n v H.
apply in_app_or in H as [H | H]; [apply in_app_or in H as [H | H]|];
[unfold rbn_argc in H | unfold rbn_rw in H | unfold rbn_rn in H]; cbn [In] in H;
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]); destruct H.
Qed.
Lemma rbn6_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn6_NB_ne : forall X, (1 <= length (rbm_NB X))%nat.
Proof.
intros X. assert (H : rbm_NM X <> []).
{ unfold rbm_NM, bn_NM. cbv zeta. pose proof (rbn6_stem_ne X) as Hne. unfold rbm_stem in Hne.
  match goal with |- (if ?b then _ else _) <> [] => destruct b end; [exact Hne|].
  destruct (bn_stem (ri_f X) (ri_sd X)); discriminate. }
unfold rbm_NB. destruct (rbm_NM X) as [|c l]; [exfalso; exact (H eq_refl)|]. cbn [firstn length]. lia.
Qed.
Lemma rbn6_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc (A n : Z),
  getr regs 9 = w64 A -> 2 ^ 46 <= A <= 2 ^ 47 -> A mod 32 = 0 -> 1 <= n <= 23 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 168) 8 n ->
  st_ok_pi SEGS VAL (ERB6 regs n) ss_rbn6
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + ss_pc ss_rbn6)) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc A n H9 HA HA32 Hn Mn.
rewrite restrict_mkst_fx.
assert (E9 : ew (ERB6 regs n) 9 = Z_to_bv 64 A)
  by (unfold ERB6; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew (ERB6 regs n) 32 = Z_to_bv 64 n)
  by (unfold ERB6; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB9 : base_val (ERB6 regs n) (Some 9%nat) = A) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
unfold ss_rbn6, rbn6_regions. cbn [ss_pc]. apply pa_entry_st_ok_full.
- unfold ERB6. apply (regs_ok_agree 32 (Ereg regs [Z_to_bv 64 n])).
  + split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  + vm_compute. reflexivity.
  + apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB9.
  split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS (ERB6 regs n) _ A 168 8 _ n);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact Mn.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- unfold rbn6_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E9, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; split; [lia|]; split; [exact HA32 | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
  exact I.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn6_run : forall (fq : YK11.FPState) (W : world SEGS) regs memc mdc n stop ss' st
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  st_ok_pi SEGS VAL (ERB6 regs n) ss_rbn6
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + ss_pc ss_rbn6)) memc (seg_rom SEGS))) ->
  sym_run_toN_pi (@pl_tpi _ PL_both3_0) FUEL stop ss_rbn6 = (ss', st) ->
  pi_plain_stop st -> ss_resv ss' = None ->
  (forall regs' mat',
     (forall r, getr regs' r = sv_denot (ERB6 regs n) (sr_get (ss_regs ss') r)) ->
     (forall r : bv 5, sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0) = true ->
        getr regs' r = getr regs r) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + ss_pc ss') regs' memc (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + ss_pc ss_rbn6) regs memc mdc) Q.
Proof.
intros fq W regs memc mdc n stop ss' st STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ HS Hrun Hst Hrv HK.
assert (HEI : img_env VAL A_LIM (ERB6 regs n)) by apply Eimg_env.
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 n]) (ERB6 regs n))
  by (split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at. change (w64 (BASE + ss_pc ss_rbn6)) with (Z_to_bv 64 (BASE + ss_pc ss_rbn6)).
eapply (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) B LAWS W FUEL stop (ERB6 regs n) ss_rbn6 ss' st _
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k Q HEI HS Hrun Hst HJ).
- apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- intros ms' mat' HS' HJ' HF _ _.
  assert (Hm : ms_mem ms' = memc) by exact (frame_of_read_only _ (ss_mem ss_rbn6) _ _ eq_refl HF).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv).
  rewrite Hm in HJ' |- *.
  apply (HK (ms_regs ms') mat'); [| |exact HJ'].
  + intros r. exact (st_ok_pi_restrict_reg _ _ _ _ r HS').
  + intros r Hr. apply (regs_kept_of_st_ok_pi _ _ _ regs [Z_to_bv 64 n] [r] HS' HA); [|left; reflexivity].
    cbn [forallb]. rewrite Hr. reflexivity.
Qed.
Lemma rbn6_fa : forall X own lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    own lyc1 Sc1 W1 memc1 mdc1 (ri_k X) ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X own lyc1 Sc1 W1 memc1 mdc1 HX HJ c p.
destruct HX as ((_ & L0 & _) & _). destruct HJ as (_ & L1 & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn6_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_SP X + 16 <= 2 ^ 47 /\ ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  rbn_A X mod 32 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
assert (Hm : 32 * ((spZ (ri_regs X) - 320) / 32) mod 32 = 0) by (rewrite Z.mul_comm; apply Z.mod_mul; lia).
lia.
Qed.
Lemma rbn6_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) ->
  frames Sc1 = (3, pos) :: frames (ri_Sc X) ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\ off_img (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HJ1 Hfrs.
pose proof (rbn6_fa X _ lyc1 Sc1 W1 memc1 mdc1 HX HJ1 3 pos) as FA.
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
pose proof (frm_off_imgP B _ _ _ _ _ 3 pos HAR1 Hin3) as Hoff.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|]. split; [exact Hoff|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
Qed.
Lemma rbn6_stk_sh : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k a n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  sp0 - STK + 64 <= a -> a + n + 64 <= sp0 -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) a n).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k a n HJ Ha Han Hn.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (am_layout B lyc Sc _ (proj1 HAR)) as HLY.
pose proof (lo_top lyc HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
pose proof (al_zshadow _ _ LAWS lyc Sc W m md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz. rewrite Elo, Ehi in *.
split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
    by (unfold shadow_of_addr; lia).
  apply Hz. clear - Hy Lplo Lphi Hslo Hshi Ha Han Hn. lia.
- intros Hn0 s Hs.
  replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
  rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
  clear - Hs Hn0 Lplo Lphi Hslo Hshi Ha Han Hn. unfold SHADOW_OFF in *. lia.
Qed.
Lemma rbn6_fra : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh j c,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  0 <= j -> 0 <= c -> j + c <= Z.of_nat (length sh) ->
  (forall i, j <= i < j + c -> nth (Z.to_nat i) sh 0 = 0) ->
  range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (rbn_F X pos + 8 * j) (8 * c).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh j c HX HM Hj Hc Hl Hz.
pose proof HM as (HJ1 & Hfrs & _ & _ & _ & _ & _ & Hsh0).
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 HX HJ1 Hfrs) as (_ & _ & HFal & _).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
apply zero_shadow_range.
- replace (rbn_F X pos + 8 * j) with (rbn_F X pos + j * 8) by lia. rewrite Z.mod_add by lia. exact HF8.
- replace (8 * c) with (c * 8) by lia. apply Z.mod_mul. lia.
- intros i Hi. replace (8 * c / 8) with c in Hi by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  rewrite shadow_of_addr_add8. change (shadow_of_addr SHADOW_OFF (rbn_F X pos)) with (rbn_SH X pos).
  replace (rbn_SH X pos + j + i) with (rbn_SH X pos + (j + i)) by lia.
  rewrite (Hsh0 (j + i)) by lia. rewrite (Hz (j + i)) by lia. reflexivity.
Qed.
Lemma rbn6_lbuf : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true false) ->
  rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1
    (rbn_A X) (rbn_A X + 120) (rbn_F X pos + 128) 24.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM.
pose proof HM as (HJ1 & Hfrs & _).
pose proof (rbn6_fa X _ lyc1 Sc1 W1 memc1 mdc1 HX HJ1) as FA.
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 HX HJ1 Hfrs) as (HF4096 & HFceil & HFal & HFapp & HFoff & HFpr).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WT : TSB_CH_STK = 4112) by reflexivity.
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hia : in_app (rbn_F X pos + 128) 24) by (apply (in_app_sub _ _ _ _ HFapp); lia).
pose proof (rbn6_fra X pos lyc1 Sc1 W1 memc1 mdc1 _ 16 3 HX HM ltac:(lia) ltac:(lia)
  ltac:(rewrite rbn6_sh_len; lia)
  ltac:(intros i Hi; assert (i = 16 \/ i = 17 \/ i = 18) as [-> | [-> | ->]] by lia; reflexivity)) as Hra.
unfold rbn_lbuf.
split; [lia|]. split; [lia|]. split; [exact Hia|].
split; [unfold in_app, ASAN_CEIL in Hia; unfold amem_range, kLowMemEnd, kHighMemEnd, kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold off_img in *; lia|].
split; [right; lia|]. split; [left; lia|].
split; [exact Hra|].
split.
{ apply (shadow_hull_vis_of_frame SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 3 pos);
  [exact HAR1 | exact Hin3 | rewrite FA3; lia | rewrite FA3; change (fs_frame_bytes 3) with 512; lia | lia]. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA3. change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rbn6_lrec : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_rt X pos 0 0) ->
  rbn_lrec B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1
    (rbn_A X) (rbn_A X + 120) (rbn_F X pos + 128) 24 0 0.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh HX HM HC.
pose proof HM as (HJ1 & Hfrs & _).
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 HX HJ1 Hfrs) as (HF4096 & HFceil & _).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WT : TSB_CH_STK = 4112) by reflexivity.
destruct (rbn6_stk_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rbn_A X + 120) 28 HJ1 ltac:(lia) ltac:(lia) ltac:(lia))
  as (Hra & Hhv).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
unfold rbn_rt in HC. cbn [rbn_cells] in HC. destruct HC as (V1 & V2 & V3 & V4 & _).
unfold rbn_lrec.
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold amem_range, kHighMemBeg, kHighMemEnd; lia|].
split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
split; [left; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact V1|].
split; [replace (rbn_A X + 120 + 8) with (rbn_A X + 128) by lia; exact V2|].
split; [replace (rbn_A X + 120 + 16) with (rbn_A X + 136) by lia; exact V3|].
split; [replace (rbn_A X + 120 + 24) with (rbn_A X + 144) by lia; exact V4|].
split; [exact Hra|]. split; [apply Hhv; lia|].
intros a Ha. split; [left; lia | apply Hpres; lia].
Qed.
Lemma rbn6_mid_call : forall X pos lyc1 Sc1 lyc2 Sc2 (W1 W2 : world SEGS) m mdc1 m' md' sh (Er : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 m' md' (ri_k X) ->
  frames Sc2 = frames Sc1 -> ablocks B lyc2 Sc2 = ablocks B lyc1 Sc1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m') ->
  tsb_ch_kept B lyc1 Sc1 W1 m W2 m' (rbn_A X) Er ->
  (forall a, Er a -> (rbn_A X <= a < rbn_A X + 216) \/ (rbn_F X pos <= a < rbn_F X pos + 504)) ->
  Z.of_nat (length sh) <= 64 ->
  rbn_mid B X pos lyc2 Sc2 W2 m' md' (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 lyc2 Sc2 W1 W2 m mdc1 m' md' sh Er HX HM HJ2 Hfr2 Hbl2 Hro2 HKC HEr Hsh.
destruct HKC as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (rbn6_fa X _ lyc1 Sc1 W1 m mdc1 HX HJ1) as FA.
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 m mdc1 HX HJ1 Hfrs) as (HF4096 & HFceil & HFal & HFapp & HFoff & HFpr).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (WT : TSB_CH_STK = 4112) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (FR : forall c p, frame_rng lyc1 (c, p) = frame_rng (ri_lyc X) (c, p))
  by (intros c p0; unfold frame_rng; cbn [fst snd]; rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HnEr : forall a, ~ (rbn_A X <= a < rbn_A X + 216) -> ~ (rbn_F X pos <= a < rbn_F X pos + 504) -> ~ Er a)
  by (intros a H1 H2 He; destruct (HEr a He); contradiction).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|].
split; [rewrite Hbl2; exact Hperm|]. split; [exact Hro2|].
split.
{ unfold rbn_kept. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (C1 a ltac:(lia) ltac:(lia) (HnEr a ltac:(lia) ltac:(lia))).
    exact (K1 a Ha Hn' He).
  - intros b mm j Hb Hj He.
    assert (Hb1 : In (b, mm) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb1) as (_ & Hb4 & Hbc & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mm 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite (C2 b mm j Hb1 Hj (HnEr (b + j) ltac:(lia) ltac:(lia))).
    exact (K2 b mm j Hb Hj He).
  - intros a Hia Ho He. rewrite (C3 a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    rewrite FA in Hc4096, Hcceil.
    assert (HnE : ~ Er a).
    { apply HnEr.
      - destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; [lia|].
        pose proof (rbn6_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
          (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
        unfold kLowShadowBeg, kHighMemBeg in Hb. lia.
      - destruct Ha as [Ha | Ha].
        + destruct (in_split _ _ Hcp) as (l2 & l3 & El).
          pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
            ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
          unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, Hfb3, FA in Hd.
          unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. lia.
        + unfold in_zr in Ha. cbn [fst snd] in Ha.
          pose proof (rbn6_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
            (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
          intros Hf. destruct (Happ a ltac:(lia)); unfold kLowShadowBeg, kHighMemBeg in *; lia. }
    rewrite (C4 cid p a Hcp1 ltac:(rewrite FR, FA; exact Ha) HnE). exact (K4 cid p a Hcp Ha He).
  - intros a Ha Hn' Hp. exact (C5 a Ha ltac:(lia) (K5 a Ha Hn' Hp)).
  - intros a Ha.
    destruct (Z_lt_le_dec a (rbn_A X - TSB_CH_STK)) as [Hlt | Hge].
    + apply C5; [lia | lia | exact (K6 a Ha)].
    + destruct (Z_lt_le_dec a (rbn_A X)) as [Hlt2 | Hge2].
      * apply C6. lia.
      * apply C5; [lia | lia | exact (K6 a Ha)]. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m'); [|exact (Hfr j r Hj)].
  intros kk Hk. apply C1; [lia | lia | apply HnEr; lia]. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m'); [|exact Hfl].
  intros kk Hk. apply C1; [lia | lia | apply HnEr; lia]. }
unfold rbn_shadow_at. intros j Hj.
pose proof (rbn6_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
rewrite (C1 (shadow_addr (rbn_F X pos) + j)).
- exact (Hsh0 j Hj).
- unfold kLowShadowBeg, kHighMemBeg in Hb. lia.
- unfold kLowShadowBeg, kHighMemBeg in Hb. lia.
- apply HnEr.
  + unfold kLowShadowBeg, kHighMemBeg in Hb. lia.
  + intros Hf. destruct (Happ (shadow_addr (rbn_F X pos) + j) ltac:(lia)) as [Hq | Hq];
    unfold kLowShadowBeg, kHighMemBeg in Hb, Hq; lia.
Qed.
Lemma rbn6_tail : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' nF ovF wr W2 c2,
  rbn_cx B X -> rbn_st6 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall r, In r rbn6_keep -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  spZ regs' = rbn_A X ->
  rbn_lpost B (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (ri_k X) regs' RBN_L3X rbn_cl3
    (spZ regs' + 120) (rbn_F X pos + 128) 0 nF ovF wr W2 c2 ->
  nF = Z.of_nat (length (rbm_TB X)) -> ovF = rbm_ovf 23 (bn_TK (rbm_NB X)) -> wr = rbm_TB X ->
  rbn_at7 B X W2 c2.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' nF ovF wr W2 c2 HX H6 KK1 Hsp'
  (lyc2 & Sc2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hbl2 & Hro2 & HK2 & VnF & VovF & HG & HKC) -> -> ->.
rewrite Hsp' in VnF, VovF, HKC. rewrite Z.add_0_r in HG, HKC.
pose proof H6 as (HM & HRB & R18 & R20 & R25 & R27 & HC & HNB & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
pose proof HM as (HJ1 & Hfrs & _).
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 HX HJ1 Hfrs) as (HF4096 & HFceil & _).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WT : TSB_CH_STK = 4112) by reflexivity.
assert (HTB : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
pose proof HKC as (C1 & _).
assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) ->
  ~ (rbn_A X + 136 <= a < rbn_A X + 148) -> ~ (rbn_F X pos + 128 <= a < rbn_F X pos + 152) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2 H3. apply C1; [exact Ha | exact H1 | cbv beta; lia]. }
assert (KK : forall r, In r rbn6_keep -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (KK1 r Hr). apply HK2.
  - unfold rbn6_keep in Hr. cbn [In] in Hr. lia.
  - unfold rbn6_keep in Hr. unfold rbn_cl3, rbn_clc. cbn [In app] in Hr |- *. lia. }
pose proof (rbn6_kg regs2 regs1 rbn6_keep KK) as KG.
exists pos, regs2, lyc2, Sc2, mem2, md2. split.
{ unfold rbn_cfg. reflexivity. }
unfold rbn_st7. split.
{ apply (rbn6_mid_call X pos lyc1 Sc1 lyc2 Sc2 W1 W2 memc1 mdc1 mem2 md2 _ _ HX HM HJ2 Hfr2 Hbl2 Hro2 HKC);
  [cbv beta; intros a [Ha | Ha]; [left | right]; lia | rewrite rbn6_sh_len; lia]. }
split.
{ unfold rbn_rbase.
  split; [rewrite KG by reflexivity; exact B2|]. split; [rewrite KG by reflexivity; exact B3|].
  split; [rewrite KG by reflexivity; exact B4|]. split; [rewrite KG by reflexivity; exact B8|].
  split; [rewrite KG by reflexivity; exact B9|]. split; [rewrite KG by reflexivity; exact B19|].
  split; [rewrite KG by reflexivity; exact B22|]. rewrite KG by reflexivity; exact B23. }
split; [rewrite KG by reflexivity; exact R18|]. split; [rewrite KG by reflexivity; exact R25|].
split; [rewrite KG by reflexivity; exact R27|].
split.
{ rewrite !app_assoc in HC. rewrite !app_assoc.
  apply rbn6_cells_app in HC as [Clo Crt].
  apply rbn6_cells_app. split.
  - apply (rbn6_cells_kept (w_H W1) (w_H W2) memc1 mem2); [|exact Clo].
    intros a n v k Hin Hk. pose proof (rbn6_locs_rng X pos _ _ _ _ a n v Hin) as Hr. apply HAV; lia.
  - unfold rbn_rt in Crt |- *. cbn [rbn_cells] in Crt |- *. destruct Crt as (T1 & T2 & _ & _ & _).
    split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 mem2); [intros k Hk; apply HAV; lia | exact T1]|].
    split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 mem2); [intros k Hk; apply HAV; lia | exact T2]|].
    split; [replace (rbn_A X + 136) with (rbn_A X + 120 + 16) by lia; exact VnF|].
    split; [replace (rbn_A X + 144) with (rbn_A X + 120 + 24) by lia; exact VovF|]. exact I. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HNB|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HAV; lia. }
split; [exact HG | exact HA].
Qed.
Hypothesis L3F : rbn_L3_fits B.
Hypothesis L3O : rbn_L3_ovf B.
Theorem rbn_seg6 : rbn_seg6_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H6.
pose proof H6 as (HM & HRB & R18 & R20 & R25 & R27 & HC & HNB & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
pose proof HM as (HJ1 & Hfrs & _ & Hro1 & _).
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 HX HJ1 Hfrs) as (HF4096 & HFceil & HFal & HFapp & HFoff & HFpr).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WT : TSB_CH_STK = 4112) by reflexivity.
pose proof (rbn6_NB_ne X) as Hne.
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
pose proof HC as HC0.
apply rbn6_cells_app in HC0 as [_ HC0]. apply rbn6_cells_app in HC0 as [_ HC0].
apply rbn6_cells_app in HC0 as [Crn Crt].
pose proof Crn as Crn0. unfold rbn_rn in Crn0. cbn [rbn_cells] in Crn0. destruct Crn0 as (_ & _ & Vn & _).
destruct (proj1 (garr8_app SEGS _ _ _ _) HNB) as [HNBg _].
pose proof (garr8_bytes_ok SEGS _ _ _ HNBg) as Hby.
pose proof (rbn6_fra X pos lyc1 Sc1 W1 memc1 mdc1 _ 8 3 HX HM ltac:(lia) ltac:(lia)
  ltac:(rewrite rbn6_sh_len; lia)
  ltac:(intros i Hi; assert (i = 8 \/ i = 9 \/ i = 10) as [-> | [-> | ->]] by lia; reflexivity)) as Hra64.
assert (Hsrc : rbn_lsrc W1 memc1 (rbn_F X pos + 64) (rbm_NB X)).
{ split; [exact HNBg|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply (range_addressable_sub _ _ (rbn_F X pos + 8 * 8) (8 * 3)); [exact Hra64 | lia | lia]. }
pose proof (rbn6_lbuf X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as Hbuf0.
pose proof (rbn6_lrec X pos lyc1 Sc1 W1 memc1 mdc1 _ HX HM Crt) as Hrec0.
assert (HA9 : 2 ^ 46 <= rbn_A X <= 2 ^ 47) by lia.
pose proof (rbn6_entry (ri_fq X) W1 regs1 memc1 (rbn_A X) (Z.of_nat (length (rbm_NB X))) B9 HA9 AR7
  ltac:(lia) Vn) as HS.
unfold rbn_cfg.
replace (BASE + AF_both3_reac_box_name + RBN_P6) with (BASE + ss_pc ss_rbn6)
  by (unfold ss_rbn6, AF_both3_reac_box_name, RBN_P6; cbn [ss_pc]; lia).
rbn6_runh 0x3b14 Hrun.
apply (rbn6_run (ri_fq X) W1 regs1 memc1 mdc1 _ 0x3b14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 HS Hrun I eq_refl).
intros regs' mat' HR KP HJ'.
cbn [ss_pc].
replace (BASE + 15124) with (BASE + AF_both3_reac_box_name + RBN_L3) by (unfold AF_both3_reac_box_name, RBN_L3; lia).
assert (KK1 : forall r, In r rbn6_keep -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply KP; vm_compute; reflexivity|]). destruct Hr. }
pose proof (rbn6_kg regs' regs1 rbn6_keep KK1) as KG1.
assert (G2 : getr regs' 2 = w64 (rbn_A X)) by (rewrite KG1 by reflexivity; exact B2).
assert (Hsp' : spZ regs' = rbn_A X) by (unfold spZ; rewrite G2; apply unsigned_lit_small; lia).
rbn6_rget HR (21%bv : bv 5) G21. rbn6_rget HR (24%bv : bv 5) G24. rbn6_rget HR (26%bv : bv 5) G26.
rewrite rbn6_lit in G21, G24, G26 by lia.
assert (Hlcx : rbn_lcx B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) (ri_k X) regs').
{ split; [exact HJ'|]. split; [exact Hro1|].
  split; [rewrite KG1 by reflexivity; exact B3|]. split; [rewrite KG1 by reflexivity; exact B4|].
  split; [rewrite !KG1 by reflexivity; rewrite B9, B2; reflexivity|].
  split; [rewrite KG1 by reflexivity; exact B22|].
  rewrite Hsp'. lia. }
assert (Hrec : rbn_lrec B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  memc1 (spZ regs') (spZ regs' + 120) (rbn_F X pos + 128) 24 0 0) by (rewrite Hsp'; exact Hrec0).
assert (Hbuf : rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  memc1 (spZ regs') (spZ regs' + 120) (rbn_F X pos + 128) 24) by (rewrite Hsp'; exact Hbuf0).
assert (Hsep : rbn_lsep (spZ regs') (spZ regs' + 120) (rbn_F X pos + 128) 24 (rbn_F X pos + 64)
  (Z.of_nat (length (rbm_NB X)))) by (rewrite Hsp'; unfold rbn_lsep; lia).
assert (P9 : rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) <= spZ regs' + 152 \/
  spZ regs' + 180 <= rbn_F X pos + 64) by lia.
assert (P10 : rbn_F X pos + 128 + 24 <= spZ regs' + 152 \/ spZ regs' + 180 <= rbn_F X pos + 128) by lia.
assert (Vsp : val_mem SEGS (mrestrict (w_H W1) memc1) (spZ regs' + 168) 8 (Z.of_nat (length (rbm_NB X))))
  by (rewrite Hsp'; exact Vn).
assert (G20 : getr regs' 20 = w64 24) by (rewrite KG1 by reflexivity; exact R20).
assert (G27 : getr regs' 27 = w64 (rbn_F X pos + 64)) by (rewrite KG1 by reflexivity; exact R27).
destruct (Z_le_gt_dec (Z.of_nat (length (bn_TK (rbm_NB X)))) 23) as [Hf | Ho].
- pose proof (L3F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) (ri_k X) regs'
    (rbn_F X pos + 64) (rbn_F X pos + 128) (rbm_NB X) Hf
    Hlcx Hrec Hbuf Hne HNB23 Hby Hsrc Hsep P9 P10 Vsp G20 G21 G24 G26 G27) as R.
  eapply SRr_mono; [exact R|].
  intros W2 c2 _ Hp. apply (rbn6_tail X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' _ _ _ W2 c2 HX H6 KK1 Hsp' Hp).
  + unfold rbm_TB. rewrite firstn_all2 by lia. reflexivity.
  + unfold rbm_ovf. replace (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))) with false
      by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + unfold rbm_TB. rewrite firstn_all2 by lia. reflexivity.
- pose proof (L3O (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) (ri_k X) regs'
    (rbn_F X pos + 64) (rbn_F X pos + 128) (rbm_NB X) ltac:(lia)
    Hlcx Hrec Hbuf Hne HNB23 Hby Hsrc Hsep P9 P10 Vsp G20 G21 G24 G26 G27) as R.
  eapply SRr_mono; [exact R|].
  intros W2 c2 _ Hp. apply (rbn6_tail X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' _ _ _ W2 c2 HX H6 KK1 Hsp' Hp).
  + unfold rbm_TB. rewrite firstn_length_le by lia. reflexivity.
  + unfold rbm_ovf. replace (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))) with true
      by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  + reflexivity.
Qed.
End h.
End f.
End d.
