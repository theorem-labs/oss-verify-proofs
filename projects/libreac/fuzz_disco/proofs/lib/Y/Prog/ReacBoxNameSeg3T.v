(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 974 of its 1101 lines of code are new or changed and 964 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1h YC81 YC45 YC85 YCkd YC1i YCbf YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC88 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameSeg3D.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma rbn3t_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.

Lemma rbn3t_sh_nth : forall j, j <> 4%nat ->
  nth j (rbn_sh true false false false) 0 = nth j (rbn_sh false false false false) 0.
Proof. intros j Hj. destruct j as [|[|[|[|[|j]]]]]; try reflexivity. lia. Qed.

Lemma rbn3t_dec2 : forall v, bn_ok v = true ->
  sb_dec_c.sb_dec_D v 2 = bn_dec v 2 /\ length (sb_dec_c.sb_dec_D v 2) = 2%nat.
Proof.
intros v Hv. apply bn_ok_in in Hv. vm_compute in Hv.
repeat (destruct Hv as [<- | Hv]; [vm_compute; split; reflexivity|]). destruct Hv.
Qed.

Lemma rbn3t_room : forall n, n = 0 \/ n = 2 -> sb_dec_c.sb_dec_room 5 n = 4 - n.
Proof. intros n [-> | ->]; reflexivity. Qed.

Lemma rbn3t_acc : forall v n, bn_ok v = true -> (n = 0 \/ n = 2) ->
  sb_dec_c.sb_dec_acc v 2 5 n = 2 /\ 0 < sb_dec_c.sb_dec_room 5 n /\
  (if sb_dec_c.sb_dec_room 5 n <? Z.of_nat (length (sb_dec_c.sb_dec_D v 2)) then 1 else 0) = 0.
Proof.
intros v n Hv Hn. destruct (rbn3t_dec2 v Hv) as (HD & HDl).
unfold sb_dec_c.sb_dec_acc. rewrite HDl. rewrite (rbn3t_room n Hn).
destruct Hn as [-> | ->]; (split; [reflexivity|]); (split; [lia|]); reflexivity.
Qed.

Lemma rbn3t_fst : forall v n, bn_ok v = true -> (n = 0 \/ n = 2) ->
  firstn (Z.to_nat (sb_dec_c.sb_dec_acc v 2 5 n)) (sb_dec_c.sb_dec_D v 2) = bn_dec v 2.
Proof.
intros v n Hv Hn. destruct (rbn3t_acc v n Hv Hn) as (Ha & _ & _). destruct (rbn3t_dec2 v Hv) as (HD & HDl).
rewrite Ha. rewrite firstn_all2 by (rewrite HDl; lia). exact HD.
Qed.

Lemma rbn3t_regs_pres : forall (regsT regs2 : bvmap 5 word), aregs_preserved regsT regs2 ->
  getr regs2 2 = getr regsT 2 /\ getr regs2 3 = getr regsT 3 /\ getr regs2 4 = getr regsT 4 /\
  getr regs2 8 = getr regsT 8 /\ getr regs2 9 = getr regsT 9 /\ getr regs2 18 = getr regsT 18 /\
  getr regs2 19 = getr regsT 19 /\ getr regs2 20 = getr regsT 20 /\ getr regs2 21 = getr regsT 21 /\
  getr regs2 22 = getr regsT 22 /\ getr regs2 23 = getr regsT 23 /\ getr regs2 25 = getr regsT 25.
Proof.
intros regsT regs2 HP.
split; [exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 3 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 4 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 8 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 9 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 18 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 19 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 20 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 21 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 22 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 23 ltac:(unfold acallee_saved; lia))|].
exact (HP 25 ltac:(unfold acallee_saved; lia)).
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn3t_ok_rng : forall X, rbm_args X -> 0 <= ri_i X <= 40 /\ 0 <= ri_o X <= 40 /\
  bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
assert (Hb : forall x, bn_ok x = true -> 0 <= x <= 40)
  by (intros x Hx; apply bn_ok_in in Hx; vm_compute in Hx;
      repeat (destruct Hx as [<- | Hx]; [lia|]); destruct Hx).
split; [exact (Hb _ Hi)|]. split; [exact (Hb _ Ho)|]. split; [exact Hi | exact Ho].
Qed.

Lemma rbn3t_w4_eq : forall X, rbm_args X ->
  rbm_w4 X = bn_dec (ri_i X) 2 ++ bn_dec (ri_o X) 2.
Proof. intros X HA. reflexivity. Qed.

Lemma rbn3t_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|]. rewrite IH. tauto.
Qed.

Lemma rbn3t_argc_rng : forall X a n v, In (a, n, v) (rbn_argc X) ->
  rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64.
Proof.
intros X a n v H. unfold rbn_argc in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.


Lemma rbn3t_aview_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hm. apply aview_eq_of. apply Hm. Qed.
Lemma rbn3t_apresent_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hm (Ha & b & Hb). split; [exact Ha|]. exists b.
pose proof (Hm (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Ha in Hx. rewrite Hx. exact Hb.
Qed.
Lemma rbn3t_val_mem_mr : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hm Hv k Hk. unfold mbyte. rewrite Hm. exact (Hv k Hk).
Qed.
Definition rbn3t_cA (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  rbn_argc X ++ [(rbn_A X + 184, 8%nat, rbn_F X pos + 32); (rbn_A X + 192, 8%nat, 5)].
Lemma rbn3t_cA_rng : forall X pos a n v, In (a, n, v) (rbn3t_cA X pos) ->
  rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 200.
Proof.
intros X pos a n v H. unfold rbn3t_cA in H. apply in_app_iff in H. destruct H as [H | H].
- pose proof (rbn3t_argc_rng X a n v H). lia.
- cbn [In] in H. repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.

Lemma rbn3t_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.

Lemma rbn3t_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.

Lemma rbn3t_val_mem_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
rewrite Z.shiftr_0_l, Z.mod_0_l by (vm_compute; discriminate). lia.
Qed.

Lemma rbn3t_buf_ra : forall (W : world SEGS) memc F n k,
  F mod 8 = 0 -> 0 <= n -> 0 <= k -> n + k <= 5 ->
  aview SEGS (w_H W) memc (SHADOW_OFF + F / 8 + 4) = Some 5 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (F + 32 + n) k.
Proof.
intros W memc F n k HF8 Hn Hk Hnk Hsh x Hx. exists 5.
assert (Hx8 : x / 8 = F / 8 + 4).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
  symmetry. apply (Z.div_unique x 8 (F / 8 + 4) (x - F - 32)); lia. }
unfold shadow_of_addr. rewrite Hx8.
replace (SHADOW_OFF + (F / 8 + 4)) with (SHADOW_OFF + F / 8 + 4) by lia.
split; [exact Hsh|]. right.
assert (Hxm : x mod 8 = x - F - 32).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
  rewrite (Z.mod_eq x 8) by lia. rewrite Hx8. lia. }
rewrite Hxm. lia.
Qed.

Lemma rbn3t_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
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

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis HSBDEC : tsb_dec_spec B.

Lemma rbn3t_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.

Lemma rbn3t_faj : forall X own lyc Sc W m md c p,
  rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    own lyc Sc W m md (ri_k X) ->
  frame_addr lyc c p = frame_addr (ri_lyc X) c p.
Proof.
intros X own lyc Sc W m md c p HX HJ.
destruct HX as ((_ & L0 & _) & _).
destruct HJ as (_ & L1 & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.

Lemma rbn3t_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_A X mod 32 = 0 /\ rbn_SP X + 16 <= 2 ^ 47 /\
  ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  ly_stk_lo (ri_ly X) + ri_STK X <= ri_sp0 X /\ ri_sp0 X <= ly_stk_hi (ri_ly X) /\ rbn_SP X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
rewrite WS in Hstk. unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
repeat split; lia.
Qed.

Lemma rbn3t_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn3t_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
Qed.

Lemma rbn3t_stk_shadow : forall lyc Sc W mem md a n,
  AR SEGS B lyc Sc W mem md ->
  ly_stk_lo lyc + 64 <= a -> a + n + 64 <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros lyc Sc W mem md a n HAR H1 H2 Hn.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & HPlo & HPhi & _).
unfold page_aligned in HPlo, HPhi.
assert (Hz : forall x, ly_stk_lo lyc <= x < ly_stk_hi lyc -> aview SEGS (w_H W) mem (shadow_addr x) = Some 0).
{ intros x Hx.
  pose proof (HZ (x / 8 - ly_stk_lo lyc / 8) ltac:(lia)) as E.
  unfold shadow_of_addr in E. unfold shadow_addr.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
  exact E. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply Hz. lia.
- intros s Hs.
  assert (Hx : shadow_addr (8 * (s - SHADOW_OFF)) = s) by (unfold shadow_addr; lia).
  rewrite <- Hx. rewrite Hz; [discriminate|]. unfold shadow_addr in Hs. lia.
Qed.

Lemma rbn3t_frame_img : forall ly S (W : world SEGS) mem md cid p a n,
  AR SEGS B ly S W mem md -> In (cid, p) (frames S) ->
  frame_addr ly cid p <= a -> a + n <= frame_addr ly cid p + fs_frame_bytes cid -> 0 < n ->
  a + n <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
intros ly S W mem md cid p a n HAR Hin H1 H2 Hn.
assert (HIT : YImgTop.IMG_LO < YImgTop.IMG_TOP) by (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; lia).
destruct (Z_le_gt_dec (a + n) YImgTop.IMG_LO) as [Hle | Hgt]; [left; exact Hle|].
destruct (Z_le_gt_dec YImgTop.IMG_TOP a) as [Hge | Hlt]; [right; exact Hge|].
exfalso.
assert (Hex : exists x, YImgTop.IMG_LO <= x < YImgTop.IMG_TOP /\
   frame_addr ly cid p <= x < frame_addr ly cid p + fs_frame_bytes cid).
{ destruct (Z_le_gt_dec YImgTop.IMG_LO a) as [Ha | Ha].
  - exists a. split; lia.
  - exists YImgTop.IMG_LO. split; lia. }
destruct Hex as (x & Hx1 & Hx2).
destruct (al_client_img _ _ LAWS ly S W mem md x HAR
  (or_intror (or_introl (ex_intro _ cid (ex_intro _ p (conj Hin Hx2)))))) as (Himg & _).
apply Himg. destruct (pa_img_cover ly S md (proj1 (proj2 HAR))) as (Hc1 & Hc2).
unfold in_zr. lia.
Qed.

Definition ERB3 (regs : bvmap 5 word) (i o : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [i; o])).
Definition rbn3t_regions (X : rbn_in) (pos : Z) : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 40 0 40 [];
    YP09.mkRegion (Some 9%nat) 40 57 40 40
      [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 9%nat) 184 200 184 200 [];
    YP09.mkRegion (Some 18%nat) 4 5 4 5 [] ].
Definition ss_rbn3t (X : rbn_in) (pos : Z) : sstate :=
  mkSS 14612 sr_atoms (rbn3t_regions X pos) None (mkFacts [] [] []).

Lemma rbn3t_entry : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P,
  rbn_cx B X -> rbn3_stT B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  st_ok_pi SEGS VAL (ERB3 regs1 (ri_i X) (ri_o X)) (ss_rbn3t X pos)
    (restrict (w_H W1) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + 14612)) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX HS3.
destruct (rbn3t_A_rng X HX) as (AR0 & AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof HS3 as (HM & HRB & R18 & R25 & R21 & R24 & R26 & R14 & R15 & HC & HPok & HA).
destruct (rbn3t_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
destruct (rbn3t_ok_rng X HA) as (Hi40 & Ho40 & _ & _).
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & HK & HFr1 & HFL1 & HSh1).
pose proof (proj1 HJ1) as HAR1.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
pose proof (rbn3t_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM 3 pos) as FA.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & _ & HFpres & HSHpres).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite FA in HFpres, HSHpres. rewrite Hfb3 in HFpres, HSHpres.
fold (rbn_F X pos) in HFpres, HSHpres. fold (rbn_SH X pos) in HSHpres.
change (512 / 8) with 64 in HSHpres.
pose proof HRB as (RB2 & RB3 & RB4 & RB8 & RB9 & RB19 & RB22 & RB23).
rewrite restrict_mkst_fx.
set (E := ERB3 regs1 (ri_i X) (ri_o X)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (B9 : bv_unsigned (ew E 9%nat) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), RB9; apply unsigned_lit_small; lia).
assert (HSHlo : kLowMemEnd <= rbn_SH X pos).
{ unfold rbn_SH, shadow_addr.
  pose proof (Z.div_pos (rbn_F X pos) 8 ltac:(lia) ltac:(lia)) as Hd1.
  unfold SHADOW_OFF, kLowMemEnd in *. lia. }
assert (HSHhi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
assert (B18 : bv_unsigned (ew E 18%nat) = rbn_SH X pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32%nat = Z_to_bv 64 (ri_i X))
  by (subst E; unfold ERB3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33%nat = Z_to_bv 64 (ri_o X))
  by (subst E; unfold ERB3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
pose proof (rbn3t_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as FAg.
unfold ss_rbn3t, rbn3t_regions. apply pa_entry_st_ok_full.
- subst E. unfold ERB3. apply (regs_ok_agree 32 (Ereg regs1 (map (Z_to_bv 64) [ri_i X; ri_o X]))).
  + split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  + vm_compute. reflexivity.
  + apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  + rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply K6. lia.
  + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ (rbn_A X) 40 8 _ (ri_i X));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact (proj1 HC).
    * apply (chunk_ok_val SEGS E _ (rbn_A X) 48 8 _ (ri_o X));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact (proj1 (proj2 HC)).
  + rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply K6. lia.
  + rewrite B18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HSHpres o ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite B9, B18.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; exact I.
Qed.

Lemma rbn3t_sbd : forall (fq : YK11.FPState) X pos own lyc Sc (W : world SEGS) memc mdc regs v n,
  fq = ri_fq X ->
  rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    own lyc Sc W memc mdc (ri_k X) ->
  own = (3, pos) :: ri_own X ->
  frames Sc = (3, pos) :: frames (ri_Sc X) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs = rbn_A X ->
  getr regs 10 = w64 (rbn_A X + 184) -> getr regs 11 = w64 v -> getr regs 12 = w64 2 ->
  bn_ok v = true -> (n = 0 \/ n = 2) ->
  val_mem SEGS (mrestrict (w_H W) memc) (rbn_A X + 184) 8 (rbn_F X pos + 32) ->
  val_mem SEGS (mrestrict (w_H W) memc) (rbn_A X + 192) 8 5 ->
  val_mem SEGS (mrestrict (w_H W) memc) (rbn_A X + 200) 8 n ->
  val_mem SEGS (mrestrict (w_H W) memc) (rbn_A X + 208) 4 0 ->
  aview SEGS (w_H W) memc (rbn_SH X pos + 4) = Some 5 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_dec) regs memc mdc)
    (tsb_dec_post B fq (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
       own lyc Sc W memc (ri_k X) regs (rbn_A X + 184) v 2 (rbn_F X pos + 32) 5 n 0).
Proof.
intros fq X pos own lyc Sc W memc mdc regs v n Hfq HX HJ Hown Hfrs Hro Hra Hra4 Hgp Htp Hsp
  R10 R11 R12 Hbv Hn Vp Vcap Vn Vov Vsh.
subst fq.
destruct (rbn3t_A_rng X HX) as (AR0 & AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (rbn3t_faj X own lyc Sc W memc mdc 3 pos HX HJ) as FA.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin3) as (HF4096 & HFceil & HFapp0).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR Hin3) as (HFal & HFapp & HFpr & HFsh).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite FA in HF4096, HFceil, HFapp0, HFal, HFapp, HFpr, HFsh.
rewrite Hfb3 in HFceil, HFapp0, HFapp, HFsh.
fold (rbn_F X pos) in HF4096, HFceil, HFapp0, HFal, HFapp, HFpr.
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (HFlo : rbn_F X pos + 512 <= rbn_A X).
{ pose proof (shadow_addr_bounds (rbn_F X pos) ltac:(lia)). lia. }
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HSBS : SB_DEC_STK = 4256) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlen : Z.of_nat (length (frames Sc)) <= 9)
  by (rewrite Hfrs; cbn [length]; destruct HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrl & _); lia).
assert (Hamr : amem_range (rbn_A X + 184) 28).
{ unfold amem_range, kHighMemBeg, kHighMemEnd. right. split; lia. }
assert (HoffA : off_img (rbn_A X + 184) 28)
  by (unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia).
assert (Hvrng : 0 <= v < 2 ^ 31).
{ apply bn_ok_in in Hbv. vm_compute in Hbv.
  repeat (destruct Hbv as [<- | Hbv]; [lia|]). destruct Hbv. }
destruct (rbn3t_acc v n Hbv Hn) as (Hacc & Hroom & Hovf).
destruct (rbn3t_dec2 v Hbv) as (HDeq & HDlen).
assert (HARstk : AR SEGS B lyc Sc W memc mdc) by exact HAR.
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
apply (HSBDEC (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X)
    (ri_md0 X) own lyc Sc W memc mdc (ri_k X) regs [] (rbn_A X + 184) v 2 (rbn_F X pos + 32) 5 n 0 HJ Hro
    Hra Hra4 Hgp Htp R10 R11 R12).
  - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Hsp. pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D16. rewrite AR3, Z.add_0_r in D16.
    rewrite D16. replace (32 * (rbn_A X / 32)) with ((2 * (rbn_A X / 32)) * 16) by lia. apply Z_mod_mult.
  - rewrite Hsp, HSBS. lia.
  - rewrite Hsp. lia.
  - exact Hlen.
  - exact Hvrng.
  - right. reflexivity.
  - lia.
  - pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D. rewrite AR3, Z.add_0_r in D.
    replace (rbn_A X + 184) with ((4 * (rbn_A X / 32) + 23) * 8) by lia. apply Z_mod_mult.
  - lia.
  - exact Hamr.
  - exact HoffA.
  - rewrite Hsp. left. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Vp.
  - replace (rbn_A X + 184 + 8) with (rbn_A X + 192) by lia. exact Vcap.
  - replace (rbn_A X + 184 + 16) with (rbn_A X + 200) by lia. exact Vn.
  - replace (rbn_A X + 184 + 24) with (rbn_A X + 208) by lia. exact Vov.
  - exact (proj1 (rbn3t_stk_shadow lyc Sc W memc mdc (rbn_A X + 184) 28 HARstk
      ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia))).
  - exact (proj2 (rbn3t_stk_shadow lyc Sc W memc mdc (rbn_A X + 184) 28 HARstk
      ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia))).
  - intros a Ha. split.
    + left. lia.
    + apply Hpres. lia.
  - intros _. rewrite Hacc.
    split; [lia|]. split; [lia|].
    split.
    { destruct HFapp0 as [HF0 [HFL | [HFH1 HFH2]]].
      - left. unfold amem_range, kLowShadowBeg, kLowMemEnd in *. lia.
      - right. unfold amem_range, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
    split.
    { replace (rbn_F X pos + 32 + n + 2) with ((rbn_F X pos + 32 + n) + 2) by lia.
      exact (rbn3t_frame_img lyc Sc W memc mdc 3 pos (rbn_F X pos + 32 + n) 2 HAR Hin3
        ltac:(rewrite FA; fold (rbn_F X pos); lia) ltac:(rewrite FA, Hfb3; fold (rbn_F X pos); lia) ltac:(lia)). }
    split; [left; lia|].
    split; [rewrite Hsp, HSBS; right; lia|].
    split.
    { apply (rbn3t_buf_ra W memc (rbn_F X pos) n 2 HF8 ltac:(lia) ltac:(lia) ltac:(lia)). exact Vsh. }
    split.
    { exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc 3 pos (rbn_F X pos + 32 + n) 2 HAR Hin3
        ltac:(rewrite FA; fold (rbn_F X pos); lia) ltac:(rewrite FA, Hfb3; fold (rbn_F X pos); lia) ltac:(lia)). }
    intros a Ha. split.
    + right. right. right. exists 3, pos. split; [rewrite Hown; left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite FA, Hfb3. fold (rbn_F X pos). lia.
    + exact (proj1 (HFpr a ltac:(lia))).
Qed.
Lemma rbn3t_rod : forall (W W' : world SEGS) (m m' : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' Hro Hk a Hin Ho He.
assert (Hia : in_img SEGS a).
{ destruct Hin as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]. }
rewrite (Hk a Hia Ho He). exact (Hro a Hin Ho He).
Qed.
Lemma rbn3t_mid_fw : forall X pos lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem2 md2 sh0 sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh0 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem2 md2 (ri_k X) ->
  frames Sc2 = frames Sc1 -> Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) ->
  Z.of_nat (length sh) <= 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 4256 <= a < rbn_A X + 216) ->
     ~ (rbn_F X pos <= a < rbn_F X pos + 512) -> ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - 4256 <= a < rbn_A X) ->
     apresent (w_H W1) memc1 a -> apresent (w_H W2) mem2 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_frame X (mrestrict (w_H W2) mem2) ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (rbn_F X pos + 504) 8 (rbn_FL X pos) ->
  rbn_shadow_at W2 mem2 (rbn_SH X pos) sh ->
  rbn_mid B X pos lyc2 Sc2 W2 mem2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem2 md2 sh0 sh HX HM HJ2 Hfr2 Hperm2 Hro2 Hshlen
  HEQ HPR HIMG Hframe Hflag Hshadow.
pose proof (rbn3t_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as FA.
destruct (rbn3t_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn3t_A_rng X HX) as (AR0 & AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HFsh_lo : kLowMemEnd <= rbn_SH X pos).
{ unfold rbn_SH, shadow_addr. pose proof (Z.div_pos (rbn_F X pos) 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kLowMemEnd in *. lia. }
assert (HFsh_hi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & HFr & HFl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|].
split; [etransitivity; [exact Hperm2 | exact Hperm]|]. split; [exact Hro2|].
split.
{ destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold rbn_kept.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' _. rewrite (HEQ a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    exact (K1 a Ha Hn' ltac:(intros [])).
  - intros b m j Hb Hj _.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & [Hbz0 Hbz1] & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite (HEQ (b + j) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *; lia)).
    exact (K2 b m j Hb Hj ltac:(intros [])).
  - intros a Hia Ho He. rewrite (HIMG a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
    rewrite FA in Hc4096, Hcceil, Hcapp.
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct (in_split _ _ Hcp) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, Hfb3, FA in Hd.
    destruct Ha as [Ha | Ha].
    + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
      rewrite (HEQ a ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(destruct Hcapp as [_ [HcL | [HcH1 HcH2]]];
              unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *; lia)).
      exact (K4 cid p a Hcp (or_introl Ha) He).
    + unfold in_zr in Ha. cbn [fst snd] in Ha.
      pose proof (rbn3t_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
      pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as HSe. change (512 / 8) with 64 in HSe.
      pose proof (shadow_mono (rbn_F X pos + 512) (frame_addr (ri_lyc X) cid p)) as HSm1.
      pose proof (shadow_mono (frame_addr (ri_lyc X) cid p + fs_frame_bytes cid) (rbn_F X pos)) as HSm2.
      pose proof (shadow_range_end (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid) Hcnn) as HSe2.
      rewrite (HEQ a ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)
        ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)
        ltac:(destruct (HFapp) as [HF0 [HFL | [HFH1 HFH2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)
        ltac:(unfold rbn_SH in *; destruct Hd as [Hd | Hd]; lia)).
      exact (K4 cid p a Hcp (or_intror Ha) He).
  - intros a Ha Hn' Hp. apply HPR; [lia | lia | exact (K5 a Ha Hn' Hp)].
  - intros a Ha. apply Hpres2. lia. }
split; [exact Hframe|]. split; [exact Hflag | exact Hshadow].
Qed.
Lemma rbn3t_mid_same : forall X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) ->
  (forall x, mrestrict (w_H W1) memc3 x = mrestrict (w_H W1) memc2 x) ->
  rbn_mid B X pos lyc1 Sc1 W1 memc3 mdc3 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh
  (HJ & Hfr & Hp & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & HFr & HFL & HSh) HJ3 Hm.
assert (Hv : forall a, aview SEGS (w_H W1) memc3 a = aview SEGS (w_H W1) memc2 a)
  by (intros a; apply rbn3t_aview_mr; exact Hm).
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hp|].
split; [intros a H1 H2 H3; rewrite Hv; exact (Hro a H1 H2 H3)|].
split.
{ split; [intros a H1 H2 H3; rewrite Hv; exact (K1 a H1 H2 H3)|].
  split; [intros b m j H1 H2 H3; rewrite Hv; exact (K2 b m j H1 H2 H3)|].
  split; [intros a H1 H2 H3; rewrite Hv; exact (K3 a H1 H2 H3)|].
  split; [intros cid p a H1 H2 H3; rewrite Hv; exact (K4 cid p a H1 H2 H3)|].
  split; [intros a H1 H2 H3; apply (rbn3t_apresent_mr _ memc2 memc3 a Hm); exact (K5 a H1 H2 H3)|].
  intros a H1. apply (rbn3t_apresent_mr _ memc2 memc3 a Hm). exact (K6 a H1). }
split; [intros j r Hj; apply (rbn3t_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact (HFr j r Hj)|].
split; [apply (rbn3t_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact HFL|].
intros j Hj. rewrite Hv. exact (HSh j Hj).
Qed.
Lemma rbn3t_mid_sb : forall X pos lyc1 Sc1 W1 m1 md1 ly2 S2 W2 m2 md2 sh sp A (Ex : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m1 md1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) ly2 S2 W2 m2 md2 (ri_k X) ->
  frames S2 = frames Sc1 -> Permutation (ablocks B ly2 S2) (ablocks B lyc1 Sc1) ->
  Z.of_nat (length sh) <= 64 ->
  sp = rbn_A X -> A = rbn_A X + 184 ->
  (forall a, Ex a -> rbn_F X pos + 32 <= a < rbn_F X pos + 36) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - SB_DEC_STK <= a < sp) -> ~ (A + 16 <= a < A + 28) -> ~ Ex a ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  (forall b m i, In (b, m) (ablocks B lyc1 Sc1) -> 0 <= i < req_size m -> ~ (A + 16 <= b + i < A + 28) ->
     ~ Ex (b + i) -> aview SEGS (w_H W2) m2 (b + i) = aview SEGS (w_H W1) m1 (b + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  (forall cid p a, In (cid, p) (frames Sc1) ->
     (in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)) ->
     ~ (A + 16 <= a < A + 28) -> ~ Ex a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - SB_DEC_STK <= a < sp) ->
     apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
  rbn_mid B X pos ly2 S2 W2 m2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 m1 md1 ly2 S2 W2 m2 md2 sh sp A Ex HX HM HJ2 Hfr2 Hperm2 Hshlen Hsp HA HEx
  Q1 Q2 Q3 Q4 Q5.
subst sp A.
pose proof (rbn3t_fa X pos lyc1 Sc1 W1 m1 md1 _ _ HX HM) as FA.
destruct (rbn3t_F_facts X pos lyc1 Sc1 W1 m1 md1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn3t_A_rng X HX) as (AR0 & AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (HSBS : SB_DEC_STK = 4256) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HFsh_lo : kLowMemEnd <= rbn_SH X pos).
{ unfold rbn_SH, shadow_addr. pose proof (Z.div_pos (rbn_F X pos) 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kLowMemEnd in *. lia. }
assert (HFsh_hi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & HFr & HFl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HExF : forall a, Ex a -> rbn_F X pos <= a < rbn_F X pos + 512)
  by (intros a Ha; specialize (HEx a Ha); lia).
assert (Q1' : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hn. apply Q1; [lia | rewrite HSBS; lia | lia | intros Hx; specialize (HEx a Hx); lia]. }
assert (QF : forall a, rbn_F X pos <= a < rbn_F X pos + 512 \/ rbn_SH X pos <= a < rbn_SH X pos + 64 ->
  ~ Ex a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hne. apply (Q4 3 pos a Hin3).
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3, Hfb3;
      [lia | change (512 / 8) with 64; unfold rbn_SH in Ha; lia].
  - lia.
  - exact Hne. }
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|].
split; [etransitivity; [exact Hperm2 | exact Hperm]|].
split; [exact (rbn3t_rod W1 W2 m1 m2 Hro Q3)|].
split.
{ destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold rbn_kept.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' _. rewrite (Q1' a Ha Hn'). exact (K1 a Ha Hn' ltac:(intros [])).
  - intros b m j Hb Hj _.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite (Q2 b m j Hb1 Hj ltac:(lia) ltac:(intros Hx; specialize (HExF _ Hx); lia)).
    exact (K2 b m j Hb Hj ltac:(intros [])).
  - intros a Hia Ho He. rewrite (Q3 a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha _.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
    rewrite FA in Hc4096, Hcceil, Hcapp.
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct (in_split _ _ Hcp) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, Hfb3, FA in Hd.
    assert (Ha1 : in_zr a (frame_rng lyc1 (cid, p)) \/
      in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8))
      by (unfold frame_rng in *; cbn [fst snd] in *; rewrite !FA; exact Ha).
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
    destruct Ha as [Ha | Ha].
    + rewrite (Q4 cid p a Hcp1 Ha1 ltac:(lia) ltac:(intros Hx; specialize (HExF _ Hx); lia)).
      exact (K4 cid p a Hcp ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; exact Ha) ltac:(intros [])).
    + pose proof (rbn3t_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
      rewrite (Q4 cid p a Hcp1 Ha1 ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)
        ltac:(intros Hx; specialize (HExF _ Hx); destruct HFapp as [HF0 [HFL | [HFH1 HFH2]]];
              unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)).
      exact (K4 cid p a Hcp ltac:(right; unfold in_zr; cbn [fst snd]; exact Ha) ltac:(intros [])).
  - intros a Ha Hn' Hp. apply Q5; [lia | rewrite HSBS; lia | exact (K5 a Ha Hn' Hp)].
  - intros a Ha. apply Hpres2. lia. }
split.
{ intros j r Hj.
  assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some rbn_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HFr j r Hj)].
  intros k Hk. apply Q1; [lia | rewrite HSBS; lia | lia | intros Hx; specialize (HEx _ Hx); lia]. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact HFl].
  intros k Hk. apply QF; [lia | intros Hx; specialize (HEx _ Hx); lia]. }
intros j Hj. rewrite (QF (rbn_SH X pos + j) ltac:(lia)
  ltac:(intros Hx; specialize (HEx _ Hx); destruct HFapp as [HF0 [HFL | [HFH1 HFH2]]];
        unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *; lia)).
exact (Hsh0 j Hj).
Qed.
Theorem rbn3t_t : rbn3_t_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H3.
pose proof H3 as (HM & HRB & R18 & R25 & R21 & R24 & R26 & R14 & R15 & HC & HPok & HA).
pose proof (rbn3t_entry (ri_fq X) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H3) as HS.
destruct (rbn3t_A_rng X HX) as (AR0 & AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
destruct (rbn3t_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn3t_ok_rng X HA) as (Hi40 & Ho40 & Hbi & Hbo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (rbn3t_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as FA.
pose proof HM as (HJ1 & Hfrs1 & Hperm1 & Hro1 & HK1 & HFr1 & HFL1 & HSh1).
pose proof HRB as (RB2 & RB3 & RB4 & RB8 & RB9 & RB19 & RB22 & RB23).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & Hly1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk1 & _).
pose proof Hstk1 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HSHlo : kLowMemEnd <= rbn_SH X pos).
{ unfold rbn_SH, shadow_addr. pose proof (Z.div_pos (rbn_F X pos) 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kLowMemEnd in *. lia. }
assert (HSHhi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
pose proof pa_segs_low as Hsegs.
remember (ERB3 regs1 (ri_i X) (ri_o X)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (V9 : bv_unsigned (ew E 9%nat) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), RB9; apply unsigned_lit_small; lia).
assert (V18 : bv_unsigned (ew E 18%nat) = rbn_SH X pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32%nat = Z_to_bv 64 (ri_i X))
  by (subst E; unfold ERB3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33%nat = Z_to_bv 64 (ri_o X))
  by (subst E; unfold ERB3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
clear HE.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Rn & _ & Rnl & _ & Rt & _ & Rtl & _ & Rd & _ & Rdl & _ & _).
assert (U14 : bv_unsigned (ew E 14%nat) = ri_display X)
  by (rewrite (EE 14%nat 14%bv eq_refl), R14; unfold w64; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15%nat) = ri_display_len X)
  by (rewrite (EE 15%nat 15%bv eq_refl), R15; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21%nat) = ri_token X)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24%nat) = ri_name X)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26%nat) = ri_token_len X)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19%nat) = rbn_F X pos)
  by (rewrite (EE 19%nat 19%bv eq_refl), RB19; unfold w64; apply unsigned_lit_small; lia).
assert (HA16 : rbn_A X mod 16 = 0).
{ pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D. rewrite AR3, Z.add_0_r in D. rewrite D.
  replace (32 * (rbn_A X / 32)) with ((2 * (rbn_A X / 32)) * 16) by lia. apply Z_mod_mult. }
assert (HSBS : SB_DEC_STK = 4256) by reflexivity.
assert (HFapp' : rbn_F X pos + 512 <= kLowShadowBeg \/ kHighMemBeg <= rbn_F X pos)
  by (destruct HFapp as [_ [HL | [HH _]]]; [left | right]; lia).
destruct (rbn3t_acc (ri_i X) 0 Hbi (or_introl eq_refl)) as (Hacc1 & Hroom1 & Hovf1).
destruct (rbn3t_acc (ri_o X) 2 Hbo (or_intror eq_refl)) as (Hacc2 & Hroom2 & Hovf2).
destruct (rbn3t_dec2 (ri_i X) Hbi) as (HDi & HDil).
unfold rbn_cfg, cfg_at.
replace (BASE + AF_both3_reac_box_name + RBN_T3) with (BASE + 14612)
  by (unfold AF_both3_reac_box_name, RBN_T3; lia).
change (w64 (BASE + 14612)) with (Z_to_bv 64 (BASE + 14612)).
paj_run_shc RUNP RUNC HS HJ1.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X));
    [reflexivity | exact V9 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X));
    [reflexivity | exact V9 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; lia |].
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos));
    [reflexivity | exact V18 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
     exists 3, pos; split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
     rewrite (FA 3 pos); fold (rbn_F X pos); fold (rbn_SH X pos);
     change (fs_frame_bytes 3 / 8) with 64; lia |].
  apply awr_ok_nil. }
rename ms into msA. rename mat into matA. rename HF into HFA. rename HFr into HFrA. rename HG into HGA.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((rbn_A X <= a < rbn_A X + 40) \/ (rbn_A X + 184 <= a < rbn_A X + 200) \/
     (rbn_SH X pos + 4 <= a < rbn_SH X pos + 5)) ->
  aview SEGS (w_H W1) (ms_mem msA) a = aview SEGS (w_H W1) memc1 a).
{ apply (rbn3t_kept_frame E _ (w_H W1) memc1 (ms_mem msA)
    (fun a => (rbn_A X <= a < rbn_A X + 40) \/ (rbn_A X + 184 <= a < rbn_A X + 200) \/
       (rbn_SH X pos + 4 <= a < rbn_SH X pos + 5)) HFrA).
  intros a (r & Hr & Hw). unfold ss_rbn3t, rbn3t_regions in Hr. cbn [ss_mem In] in Hr.
  repeat (destruct Hr as [<- | Hr]); try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?V9, ?V18 in Hw; cbv beta; lia. }
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0.
pose proof (st_ok_region_nth _ _ _ 2%nat _ HS eq_refl) as HR2.
pose proof (st_ok_region_nth _ _ _ 3%nat _ HS eq_refl) as HR3.
cbn [ms_mem restrict] in HR0, HR2, HR3.
destruct HC as (C40 & C48 & C56 & _).
assert (HCA : rbn_cells (mrestrict (w_H W1) (ms_mem msA)) (rbn3t_cA X pos)).
{ unfold rbn3t_cA, rbn_argc. cbn [app rbn_cells].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 0 40 0 40 0 8%N (SOff 14 0) (ri_display X) HR0 V9);
    [cbn [In]; tauto | cbn [sv_denot]; rewrite U14, Z.add_0_r; reflexivity | zside | zside]|].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 0 40 0 40 8 8%N (SOff 24 0) (ri_name X) HR0 V9);
    [cbn [In]; tauto | cbn [sv_denot]; rewrite U24, Z.add_0_r; reflexivity | zside | zside]|].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 0 40 0 40 16 8%N (SOff 21 0) (ri_token X) HR0 V9);
    [cbn [In]; tauto | cbn [sv_denot]; rewrite U21, Z.add_0_r; reflexivity | zside | zside]|].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 0 40 0 40 24 8%N (SOff 26 0) (ri_token_len X) HR0 V9);
    [cbn [In]; tauto | cbn [sv_denot]; rewrite U26, Z.add_0_r; reflexivity | zside | zside]|].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 0 40 0 40 32 8%N (SOff 15 0) (ri_display_len X) HR0 V9);
    [cbn [In]; tauto | cbn [sv_denot]; rewrite U15, Z.add_0_r; reflexivity | zside | zside]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem msA)); [intros k Hk; apply KW1; lia | exact C40]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem msA)); [intros k Hk; apply KW1; lia | exact C48]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem msA)); [intros k Hk; apply KW1; lia | exact C56]|].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 184 200 184 200 184 8%N (SOff 19 32) (rbn_F X pos + 32) HR2 V9);
    [cbn [In]; tauto | cbn [sv_denot]; rewrite U19; reflexivity | zside | zside]|].
  split; [apply (field_of_region E _ 9%nat (rbn_A X) _ 184 200 184 200 192 8%N (SLit 5) 5 HR2 V9);
    [cbn [In]; tauto | reflexivity | zside | zside]|].
  exact I. }
assert (SH4 : aview SEGS (w_H W1) (ms_mem msA) (rbn_SH X pos + 4) = Some 5).
{ pose proof (field_of_region E _ 18%nat (rbn_SH X pos) _ 4 5 4 5 4 1%N (SLit 5) 5 HR3 V18
    ltac:(cbn [In]; tauto) eq_refl ltac:(zside) ltac:(zside)) as V0.
  pose proof (V0 0%nat ltac:(cbn; lia)) as V00. cbn [Z.of_nat] in V00. rewrite Z.add_0_r in V00.
  unfold aview. rewrite V00. reflexivity. }
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) (AMEMSET (ri_fq X)) W1 rT mT
    (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 dT (ri_k X) (rbn_A X + 200) 0 16 (rbn_A X - ri_sp0 X) _ HJ1) end.
  - rewrite Ra0, V9. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Rsp, (EE 2%nat 2%bv eq_refl), RB2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, HA16, Hsp0al. reflexivity.
  - lia.
  - lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact RB3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact RB4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [left; lia | lia].
  - unfold amem_range, kHighMemBeg, kHighMemEnd. right. lia.
  - exact (proj1 (rbn3t_stk_shadow lyc1 Sc1 W1 _ _ (rbn_A X + 200) 16 (proj1 HJ1)
      ltac:(rewrite Elo1; lia) ltac:(rewrite Ehi1; lia) ltac:(lia))).
  - intros _. exact (proj2 (rbn3t_stk_shadow lyc1 Sc1 W1 _ _ (rbn_A X + 200) 16 (proj1 HJ1)
      ltac:(rewrite Elo1; lia) ltac:(rewrite Ehi1; lia) ltac:(lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hfrm & Hpres2).
assert (KWM : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 4096 <= a < rbn_A X + 216) ->
  ~ (rbn_SH X pos + 4 <= a < rbn_SH X pos + 5) -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2. rewrite (Hfrm a Ha ltac:(lia) ltac:(lia)). apply KW1; [exact Ha | lia]. }
assert (HM2 : rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh true false false false)).
{ apply (rbn3t_mid_fw X pos lyc1 Sc1 W1 memc1 mdc1 lyc1 Sc1 W1 mem2 md2 _ _ HX HM HJ2 eq_refl (Permutation_refl _)).
  - apply (rbn3t_rod W1 W1 memc1 mem2 Hro1). intros a Hia Ho He. pose proof (Hsegs a Hia) as Hlow.
    apply KWM; lia.
  - rewrite rbn3t_sh_len. lia.
  - intros a Ha Hz1 Hz2 Hz3. apply KWM; [exact Ha | lia | lia].
  - intros a _ _ Hp. apply Hpres2. exact (apresent_grows _ _ _ _ HGA Hp).
  - intros a Hia Ho He. pose proof (Hsegs a Hia) as Hlow. apply KWM; lia.
  - intros j r Hj.
    assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some rbn_saved_regs j)); rewrite Hj; discriminate).
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact (HFr1 j r Hj)].
    intros k Hk. apply KWM; lia.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact HFL1].
    intros k Hk. apply KWM; [lia | lia | unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia].
  - intros j Hj. rewrite rbn3t_sh_len in Hj. destruct (Z.eq_dec j 4) as [-> | Hne].
    + rewrite (Hfrm (rbn_SH X pos + 4) ltac:(lia) ltac:(lia) ltac:(lia)). rewrite SH4. reflexivity.
    + rewrite (KWM (rbn_SH X pos + j) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (HSh1 j ltac:(rewrite rbn3t_sh_len; lia)). f_equal. symmetry. apply rbn3t_sh_nth. lia. }
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W1) mem2) HP2 [1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite V9; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply Hfrm; lia.
  - exfalso. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 34)%nat -> ew E2 n = ew E n)
  by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
clear HE2.
assert (W9 : bv_unsigned (ew E2 9%nat) = rbn_A X) by (rewrite OLD2 by lia; exact V9).
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
rename ms into msB. rename mat into matB. rename HF into HFB. rename HFr into HFrB. rename HG into HGB.
assert (Hm2 : forall x, mrestrict (w_H W1) (ms_mem msB) x = mrestrict (w_H W1) mem2 x).
{ intros x. apply HFrB. intros (r & Hr & Hw). cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
pose proof (rbn3t_mid_same X pos lyc1 Sc1 W1 mem2 md2 (ms_mem msB) _ _ HM2 HJ2 Hm2) as HM2b.
assert (HCB : rbn_cells (mrestrict (w_H W1) (ms_mem msB)) (rbn3t_cA X pos)).
{ apply (rbn3t_cells_kept (w_H W1) (w_H W1) (ms_mem msA) (ms_mem msB)); [|exact HCA].
  intros a n v k Hin Hk. pose proof (rbn3t_cA_rng X pos a n v Hin) as Hr.
  rewrite (rbn3t_aview_mr _ _ _ _ Hm2). apply Hfrm; lia. }
pose proof HCB as HCB'. unfold rbn3t_cA in HCB'. apply rbn3t_cells_app in HCB' as [_ HCBr].
cbn [rbn_cells] in HCBr. destruct HCBr as (D184 & D192 & _).
assert (Vn1 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msB)) (rbn_A X + 200) 8 0).
{ apply (rbn3t_val_mem_mr _ mem2 (ms_mem msB) _ _ _ Hm2). apply val_mem_zero8. intros i Hi.
  rewrite Heff by lia. reflexivity. }
assert (Vo1 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msB)) (rbn_A X + 208) 4 0).
{ apply (rbn3t_val_mem_mr _ mem2 (ms_mem msB) _ _ _ Hm2). apply rbn3t_val_mem_zero4. intros i Hi.
  replace (rbn_A X + 208 + i) with (rbn_A X + 200 + (8 + i)) by lia. rewrite Heff by lia. reflexivity. }
pose proof HM2b as (_ & _ & _ & HroB & _ & _ & _ & HShB).
assert (Vsh1 : aview SEGS (w_H W1) (ms_mem msB) (rbn_SH X pos + 4) = Some 5)
  by (rewrite (HShB 4 ltac:(rewrite rbn3t_sh_len; lia)); reflexivity).
pmkst HS.
prreg HS (10%bv : bv 5) Sa0. prreg HS (11%bv : bv 5) Sa1. prreg HS (12%bv : bv 5) Sa2.
prreg HS (1%bv : bv 5) Sra. prreg HS (2%bv : bv 5) Ssp. prreg HS (3%bv : bv 5) Sgp. prreg HS (4%bv : bv 5) Stp.
assert (SspA : spZ (ms_regs msB) = rbn_A X).
{ unfold spZ. rewrite Ssp, OLD2, (EE 2%nat 2%bv eq_refl), RB2 by lia. unfold w64. apply unsigned_lit_small. lia. }
rewrite pa_sigma_sb_dec.
eapply SRr_bind.
{ apply (rbn3t_sbd (ri_fq X) X pos ((3, pos) :: ri_own X) lyc1 Sc1 W1 (ms_mem msB) _ (ms_regs msB) (ri_i X) 0
    eq_refl HX HJ2 eq_refl Hfrs1 HroB).
  - rewrite Sra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Sra. pose proof pa_B_ok as (HB0 & HB1 & _). rewrite unsigned_lit_small by lia. lia.
  - rewrite Sgp, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact RB3.
  - rewrite Stp, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact RB4.
  - exact SspA.
  - rewrite Sa0, W9. reflexivity.
  - rewrite Sa1, OLD2, E32 by lia. reflexivity.
  - rewrite Sa2. reflexivity.
  - exact Hbi.
  - left. reflexivity.
  - exact D184.
  - exact D192.
  - exact Vn1.
  - exact Vo1.
  - exact Vsh1. }
cbv beta. intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & Hperm3 &
  P1 & P2 & P3 & P4 & P5 & P6 & PV0 & PV8 & PV16 & PV24 & PG).
assert (HM3 : rbn_mid B X pos ly3 S3 W3 mem3 md3 (fun _ => False) (rbn_sh true false false false)).
{ apply (rbn3t_mid_sb X pos lyc1 Sc1 W1 (ms_mem msB) _ ly3 S3 W3 mem3 md3 _ (spZ (ms_regs msB)) (rbn_A X + 184)
    (fun a => 0 < sb_dec_c.sb_dec_room 5 0 /\
       rbn_F X pos + 32 + 0 <= a < rbn_F X pos + 32 + 0 + sb_dec_c.sb_dec_acc (ri_i X) 2 5 0)
    HX HM2b HJ3 Hfrs3 Hperm3 ltac:(rewrite rbn3t_sh_len; lia) SspA eq_refl).
  - intros a (_ & Ha). rewrite Hacc1 in Ha. lia.
  - exact P1.
  - exact P2.
  - exact P3.
  - exact P4.
  - exact P5. }
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite W9; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply P1; [lia | rewrite SspA; lia | lia |
      intros (_ & Hx); rewrite Hacc1 in Hx; lia].
  - exfalso. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 50 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 50)%nat -> ew E3 n = ew E2 n)
  by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
clear HE3.
assert (W9' : bv_unsigned (ew E3 9%nat) = rbn_A X) by (rewrite OLD3 by lia; exact W9).
rewrite Sra.
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
rename ms into msC. rename mat into matC. rename HF into HFC. rename HFr into HFrC. rename HG into HGC.
assert (Hm3 : forall x, mrestrict (w_H W3) (ms_mem msC) x = mrestrict (w_H W3) mem3 x).
{ intros x. apply HFrC. intros (r & Hr & Hw). cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
pose proof (rbn3t_mid_same X pos ly3 S3 W3 mem3 md3 (ms_mem msC) _ _ HM3 HJ3 Hm3) as HM3b.
assert (HCC : rbn_cells (mrestrict (w_H W3) (ms_mem msC)) (rbn3t_cA X pos)).
{ apply (rbn3t_cells_kept (w_H W1) (w_H W3) (ms_mem msB) (ms_mem msC)); [|exact HCB].
  intros a n v k Hin Hk. pose proof (rbn3t_cA_rng X pos a n v Hin) as Hr.
  rewrite (rbn3t_aview_mr _ _ _ _ Hm3).
  apply P1; [lia | rewrite SspA; lia | lia | intros (_ & Hx); rewrite Hacc1 in Hx; lia]. }
assert (G1 : garr8 SEGS (mrestrict (w_H W3) (ms_mem msC)) (rbn_F X pos + 32) (bn_dec (ri_i X) 2)).
{ pose proof (PG Hroom1) as G. rewrite (rbn3t_fst (ri_i X) 0 Hbi (or_introl eq_refl)) in G.
  rewrite Z.add_0_r in G.
  eapply garr8_aview_kept; [|exact G]. intros a _. apply rbn3t_aview_mr. exact Hm3. }
assert (Vp2 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (rbn_A X + 184) 8 (rbn_F X pos + 32))
  by (apply (rbn3t_val_mem_mr _ mem3 (ms_mem msC) _ _ _ Hm3); exact PV0).
assert (Vc2 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (rbn_A X + 192) 8 5).
{ apply (rbn3t_val_mem_mr _ mem3 (ms_mem msC) _ _ _ Hm3).
  replace (rbn_A X + 192) with (rbn_A X + 184 + 8) by lia. exact PV8. }
assert (Vn2 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (rbn_A X + 200) 8 2).
{ apply (rbn3t_val_mem_mr _ mem3 (ms_mem msC) _ _ _ Hm3).
  replace (rbn_A X + 200) with (rbn_A X + 184 + 16) by lia. rewrite Hacc1 in PV16. exact PV16. }
assert (Vo2 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (rbn_A X + 208) 4 0).
{ apply (rbn3t_val_mem_mr _ mem3 (ms_mem msC) _ _ _ Hm3).
  replace (rbn_A X + 208) with (rbn_A X + 184 + 24) by lia. rewrite Hovf1 in PV24. exact PV24. }
pose proof HM3b as (_ & _ & _ & HroC & _ & _ & _ & HShC).
assert (Vsh2 : aview SEGS (w_H W3) (ms_mem msC) (rbn_SH X pos + 4) = Some 5)
  by (rewrite (HShC 4 ltac:(rewrite rbn3t_sh_len; lia)); reflexivity).
pmkst HS.
prreg HS (10%bv : bv 5) Ta0. prreg HS (11%bv : bv 5) Ta1. prreg HS (12%bv : bv 5) Ta2.
prreg HS (1%bv : bv 5) Tra. prreg HS (2%bv : bv 5) Tsp. prreg HS (3%bv : bv 5) Tgp. prreg HS (4%bv : bv 5) Ttp.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (25%bv : bv 5) T25.
assert (TspA : spZ (ms_regs msC) = rbn_A X).
{ unfold spZ. rewrite Tsp, OLD3, OLD2, (EE 2%nat 2%bv eq_refl), RB2 by lia. unfold w64.
  apply unsigned_lit_small. lia. }
rewrite pa_sigma_sb_dec.
eapply SRr_bind.
{ apply (rbn3t_sbd (ri_fq X) X pos ((3, pos) :: ri_own X) ly3 S3 W3 (ms_mem msC) _ (ms_regs msC) (ri_o X) 2
    eq_refl HX HJ3 eq_refl ltac:(rewrite Hfrs3; exact Hfrs1) HroC).
  - rewrite Tra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Tra. pose proof pa_B_ok as (HB0 & HB1 & _). rewrite unsigned_lit_small by lia. lia.
  - rewrite Tgp, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact RB3.
  - rewrite Ttp, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact RB4.
  - exact TspA.
  - rewrite Ta0, W9'. reflexivity.
  - rewrite Ta1, OLD3, OLD2, E33 by lia. reflexivity.
  - rewrite Ta2. reflexivity.
  - exact Hbo.
  - right. reflexivity.
  - exact Vp2.
  - exact Vc2.
  - exact Vn2.
  - exact Vo2.
  - exact Vsh2. }
cbv beta. intros W4 c4 Hle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & Hperm4 &
  Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & QV0 & QV8 & QV16 & QV24 & QG).
pose proof (rbn3t_mid_sb X pos ly3 S3 W3 (ms_mem msC) _ ly4 S4 W4 mem4 md4 _ (spZ (ms_regs msC)) (rbn_A X + 184)
  (fun a => 0 < sb_dec_c.sb_dec_room 5 2 /\
     rbn_F X pos + 32 + 2 <= a < rbn_F X pos + 32 + 2 + sb_dec_c.sb_dec_acc (ri_o X) 2 5 2)
  HX HM3b HJ4 Hfrs4 Hperm4 ltac:(rewrite rbn3t_sh_len; lia) TspA eq_refl
  ltac:(intros a (_ & Ha); rewrite Hacc2 in Ha; lia) Q1 Q2 Q3 Q4 Q5) as HM4.
pose proof (rbn3t_fa X pos ly3 S3 W3 (ms_mem msC) _ _ _ HX HM3b 3 pos) as FA3b.
assert (HCD : rbn_cells (mrestrict (w_H W4) mem4) (rbn3t_cA X pos)).
{ apply (rbn3t_cells_kept (w_H W3) (w_H W4) (ms_mem msC) mem4); [|exact HCC].
  intros a n v k Hin Hk. pose proof (rbn3t_cA_rng X pos a n v Hin) as Hr.
  apply Q1; [lia | rewrite TspA; lia | lia | intros (_ & Hx); rewrite Hacc2 in Hx; lia]. }
unfold rbn3t_cA in HCD. apply rbn3t_cells_app in HCD as [HCDa HCDr]. cbn [rbn_cells] in HCDr.
destruct HCDr as (E184 & E192 & _).
destruct (rbn3t_regs_pres _ _ HP4) as (P2r & P3r & P4r & P8r & P9r & P18r & P19r & P20r & P21r & P22r & P23r & P25r).
apply SRr_ret.
exists pos, regs4, ly4, S4, mem4, md4, P.
split.
{ unfold rbn_cfg, cfg_at, w64. rewrite Tra.
  replace (BASE + AF_both3_reac_box_name + RBN_U3) with (BASE + 14700)
    by (unfold AF_both3_reac_box_name, RBN_U3; lia).
  reflexivity. }
unfold rbn3_stU. split; [exact HM4|].
split.
{ unfold rbn_rbase.
  split; [rewrite P2r, Tsp, OLD3, OLD2, (EE 2%nat 2%bv eq_refl) by lia; exact RB2|].
  split; [rewrite P3r, Tgp, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) by lia; exact RB3|].
  split; [rewrite P4r, Ttp, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) by lia; exact RB4|].
  split; [rewrite P8r, T8, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; exact RB8|].
  split; [rewrite P9r, T9, OLD3, OLD2, (EE 9%nat 9%bv eq_refl) by lia; exact RB9|].
  split; [rewrite P19r, T19, OLD3, OLD2, (EE 19%nat 19%bv eq_refl) by lia; exact RB19|].
  split; [rewrite P22r, T22, OLD3, OLD2, (EE 22%nat 22%bv eq_refl) by lia; exact RB22|].
  rewrite P23r, T23, OLD3, OLD2, (EE 23%nat 23%bv eq_refl) by lia; exact RB23. }
split; [rewrite P18r, T18, OLD3, OLD2, (EE 18%nat 18%bv eq_refl) by lia; exact R18|].
split; [rewrite P20r, T20, OLD3, OLD2 by lia; rewrite U19; reflexivity|].
split; [rewrite P21r, T21; reflexivity|].
split; [rewrite P25r, T25, OLD3, OLD2, (EE 25%nat 25%bv eq_refl) by lia; exact R25|].
split.
{ apply rbn3t_cells_app. split; [exact HCDa|].
  unfold rbn_rw. cbn [rbn_cells]. split; [exact E184|]. split; [exact E192|].
  split; [replace (rbn_A X + 200) with (rbn_A X + 184 + 16) by lia; rewrite Hacc2 in QV16; exact QV16|].
  split; [replace (rbn_A X + 208) with (rbn_A X + 184 + 24) by lia; rewrite Hovf2 in QV24; exact QV24|].
  exact I. }
split.
{ rewrite (rbn3t_w4_eq X HA). apply garr8_app. split.
  - eapply garr8_aview_kept; [|exact G1]. intros a Ha.
    rewrite <- HDi, HDil in Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    apply (Q4 3 pos a ltac:(rewrite Hfrs3, Hfrs1; left; reflexivity)).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA3b, Hfb3. fold (rbn_F X pos). lia.
    + lia.
    + intros (_ & Hx). rewrite Hacc2 in Hx. lia.
  - replace (Z.of_nat (length (bn_dec (ri_i X) 2))) with 2 by (rewrite <- HDi, HDil; reflexivity).
    pose proof (QG Hroom2) as G. rewrite (rbn3t_fst (ri_o X) 2 Hbo (or_intror eq_refl)) in G. exact G. }
split; [exact HPok | exact HA].
Qed.
End h.
End f.
End d.
