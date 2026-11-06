(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 167 of its 196 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacBoxName.v, with its module paths and module names changed; 766 of its 807 lines of code are new or changed and 155 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC45 YC88 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition slR_SH : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 4 (CVal 1 (SLit 4))].
Definition slR_BUF (j : Z) : YP09.region := YP09.mkRegion (Some 25%nat) 0 3 0 0 [YP09.mkChunk j (CVal 1 (SOff 32 0))].
Definition sl_shkey (j : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 j) (SLit 3)) (SOff 22 0).
Definition sl_facts (j : Z) : facts :=
  mkFacts [(25%nat, mkAF 4096 (2 ^ 47) 5); (26%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (32%nat, mkAF 0 255 0)] []
    [(sl_shkey j, SOff 24 4)].
Definition sl_regs (j : Z) : list sv := sr_set (sr_set sr_atoms 20%bv (SLit j)) 21%bv (SLit (-1)).
Definition ss_sl (j : Z) : sstate := mkSS (AF_both3_sb_dec + SBD_PL) (sl_regs j) [slR_SH; slR_BUF j] None (sl_facts j).
Definition ss_slp (j : Z) : sstate := mkSS (AF_both3_sb_dec + 0x1a8) (sl_regs j) [] None (mkFacts [] [] []).

Lemma sl_lsd_len : forall k v, (length (sb_dec_c.sb_dec_lsd v k) <= k)%nat.
Proof.
induction k as [|k IH]; intros v; cbn [sb_dec_c.sb_dec_lsd length]; [lia|].
destruct (v <? 10); cbn [length]; [lia|]. specialize (IH (v / 10)). lia.
Qed.
Lemma sl_lsd_pos : forall k v, (1 <= length (sb_dec_c.sb_dec_lsd v (S k)))%nat.
Proof. intros k v. cbn [sb_dec_c.sb_dec_lsd length]. lia. Qed.
Lemma sl_D_len : forall v md, md = 1 \/ md = 2 -> 1 <= Z.of_nat (length (sb_dec_c.sb_dec_D v md)) <= 3.
Proof.
intros v md Hmd. unfold sb_dec_c.sb_dec_D. cbv zeta. rewrite length_rev.
pose proof (sl_lsd_len 3 v) as H1. pose proof (sl_lsd_pos 2 v) as H2.
destruct (Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3)) <? md) eqn:Hc.
- apply Z.ltb_lt in Hc. rewrite length_app. cbn [length]. lia.
- lia.
Qed.
Lemma sl_room_nn : forall cap n, 0 <= sb_dec_c.sb_dec_room cap n.
Proof. intros cap n. unfold sb_dec_c.sb_dec_room. destruct (n + 1 <=? cap) eqn:H; [apply Z.leb_le in H; lia | lia]. Qed.
Lemma sl_succ_iff : forall cap n e, 0 <= n -> 0 <= e ->
  (n + Z.min e (sb_dec_c.sb_dec_room cap n) + 1 < cap <-> e < sb_dec_c.sb_dec_room cap n).
Proof.
intros cap n e Hn He. unfold sb_dec_c.sb_dec_room.
destruct (n + 1 <=? cap) eqn:H1; [apply Z.leb_le in H1 | apply Z.leb_gt in H1]; lia.
Qed.
Lemma sl_nth_rev : forall (l : list Z) j e, 0 <= j -> 0 <= e -> j + e + 1 = Z.of_nat (length l) ->
  nth (Z.to_nat j) (rev l) 0 = nth (Z.to_nat e) l 0.
Proof. intros l j e Hj He H. rewrite rev_nth by lia. f_equal. lia. Qed.
Lemma sl_firstn_S : forall (l : list Z) e, (e < length l)%nat -> firstn (S e) l = firstn e l ++ [nth e l 0].
Proof.
induction l as [|x l IH]; intros e He; cbn [length] in He; [lia|].
destruct e as [|e]; cbn [firstn nth app]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.
Lemma sl_S1 : forall SP, SP mod 16 = 0 ->
  SP - 144 <= 32 * ((SP - 128) / 32) <= SP - 128 /\ (32 * ((SP - 128) / 32)) mod 32 = 0.
Proof.
intros SP H. split; [|rewrite Z.mul_comm; apply Z.mod_mul; lia].
pose proof (Z.div_mod (SP - 128) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (SP - 128) 32 ltac:(lia)). lia.
Qed.
Lemma sl_neg_u : forall x, 0 <= x < 2 ^ 63 -> bv_unsigned (Z_to_bv 64 (- x - 1)) = 2 ^ 64 - x - 1.
Proof.
intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (- x - 1) with ((2 ^ 64 - x - 1) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma sl_regs_ok_set : forall E sr (regs : bvmap 5 word) r e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
- exact Hr.
Qed.
Lemma sl_ra_band : forall (rd rd' : Z -> option Z) a n,
  (forall s, kLowMemEnd <= s < kHighMemBeg -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma sl_shv_band : forall (rd rd' : Z -> option Z) a n,
  (forall s, kLowMemEnd <= s < kHighMemBeg -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|].
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + (a + n - 1) / 8) 8).
pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.
Lemma sl_shv_sub : forall (rd : Z -> option Z) a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> a' + n' <= a + n -> 0 < n' -> shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma sl_awr_ly : forall STK sp0 FP bl0 blc ly ly' own a, ly_F ly' = ly_F ly ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof. intros STK sp0 FP bl0 blc ly ly' own a E H. unfold awr_byte, in_frames, frame_addr in *. rewrite E. exact H. Qed.
Lemma sl_nowr_sl : forall j E a, ~ in_wrange E (ss_mem (ss_sl j)) a.
Proof.
intros j E a (r & Hr & Ha). cbn [ss_sl ss_mem In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [slR_SH slR_BUF YP09.r_wlo YP09.r_whi] in Ha; lia.
Qed.
Lemma sl_nowr_slp : forall j E a, ~ in_wrange E (ss_mem (ss_slp j)) a.
Proof. intros j E a (r & Hr & _). cbn [ss_slp ss_mem In] in Hr. exact Hr. Qed.
Lemma sl_awr_sl : forall j E STK sp0 FP bl0 blc ly own, awr_ok E (ss_mem (ss_sl j)) STK sp0 FP bl0 blc ly own.
Proof. intros j E STK sp0 FP bl0 blc ly own a Ha. exfalso. exact (sl_nowr_sl j E a Ha). Qed.
Lemma sl_pres_list : forall (r1 r2 : bvmap 5 word), aregs_preserved r1 r2 ->
  forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr r1 r.
Proof.
intros r1 r2 HP r Hr.
assert (K : forall z, r = Z_to_bv 5 z -> acallee_saved z -> getr r2 r = getr r1 r) by (intros z -> Hz; exact (HP z Hz)).
cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
lazymatch goal with |- getr _ ?x = _ => let z := eval vm_compute in (bv_unsigned x) in
  exact (K z ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)) end.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition sl_veq (W : world SEGS) (m m' : word -> option byte) : Prop :=
  forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x.
Lemma sl_veq_of_frame : forall E rs (W : world SEGS) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> (forall a, ~ in_wrange E rs a) -> sl_veq W m m'.
Proof. intros E rs W m m' HF Hn x. apply HF. apply Hn. Qed.
Lemma sl_veq_view : forall W m m', sl_veq W m m' -> forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W m m' HV a. apply (aview_eq_of SEGS). apply HV. Qed.
Lemma sl_veq_present : forall W m m' a, sl_veq W m m' -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
intros W m m' a HV [Hh [b Hb]]. split; [exact Hh|]. exists b.
specialize (HV (Z_to_bv 64 a)). unfold mrestrict in HV. rewrite Hh in HV. rewrite HV. exact Hb.
Qed.
Lemma sl_veq_val : forall W m m' a n v, sl_veq W m m' ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof. intros W m m' a n v HV. apply (val_mem_kept SEGS). intros k Hk. apply sl_veq_view. exact HV. Qed.
Lemma sl_veq_garr8 : forall W m m' a l, sl_veq W m m' ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l HV H jj Hj. destruct (H jj Hj) as [H1 H2].
split; [exact (sl_veq_val W m m' _ _ _ HV H1) | exact H2].
Qed.
Lemma sl_ra_eq : forall (rd rd' : Z -> option Z) Bs a n, (forall x, rd' x = rd x) ->
  range_addressable rd Bs a n -> range_addressable rd' Bs a n.
Proof. intros rd rd' Bs a n He H x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s. rewrite He. split; assumption. Qed.
Lemma sl_shv_eq : forall (rd rd' : Z -> option Z) a n, (forall x, rd' x = rd x) ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof. intros rd rd' a n He H s Hs. rewrite He. exact (H s Hs). Qed.
Lemma sl_rec_veq : forall X W m m' e, sl_veq W m m' -> sbd_rec X W m e -> sbd_rec X W m' e.
Proof.
intros X W m m' e HV (H1 & H2 & H3 & H4 & H5).
split; [exact (sl_veq_val W m m' _ _ _ HV H1)|]. split; [exact (sl_veq_val W m m' _ _ _ HV H2)|].
split; [exact (sl_veq_val W m m' _ _ _ HV H3)|]. split; [exact (sl_veq_val W m m' _ _ _ HV H4)|].
intros Hr. exact (sl_veq_garr8 W m m' _ _ HV (H5 Hr)).
Qed.
Lemma sl_sh_veq : forall W m m' q l, sl_veq W m m' -> sbd_shadow_at W m q l -> sbd_shadow_at W m' q l.
Proof. intros W m m' q l HV H jj Hj. rewrite (sl_veq_view W m m' HV). exact (H jj Hj). Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TSB : tsb_ch_spec B.
Lemma sl_kept_veq : forall X W m m', sl_veq W m m' -> sbd_kept B X W m -> sbd_kept B X W m'.
Proof.
intros X W m m' HV (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (sl_veq_view W m m' HV) as V.
split; [intros a H1 H2 H3; rewrite V; exact (K1 a H1 H2 H3)|].
split; [intros b mm i H1 H2 H3; rewrite V; exact (K2 b mm i H1 H2 H3)|].
split; [intros a H1 H2 H3; rewrite V; exact (K3 a H1 H2 H3)|].
split; [intros cid p a H1 H2 H3; rewrite V; exact (K4 cid p a H1 H2 H3)|].
split; [intros a H1 H2 H3; exact (sl_veq_present W m m' a HV (K5 a H1 H2 H3))|].
intros a H1. exact (sl_veq_present W m m' a HV (K6 a H1)).
Qed.
Lemma sl_ro_veq : forall W m m', sl_veq W m m' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m').
Proof. intros W m m' HV H a H1 H2 H3. rewrite (sl_veq_view W m m' HV). exact (H a H1 H2 H3). Qed.
Lemma sl_recP_veq : forall X lyc1 Sc1 W m m' own, sl_veq W m m' ->
  sbd_recP B X lyc1 Sc1 W m own -> sbd_recP B X lyc1 Sc1 W m' own.
Proof.
intros X lyc1 Sc1 W m m' own HV (H1 & H2 & H3).
split; [exact (sl_ra_eq _ _ _ _ _ (sl_veq_view W m m' HV) H1)|].
split; [exact (sl_shv_eq _ _ _ _ (sl_veq_view W m m' HV) H2)|].
intros a Ha. destruct (H3 a Ha) as [Hw Hp]. split; [exact Hw | exact (sl_veq_present W m m' a HV Hp)].
Qed.
Lemma sl_outP_veq : forall X lyc1 Sc1 W m m' own, sl_veq W m m' ->
  sbd_outP B X lyc1 Sc1 W m own -> sbd_outP B X lyc1 Sc1 W m' own.
Proof.
intros X lyc1 Sc1 W m m' own HV (H1 & H2 & H3).
split; [exact (sl_ra_eq _ _ _ _ _ (sl_veq_view W m m' HV) H1)|].
split; [exact (sl_shv_eq _ _ _ _ (sl_veq_view W m m' HV) H2)|].
intros a Ha. destruct (H3 a Ha) as [Hw Hp]. split; [exact Hw | exact (sl_veq_present W m m' a HV Hp)].
Qed.
Lemma sl_mid0_veq : forall X pos lyc1 Sc1 W m md m' md', sl_veq W m m' ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W m' md' (si_k X) ->
  sbd_mid0 B X pos lyc1 Sc1 W m md -> sbd_mid0 B X pos lyc1 Sc1 W m' md'.
Proof.
intros X pos lyc1 Sc1 W m md m' md' HV HJ (_ & Hfr & Hab & Hro & Hk & Hf & Hfl & Hrp & Hop).
split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hab|].
split; [exact (sl_ro_veq W m m' HV Hro)|]. split; [exact (sl_kept_veq X W m m' HV Hk)|].
split; [intros jj r Hr; exact (sl_veq_val W m m' _ _ _ HV (Hf jj r Hr))|].
split; [exact (sl_veq_val W m m' _ _ _ HV Hfl)|].
split; [exact (sl_recP_veq X lyc1 Sc1 W m m' _ HV Hrp)|].
intros Hr. exact (sl_outP_veq X lyc1 Sc1 W m m' _ HV (Hop Hr)).
Qed.
Lemma sl_rbase_eq : forall X pos (r1 r2 : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr r1 r) ->
  sbd_rbase B X pos r1 -> sbd_rbase B X pos r2.
Proof.
intros X pos r1 r2 HE (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G23 & G24 & G25 & G26 & G27).
split; [rewrite HE by (cbn [In]; tauto); exact G2|]. split; [rewrite HE by (cbn [In]; tauto); exact G3|].
split; [rewrite HE by (cbn [In]; tauto); exact G4|]. split; [rewrite HE by (cbn [In]; tauto); exact G8|].
split; [rewrite HE by (cbn [In]; tauto); exact G9|]. split; [rewrite HE by (cbn [In]; tauto); exact G18|].
split; [rewrite HE by (cbn [In]; tauto); exact G19|]. split; [rewrite HE by (cbn [In]; tauto); exact G22|].
split; [rewrite HE by (cbn [In]; tauto); exact G23|]. split; [rewrite HE by (cbn [In]; tauto); exact G24|].
split; [rewrite HE by (cbn [In]; tauto); exact G25|]. split; [rewrite HE by (cbn [In]; tauto); exact G26|].
rewrite HE by (cbn [In]; tauto); exact G27.
Qed.
Lemma sl_F_facts : forall X pos lyc1 Sc1 W1 m md,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 m md ->
  (forall c p, frame_addr lyc1 c p = frame_addr (si_lyc X) c p) /\
  4096 <= sbd_F X pos /\ sbd_F X pos + 64 <= alloc_ceiling /\ sbd_F X pos mod 32 = 0 /\ in_app (sbd_F X pos) 64.
Proof.
intros X pos lyc1 Sc1 W1 m md HX HM.
destruct HX as (HJ & _). destruct HM as (HJ1 & Hfr1 & _).
pose proof HJ as (_ & Hly & _). pose proof HJ1 as (HAR1 & Hly1 & _).
assert (EF : forall c p, frame_addr lyc1 c p = frame_addr (si_lyc X) c p).
{ intros c p. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E1 & _).
  destruct Hly1 as (_ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Hin : In (0, pos) (frames Sc1)) by (rewrite Hfr1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin) as (H1 & H2 & H3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR1 Hin) as (H4 & _).
change (fs_frame_bytes 0) with 64 in H2, H3.
split; [exact EF|]. unfold sbd_F. rewrite <- (EF 0 pos).
split; [exact H1|]. split; [exact H2|]. split; [exact H4 | exact H3].
Qed.
Lemma sl_awr_notF : forall X pos lyc1 Sc1 W1 m md a,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 m md ->
  awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B (si_lyc X) (si_Sc X))
    (si_lyc X) (si_own X) a ->
  ~ (sbd_F X pos <= a < sbd_F X pos + 64).
Proof.
intros X pos lyc1 Sc1 W1 m md a HX HM Hw Ha.
destruct (sl_F_facts X pos lyc1 Sc1 W1 m md HX HM) as (EF & HF1 & HF2 & HF3 & HF4).
pose proof HX as (HJ & _). pose proof HM as (HJ1 & Hfr1 & Hab1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJ1 as (HAR1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (0, pos) (frames Sc1)) by (rewrite Hfr1; left; reflexivity).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)
  as (_ & [(Hc & _) | [(_ & b & n & Hb & Hr & _) | (cid & p & Hown & [(_ & Hr) | (Hr & _)])]]).
- lia.
- rewrite <- Hab1 in Hb.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b n 0 pos HAR1 Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  rewrite EF in Hd. unfold sbd_F in Ha. lia.
- apply in_split in Hown as (l2 & l3 & El).
  assert (Efr : frames Sc1 = [] ++ (0, pos) :: l2 ++ (cid, p) :: (l3 ++ frames (si_S X))).
  { rewrite Hfr1, Hfrs, El. cbn [app]. rewrite <- app_assoc. reflexivity. }
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ _ _ _ _ _ HAR1 Efr) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  rewrite !EF in Hd. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold sbd_F in Ha. lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF4. unfold kLowMemEnd, kHighShadowEnd in Hr. lia.
Qed.
Lemma sl_Er_facts : forall X pos lyc1 Sc1 W1 m md a,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 m md -> sbd_Er X a ->
  ~ (sbd_F X pos <= a < sbd_F X pos + 64) /\ (0 <= a < kLowMemEnd \/ kHighMemBeg <= a < kHighMemEnd) /\
  (a < sbd_SP X - SB_DEC_STK \/ sbd_SP X <= a).
Proof.
intros X pos lyc1 Sc1 W1 m md a HX HM HE.
pose proof HX as (HJ & Hro & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hal & Hlo & Hhi & Hnf & Hv & Hmd &
  HA0 & HA8 & HA63 & HAm & HAi & HAs & Hp & Hcap & Hn & Hn1 & Hov & Hrec0 & HrecP & Hout).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HE as [Ha | (Hroom & Ha)].
- destruct HrecP as (_ & _ & Hw). destruct (Hw a ltac:(lia)) as [Hwa _].
  split; [exact (sl_awr_notF X pos lyc1 Sc1 W1 m md a HX HM Hwa)|].
  unfold amem_range in HAm. split; lia.
- destruct (Hout Hroom) as (Hp0 & Hp63 & Hpm & _ & _ & Hpside & HoutP).
  destruct HoutP as (_ & _ & Hw). destruct (Hw a ltac:(lia)) as [Hwa _].
  split; [exact (sl_awr_notF X pos lyc1 Sc1 W1 m md a HX HM Hwa)|].
  unfold amem_range in Hpm. split; lia.
Qed.
Definition sl_mid (X : sbd_in) (pos j e : Z) (regs2 : bvmap 5 word) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
  sbd_mid0 B X pos ly2 S2 W2 mem2 md2 /\ sbd_shadow_at W2 mem2 (sbd_SH X pos) sbd_sh /\
  sbd_rbase B X pos regs2 /\ getr regs2 20 = w64 j /\ getr regs2 21 = w64 (-1) /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (sbd_F X pos + 32) (rev (sbd_D X)) /\
  sbd_rec X W2 mem2 (e + 1).
Lemma sl_entry : forall (fq : YK11.FPState) X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 b,
  sbd_cx B X -> sbd_stL B X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 -> (j = 0 \/ j = 1 \/ j = 2) ->
  b = nth (Z.to_nat e) (sbd_D X) 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [Z_to_bv 64 b])) (ss_sl j)
    (restrict (w_H W1) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + (AF_both3_sb_dec + SBD_PL))) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 b HX HL Hj3 Hb.
pose proof HL as (HM & HSH & HRB & H20 & H21 & Hj & He & HjeL & HGB & HR).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmd & _).
destruct (sl_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & HF1 & HF2 & HF3 & HF4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRB as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G23 & G24 & G25 & G26 & G27).
assert (HLen : 1 <= sbd_L X <= 3) by (unfold sbd_L, sbd_D; apply sl_D_len; exact Hmd).
assert (Hbj : b = nth (Z.to_nat j) (rev (sbd_D X)) 0)
  by (rewrite Hb; symmetry; apply sl_nth_rev; [lia | lia | unfold sbd_L in HjeL; lia]).
destruct (garr8_nthZ SEGS _ _ _ j HGB ltac:(lia) ltac:(rewrite length_rev; unfold sbd_L in HjeL; lia)) as [Vb Hbr].
rewrite <- Hbj in Vb, Hbr.
pose proof (HSH 4 ltac:(cbn; lia)) as H4. change (nth (Z.to_nat 4) sbd_sh 0) with 4 in H4.
destruct (val_mem1_of_aview SEGS _ _ _ _ H4) as [V4 _].
assert (HFb : sbd_F X pos < 2 ^ 47 - 64) by lia.
assert (HSHr : kLowMemEnd <= sbd_SH X pos /\ sbd_SH X pos + 8 <= kHighMemBeg /\ sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8).
{ unfold sbd_SH, shadow_addr. split; [|split; [|reflexivity]]; unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg;
  pose proof (Z.div_pos (sbd_F X pos) 8 ltac:(lia) ltac:(lia));
  assert (sbd_F X pos / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia); lia. }
remember (Eimg (Ereg regs1 [Z_to_bv 64 b])) as E eqn:HE.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E24 : ew E 24 = Z_to_bv 64 (sbd_SH X pos)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
assert (E25 : ew E 25 = Z_to_bv 64 (sbd_F X pos + 32)) by (rewrite (EE 25%nat 25%bv eq_refl); exact G25).
assert (E26 : ew E 26 = Z_to_bv 64 (- (sbd_F X pos + 32) - 1)) by (rewrite (EE 26%nat 26%bv eq_refl); exact G26).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact G22).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (U24 : bv_unsigned (ew E 24) = sbd_SH X pos)
  by (rewrite E24; apply unsigned_lit_small; unfold kLowMemEnd, kHighMemBeg in HSHr; lia).
assert (U25 : bv_unsigned (ew E 25) = sbd_F X pos + 32) by (rewrite E25; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_sl. apply pa_entry_st_ok_full.
- rewrite HE. unfold sl_regs. apply sl_regs_ok_set; [apply sl_regs_ok_set; [apply regs_ok_Eimg_Ereg|]|].
  + cbn [sv_denot]. rewrite H20. reflexivity.
  + cbn [sv_denot]. rewrite H21. reflexivity.
- destruct Hj3 as [-> | [-> | ->]]; vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, slR_SH, slR_BUF;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U24. split; [lia|]. split; [unfold kHighMemBeg in HSHr; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (sbd_SH X pos) 4 1 (SLit 4) 4); [reflexivity | lia | lia | exact V4].
  + rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (sbd_F X pos + 32) j 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Vb].
- cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint, slR_SH, slR_BUF. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U25.
  destruct HSHr as (HS1 & HS2 & HS3). unfold SHADOW_OFF in HS3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF4. lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms sl_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U25, E26, E32, sl_neg_u, unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia.
  + cbn [f_alias sl_facts alias_ok]. split; [|exact I]. unfold sl_shkey.
    apply U_inj. rewrite U_SAlu, U_srl3. cbn [zalu_raw].
    rewrite (U_atom_off E 25 (sbd_F X pos + 32) j E25 ltac:(lia) ltac:(lia)).
    rewrite (U_atom E 22 SHADOW_OFF E22 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom_off E 24 (sbd_SH X pos) 4 E24 ltac:(unfold kHighMemBeg in HSHr; lia) ltac:(unfold kHighMemBeg in HSHr; lia)).
    destruct HSHr as (_ & _ & HS3). rewrite HS3. unfold SHADOW_OFF.
    rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma sl_common : forall X pos (regsc : bvmap 5 word) lyc1 Sc1 W1 memA mdA ly2 S2 W2 mem2 md2 (Er : Z -> Prop),
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memA mdA ->
  sbd_shadow_at W1 memA (sbd_SH X pos) sbd_sh ->
  garr8 SEGS (mrestrict (w_H W1) memA) (sbd_F X pos + 32) (rev (sbd_D X)) ->
  spZ regsc = sbd_S1 X ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) ly2 S2 W2 mem2 md2 (si_k X) ->
  frames S2 = frames Sc1 -> ablocks B ly2 S2 = ablocks B lyc1 Sc1 ->
  tsb_ch_kept B lyc1 Sc1 W1 memA W2 mem2 (spZ regsc) Er -> (forall a, Er a -> sbd_Er X a) ->
  sbd_mid0 B X pos ly2 S2 W2 mem2 md2 /\ sbd_shadow_at W2 mem2 (sbd_SH X pos) sbd_sh /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (sbd_F X pos + 32) (rev (sbd_D X)).
Proof.
intros X pos regsc lyc1 Sc1 W1 memA mdA ly2 S2 W2 mem2 md2 Er HX HM HSH HGB Usp HJ2 Hfr2 Hab2
  (K1 & K2 & K3 & K4 & K5 & K6) HEr.
pose proof HX as (HJ & Hro & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hal & Hlo & Hhi & Hnf & Hv & Hmd &
  HA0 & HA8 & HA63 & HAm & HAi & HAs & Hp & Hcap & Hn & Hn1 & Hov & Hrec0 & HrecP & Hout).
destruct (sl_F_facts X pos lyc1 Sc1 W1 memA mdA HX HM) as (EF & HF1 & HF2 & HF3 & HF4).
pose proof HM as (HJ1 & Hfr1 & Hab1 & Hro1 & Hk1 & Hfm1 & Hfl1 & HrecP1 & HoutP1).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HJ1 as (_ & Hly1 & _). pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity. assert (WT : TSB_CH_STK = 4112) by reflexivity.
destruct (sl_S1 (sbd_SP X) Hal) as (HS1 & HS1m). fold (sbd_S1 X) in HS1, HS1m.
assert (HLen : 1 <= sbd_L X <= 3) by (unfold sbd_L, sbd_D; apply sl_D_len; exact Hmd).
assert (EF2 : ly_F ly2 = ly_F lyc1).
{ destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hly1 as (_ & _ & _ & _ & _ & E1 & _). congruence. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sbd_S1 X - TSB_CH_STK <= a < sbd_S1 X) -> ~ sbd_Er X a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memA a).
{ intros a Ha Hw HE. apply K1; [exact Ha | rewrite Usp; exact Hw | intros HE'; exact (HE (HEr a HE'))]. }
assert (KSH : forall s, kLowMemEnd <= s < kHighMemBeg -> aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W1) memA s).
{ intros s Hs. unfold kLowMemEnd, kHighMemBeg in Hs. apply KA; [lia | lia |].
  intros HE. destruct (sl_Er_facts X pos lyc1 Sc1 W1 memA mdA s HX HM HE) as (_ & Hz & _).
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hz. lia. }
assert (KFr : forall a, sbd_F X pos <= a < sbd_F X pos + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memA a).
{ intros a Ha. apply KA; [lia | lia |].
  intros HE. destruct (sl_Er_facts X pos lyc1 Sc1 W1 memA mdA a HX HM HE) as (Hn' & _). exact (Hn' Ha). }
assert (KStk : forall a, sbd_S1 X <= a < sbd_SP X -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memA a).
{ intros a Ha. apply KA; [lia | lia |].
  intros HE. destruct (sl_Er_facts X pos lyc1 Sc1 W1 memA mdA a HX HM HE) as (_ & _ & Hs). lia. }
split.
{ split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr1|]. split; [rewrite Hab2; exact Hab1|].
  split.
  { intros a Hro0 Ho He0.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    rewrite (K3 a Hia Ho He0). exact (Hro1 a Hro0 Ho He0). }
  split.
  { destruct Hk1 as (k1 & k2 & k3 & k4 & k5 & k6).
    split; [|split; [|split; [|split; [|split]]]].
    - intros a H1 H2 H3. rewrite (KA a ltac:(lia) ltac:(lia) H3). exact (k1 a H1 H2 H3).
    - intros b mm i Hb Hi H3.
      rewrite (K2 b mm i ltac:(rewrite Hab1; exact Hb) Hi ltac:(intros HE'; exact (H3 (HEr _ HE')))).
      exact (k2 b mm i Hb Hi H3).
    - intros a Hia Ho He0. rewrite (K3 a Hia Ho He0). exact (k3 a Hia Ho He0).
    - intros cid p a Hcp Ha H3.
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR Hcp) as (Hf1 & Hf2 & Hf3).
      pose proof (fs_frame_bytes_nonneg cid) as Hnn.
      assert (Hac : 0 <= a < alloc_ceiling).
      { pose proof (Z.mul_div_le (frame_addr (si_lyc X) cid p) 8 ltac:(lia)) as D1.
        pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
        pose proof (Z.div_pos (frame_addr (si_lyc X) cid p) 8 ltac:(lia) ltac:(lia)) as D3.
        pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
        destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha; lia. }
      rewrite (KA a ltac:(lia) ltac:(lia) H3). exact (k4 cid p a Hcp Ha H3).
    - intros a H1 H2 Hp0. apply K5; [lia | rewrite Usp; lia | exact (k5 a H1 H2 Hp0)].
    - intros a Ha. destruct (Z_lt_le_dec a (sbd_S1 X - TSB_CH_STK)) as [Hlt | Hge].
      + apply K5; [lia | rewrite Usp; lia | exact (k6 a Ha)].
      + destruct (Z_lt_le_dec a (sbd_S1 X)) as [Hlt2 | Hge2].
        * apply K6. rewrite Usp. lia.
        * apply K5; [lia | rewrite Usp; lia | exact (k6 a Ha)]. }
  split.
  { intros jj r Hr.
    assert (Hjj : (jj < length sbd_saved_regs)%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
    change (length sbd_saved_regs) with 12%nat in Hjj.
    apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact (Hfm1 jj r Hr)].
    intros k Hk. apply KStk. lia. }
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact Hfl1]. intros k Hk. apply KFr. lia. }
  split.
  { destruct HrecP1 as (Hra1 & Hsh1 & Hw1).
    split; [apply (sl_ra_band _ _ (si_A X) 28 KSH); [lia | unfold amem_range in HAm; lia | exact Hra1]|].
    split; [apply (sl_shv_band _ _ (si_A X) 28 KSH); [lia | unfold amem_range in HAm; lia | lia | exact Hsh1]|].
    intros a Ha. destruct (Hw1 a Ha) as [Hwa _].
    assert (Hwa2 : awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B ly2 S2) ly2
      ((0, pos) :: si_own X) a) by (rewrite Hab2; exact (sl_awr_ly _ _ _ _ _ _ _ _ _ EF2 Hwa)).
    split; [exact Hwa2 | exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 Hwa2))]. }
  intros Hroom. destruct (HoutP1 Hroom) as (Hra1 & Hsh1 & Hw1). destruct (Hout Hroom) as (Hp0 & Hp63 & Hpm & _).
  assert (Hacc : 0 < sbd_acc X).
  { unfold sbd_acc, sb_dec_c.sb_dec_acc. unfold sbd_room in Hroom. unfold sbd_L, sbd_D in HLen. lia. }
  split; [apply (sl_ra_band _ _ (si_p X + si_n X) (sbd_acc X) KSH); [lia | unfold amem_range in Hpm; lia | exact Hra1]|].
  split; [apply (sl_shv_band _ _ (si_p X + si_n X) (sbd_acc X) KSH); [lia | unfold amem_range in Hpm; lia | lia | exact Hsh1]|].
  intros a Ha. destruct (Hw1 a Ha) as [Hwa _].
  assert (Hwa2 : awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B ly2 S2) ly2
    ((0, pos) :: si_own X) a) by (rewrite Hab2; exact (sl_awr_ly _ _ _ _ _ _ _ _ _ EF2 Hwa)).
  split; [exact Hwa2 | exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 Hwa2))]. }
split.
{ intros jj Hjj. pose proof Hjj as Hjj'. change (Z.of_nat (length sbd_sh)) with 8 in Hjj'.
  rewrite KSH; [exact (HSH jj Hjj)|].
  unfold sbd_SH, shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg.
  pose proof (Z.div_pos (sbd_F X pos) 8 ltac:(lia) ltac:(lia)).
  assert (sbd_F X pos / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia). lia. }
apply (garr8_aview_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact HGB].
intros a Ha. rewrite length_rev in Ha. apply KFr. unfold sbd_L in HLen. lia.
Qed.
Lemma sl_after_call : forall (fq : YK11.FPState) X pos j e (regsc : bvmap 5 word) lyc1 Sc1 W1 memA mdA W2 c2,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memA mdA ->
  sbd_shadow_at W1 memA (sbd_SH X pos) sbd_sh ->
  garr8 SEGS (mrestrict (w_H W1) memA) (sbd_F X pos + 32) (rev (sbd_D X)) ->
  sbd_rec X W1 memA e ->
  0 <= j -> 0 <= e -> j + e + 1 = sbd_L X ->
  sbd_rbase B X pos regsc -> getr regsc 20 = w64 j -> getr regsc 21 = w64 (-1) ->
  tsb_ch_post B fq (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W1 memA (si_k X) regsc (si_A X) (nth (Z.to_nat e) (sbd_D X) 0)
    (si_p X) (si_cap X) (sbd_ne X e) W2 c2 ->
  exists regs2 mem2 md2 ly2 S2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2 /\
    sl_mid X pos j e regs2 ly2 S2 W2 mem2 md2.
Proof.
intros fq X pos j e regsc lyc1 Sc1 W1 memA mdA W2 c2 HX HM HSH HGB HR Hj He HjeL HRB G20 G21 HP.
destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hfr2 & Hab2 & Hcase).
exists regs2, mem2, md2, ly2, S2. split; [reflexivity|].
pose proof HX as (HJ & Hro & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hal & Hlo & Hhi & Hnf & Hv & Hmd &
  HA0 & HA8 & HA63 & HAm & HAi & HAs & Hp & Hcap & Hn & Hn1 & Hov & Hrec0 & HrecP & Hout).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity. assert (WT : TSB_CH_STK = 4112) by reflexivity.
destruct (sl_S1 (sbd_SP X) Hal) as (HS1 & HS1m). fold (sbd_S1 X) in HS1, HS1m.
assert (Usp : spZ regsc = sbd_S1 X).
{ destruct HRB as (G2 & _). unfold spZ. rewrite G2. unfold w64. apply unsigned_lit_small. lia. }
assert (HLen : 1 <= sbd_L X <= 3) by (unfold sbd_L, sbd_D; apply sl_D_len; exact Hmd).
pose proof (sl_room_nn (si_cap X) (si_n X)) as HnR. fold (sbd_room X) in HnR.
assert (Hc256 : 0 <= nth (Z.to_nat e) (sbd_D X) 0 < 256).
{ destruct (garr8_nthZ SEGS _ _ _ j HGB ltac:(lia) ltac:(rewrite length_rev; unfold sbd_L in HjeL; lia)) as [_ Hr].
  rewrite (sl_nth_rev (sbd_D X) j e Hj He ltac:(unfold sbd_L in HjeL; lia)) in Hr. exact Hr. }
pose proof (sl_pres_list regsc regs2 HPr) as HP15.
assert (HRB2 : sbd_rbase B X pos regs2)
  by (apply (sl_rbase_eq X pos regsc regs2); [intros r Hr; apply HP15; cbn [In] in Hr |- *; tauto | exact HRB]).
assert (G20' : getr regs2 20 = w64 j) by (rewrite (HP15 20%bv ltac:(cbn [In]; tauto)); exact G20).
assert (G21' : getr regs2 21 = w64 (-1)) by (rewrite (HP15 21%bv ltac:(cbn [In]; tauto)); exact G21).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> (si_A X <= a < si_A X + 28 \/
    (0 < sbd_room X /\ si_p X + si_n X <= a < si_p X + si_n X + sbd_acc X)) ->
  ~ (spZ regsc - TSB_CH_STK <= a < spZ regsc)).
{ intros a Ha [Hr | (Hroom & Hr)]; rewrite Usp; [lia|].
  destruct (Hout Hroom) as (_ & _ & _ & _ & _ & Hps & _). lia. }
destruct HR as (V0 & V8 & V16 & V24 & VG).
destruct Hcase as [(Hge & V24n & K) | (Hlt & V16n & Vb & K)].
- assert (HRo : sbd_room X <= e).
  { destruct (Z_lt_le_dec e (sbd_room X)) as [Hl | Hl]; [|exact Hl]. exfalso.
    pose proof (proj2 (sl_succ_iff (si_cap X) (si_n X) e Hn He) Hl) as Hs. unfold sbd_ne, sbd_room in Hge. lia. }
  destruct (sl_common X pos regsc lyc1 Sc1 W1 memA mdA ly2 S2 W2 mem2 md2 _ HX HM HSH HGB Usp HJ2 Hfr2 Hab2 K
    ltac:(intros a Ha; cbv beta in Ha; unfold sbd_Er; left; lia)) as (HM2 & HSH2 & HGB2).
  destruct K as (K1 & _).
  split; [exact HM2|]. split; [exact HSH2|]. split; [exact HRB2|]. split; [exact G20'|]. split; [exact G21'|].
  split; [exact HGB2|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact V0];
    intros k Hk; apply K1; [lia | apply KW; [lia | left; lia] | cbv beta; lia]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact V8];
    intros k Hk; apply K1; [lia | apply KW; [lia | left; lia] | cbv beta; lia]|].
  split; [replace (sbd_ne X (e + 1)) with (sbd_ne X e) by (unfold sbd_ne; lia);
    apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact V16];
    intros k Hk; apply K1; [lia | apply KW; [lia | left; lia] | cbv beta; lia]|].
  split; [replace (sbd_ov X (e + 1)) with 1 by (unfold sbd_ov; destruct (Z.ltb_spec (sbd_room X) (e + 1)); lia);
    exact V24n|].
  intros Hroom. replace (Z.min (e + 1) (sbd_room X)) with (Z.min e (sbd_room X)) by lia.
  destruct (Hout Hroom) as (Hp0 & Hp63 & _ & _ & HpA & _).
  apply (garr8_aview_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact (VG Hroom)].
  intros a Ha. rewrite length_firstn in Ha.
  assert (Ha' : si_p X + si_n X <= a < si_p X + si_n X + sbd_acc X).
  { unfold sbd_acc, sb_dec_c.sb_dec_acc. unfold sbd_room in Ha, HRo, Hroom. unfold sbd_D, sbd_L in *. lia. }
  apply K1; [lia | apply KW; [lia | right; split; [exact Hroom | exact Ha']] | cbv beta; lia].
- assert (HeR : e < sbd_room X).
  { apply (proj1 (sl_succ_iff (si_cap X) (si_n X) e Hn He)). unfold sbd_ne, sbd_room in Hlt. exact Hlt. }
  assert (Hroom : 0 < sbd_room X) by lia.
  destruct (Hout Hroom) as (Hp0 & Hp63 & Hpm & Hpi & HpA & Hps & _).
  assert (Hne : sbd_ne X e = si_n X + e) by (unfold sbd_ne; lia).
  assert (HeA : e < sbd_acc X)
    by (unfold sbd_acc, sb_dec_c.sb_dec_acc; unfold sbd_room in HeR; unfold sbd_L, sbd_D in HjeL; lia).
  destruct (sl_common X pos regsc lyc1 Sc1 W1 memA mdA ly2 S2 W2 mem2 md2 _ HX HM HSH HGB Usp HJ2 Hfr2 Hab2 K
    ltac:(intros a Ha; cbv beta in Ha; unfold sbd_Er; destruct Ha as [Ha | Ha];
          [left; lia | right; split; [exact Hroom | rewrite Hne in Ha; lia]])) as (HM2 & HSH2 & HGB2).
  destruct K as (K1 & _).
  split; [exact HM2|]. split; [exact HSH2|]. split; [exact HRB2|]. split; [exact G20'|]. split; [exact G21'|].
  split; [exact HGB2|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact V0];
    intros k Hk; apply K1; [lia | apply KW; [lia | left; lia] | cbv beta; rewrite Hne; lia]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact V8];
    intros k Hk; apply K1; [lia | apply KW; [lia | left; lia] | cbv beta; rewrite Hne; lia]|].
  split; [replace (sbd_ne X (e + 1)) with (sbd_ne X e + 1) by (unfold sbd_ne; lia); exact V16n|].
  split; [replace (sbd_ov X (e + 1)) with (sbd_ov X e)
      by (unfold sbd_ov; destruct (Z.ltb_spec (sbd_room X) (e + 1)); destruct (Z.ltb_spec (sbd_room X) e); lia);
    apply (val_mem_kept SEGS (w_H W1) (w_H W2) memA mem2); [|exact V24];
    intros k Hk; apply K1; [lia | apply KW; [lia | left; lia] | cbv beta; rewrite Hne; lia]|].
  intros _.
  pose proof (VG Hroom) as VGe. rewrite Z.min_l in VGe by lia.
  replace (Z.min (e + 1) (sbd_room X)) with (e + 1) by lia.
  replace (Z.to_nat (e + 1)) with (S (Z.to_nat e)) by lia.
  rewrite sl_firstn_S by (unfold sbd_L in HjeL; lia).
  apply (garr8_app1 SEGS (mrestrict (w_H W1) memA) (mrestrict (w_H W2) mem2) (si_p X + si_n X)).
  + exact VGe.
  + rewrite length_firstn, Nat.min_l by (unfold sbd_L in HjeL; lia).
    replace (si_p X + si_n X + Z.of_nat (Z.to_nat e)) with (si_p X + sbd_ne X e) by lia.
    rewrite Z.mod_small in Vb by lia. exact Vb.
  + exact Hc256.
  + intros a Ha. rewrite length_firstn, Nat.min_l in Ha by (unfold sbd_L in HjeL; lia).
    apply (mbyte_of_aview SEGS).
    apply K1; [lia | apply KW; [lia | right; split; [exact Hroom | lia]] | cbv beta; rewrite Hne; lia].
Qed.
Lemma sl_call : forall (fq : YK11.FPState) X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 (regsc : bvmap 5 word) memA mdA,
  sbd_cx B X -> sbd_stL B X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  sl_veq W1 memc1 memA ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W1 memA mdA (si_k X) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv -> getr regsc r = getr regs1 r) ->
  getr regsc 20 = w64 j -> getr regsc 21 = w64 (-1) ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_both3_sb_dec + 0x1a8)) ->
  getr regsc 10 = w64 (si_A X) -> getr regsc 11 = Z_to_bv 64 (nth (Z.to_nat e) (sbd_D X) 0) ->
  SRr SEGS W1 (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regsc memA mdA)
    (fun W2 c2 => exists regs2 mem2 md2 ly2 S2,
      c2 = mkCfg (mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + (AF_both3_sb_dec + 0x1a8))) mem2 (seg_rom SEGS)) md2 /\
      sl_mid X pos j e regs2 ly2 S2 W2 mem2 md2).
Proof.
intros fq X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 regsc memA mdA HX HL HV HJA GK G20 G21 G1 G10 G11.
pose proof HL as (HM & HSH & HRB & H20 & H21 & Hj & He & HjeL & HGB & HR).
pose proof HX as (HJ & Hro & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hal & Hlo & Hhi & Hnf & Hv & Hmd &
  HA0 & HA8 & HA63 & HAm & HAi & HAs & Hp & Hcap & Hn & Hn1 & Hov & Hrec0 & HrecP & Hout).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity. assert (WT : TSB_CH_STK = 4112) by reflexivity.
destruct (sl_S1 (sbd_SP X) Hal) as (HS1 & HS1m). fold (sbd_S1 X) in HS1, HS1m.
pose proof (sl_mid0_veq X pos lyc1 Sc1 W1 memc1 mdc1 memA mdA HV HJA HM) as HMA.
pose proof (sl_sh_veq W1 memc1 memA _ _ HV HSH) as HSHA.
pose proof (sl_veq_garr8 W1 memc1 memA _ _ HV HGB) as HGBA.
pose proof (sl_rec_veq X W1 memc1 memA e HV HR) as HRA.
assert (HRBc : sbd_rbase B X pos regsc) by exact (sl_rbase_eq X pos regs1 regsc GK HRB).
pose proof HMA as (HJ1 & Hfr1 & Hab1 & Hro1 & Hk1 & Hfm1 & Hfl1 & HrecP1 & HoutP1).
assert (Usp : spZ regsc = sbd_S1 X).
{ destruct HRBc as (G2 & _). unfold spZ. rewrite G2. unfold w64. apply unsigned_lit_small. lia. }
assert (HLen : 1 <= sbd_L X <= 3) by (unfold sbd_L, sbd_D; apply sl_D_len; exact Hmd).
pose proof (sl_room_nn (si_cap X) (si_n X)) as HnR. fold (sbd_room X) in HnR.
assert (Hc256 : 0 <= nth (Z.to_nat e) (sbd_D X) 0 < 256).
{ destruct (garr8_nthZ SEGS _ _ _ j HGB ltac:(lia) ltac:(rewrite length_rev; unfold sbd_L in HjeL; lia)) as [_ Hr].
  rewrite (sl_nth_rev (sbd_D X) j e Hj He ltac:(unfold sbd_L in HjeL; lia)) in Hr. exact Hr. }
pose proof HRA as (V0 & V8 & V16 & V24 & VG).
pose proof pa_B_ok as HBASE.
eapply SRr_mono.
{ apply (TSB fq (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W1 memA mdA (si_k X) regsc (si_A X) (nth (Z.to_nat e) (sbd_D X) 0)
    (si_p X) (si_cap X) (sbd_ne X e) []).
  - exact HJA.
  - exact Hro1.
  - rewrite G1. apply ret_ok_codeptr_v; [unfold AF_both3_sb_dec; lia | reflexivity].
  - unfold raZ. rewrite G1, unsigned_lit_small; unfold AF_both3_sb_dec; lia.
  - destruct HRBc as (_ & G3 & _). exact G3.
  - destruct HRBc as (_ & _ & G4 & _). exact G4.
  - exact G10.
  - exact G11.
  - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac. rewrite unsigned_lit_small by lia. lia.
  - rewrite Usp. lia.
  - rewrite Usp. lia.
  - rewrite Usp. lia.
  - lia.
  - exact HA0.
  - exact HA8.
  - exact HA63.
  - exact HAm.
  - rewrite Usp. lia.
  - exact HAi.
  - exact Hp.
  - exact Hcap.
  - unfold sbd_ne. lia.
  - exact V0.
  - exact V8.
  - exact V16.
  - exact (proj1 HrecP1).
  - exact (proj1 (proj2 HrecP1)).
  - intros a Ha. apply (proj2 (proj2 HrecP1)). lia.
  - intros Hlt.
    assert (HeR : e < sbd_room X)
      by (apply (proj1 (sl_succ_iff (si_cap X) (si_n X) e Hn He)); unfold sbd_ne, sbd_room in Hlt; exact Hlt).
    assert (Hroom : 0 < sbd_room X) by lia.
    destruct (Hout Hroom) as (Hp0 & Hp63 & Hpm & Hpi & HpA & Hps & _).
    destruct (HoutP1 Hroom) as (Hra1 & Hsh1 & Hw1).
    assert (HeA : e < sbd_acc X)
      by (unfold sbd_acc, sb_dec_c.sb_dec_acc; unfold sbd_room in HeR; unfold sbd_L, sbd_D in HjeL; lia).
    assert (Hne : sbd_ne X e = si_n X + e) by (unfold sbd_ne; lia).
    rewrite Hne.
    split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
    split; [apply (range_addressable_sub _ _ (si_p X + si_n X) (sbd_acc X)); [exact Hra1 | lia | lia]|].
    split; [apply (sl_shv_sub _ (si_p X + si_n X) (sbd_acc X)); [exact Hsh1 | lia | lia | lia]|].
    split; [rewrite Usp; lia|]. split; [unfold off_img in *; lia|]. split; [lia|].
    destruct (Hw1 (si_p X + (si_n X + e)) ltac:(lia)) as [Hwa Hpa]. split; [exact Hwa | exact Hpa]. }
cbv beta. intros W2 c2 _ HP.
destruct (sl_after_call fq X pos j e regsc lyc1 Sc1 W1 memA mdA W2 c2 HX HMA HSHA HGBA HRA Hj He HjeL HRBc G20 G21 HP)
  as (regs2 & mem2 & md2 & ly2 & S2 & -> & Hmid).
exists regs2, mem2, md2, ly2, S2. rewrite G1. split; [reflexivity | exact Hmid].
Qed.
Lemma sl_post : forall X pos j e regs2 ly2 S2 W2 mem2 md2,
  sl_mid X pos j e regs2 ly2 S2 W2 mem2 md2 -> (j = 0 \/ j = 1 \/ j = 2) -> 0 <= e -> j + e + 1 = sbd_L X ->
  SRr SEGS W2 (mkCfg (mkst (fx := si_fq X) regs2 (Z_to_bv 64 (BASE + (AF_both3_sb_dec + 0x1a8))) mem2 (seg_rom SEGS)) md2)
    (fun W3 c3 => (0 < j /\ sbd_atL B X (j - 1) (e + 1) W3 c3) \/ (j = 0 /\ sbd_atE B X W3 c3)).
Proof.
intros X pos j e regs2 ly2 S2 W2 mem2 md2 Hmid Hj3 He HjeL.
pose proof Hmid as (HM2 & HSH2 & HRB2 & G20 & G21 & HGB2 & HR2).
pose proof (proj1 HM2) as HJ2.
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi (fx := si_fq X) SEGS VAL E (ss_slp j)
  (restrict (w_H W2) (mkst (fx := si_fq X) regs2 (Z_to_bv 64 (BASE + (AF_both3_sb_dec + 0x1a8))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_slp. apply pa_entry_st_ok_full.
  - rewrite HE. unfold sl_regs. apply sl_regs_ok_set; [apply sl_regs_ok_set; [apply regs_ok_Eimg_Ereg|]|].
    + cbn [sv_denot]. rewrite G20. reflexivity.
    + cbn [sv_denot]. rewrite G21. reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE.
pose proof (@SRr_run_to_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
destruct Hj3 as [-> | [-> | ->]].
- paj_run_to_shc RUNTOP HS HJ2 (AF_both3_sb_dec + SBD_PE); [cbn [ss_slp ss_mem]; apply awr_ok_nil|].
  pose proof (sl_veq_of_frame _ _ W2 mem2 (ms_mem ms) HFr (sl_nowr_slp _ E)) as HV.
  assert (GK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs2 r)
    by (intros r Hr; cbn [In] in Hr;
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        lazymatch goal with |- getr _ ?x = _ => let Q := fresh "Q" in prreg HS x Q; rewrite Q; apply EE; reflexivity end).
  apply SRr_ret. pmkst HS.
  right. split; [reflexivity|].
  exists pos, (ms_regs ms), ly2, S2, (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split.
  { unfold sbd_cfg, cfg_at, w64.
    replace (BASE + AF_both3_sb_dec + SBD_PE) with (BASE + 16604) by (unfold AF_both3_sb_dec, SBD_PE; lia). reflexivity. }
  split; [exact (sl_mid0_veq X pos ly2 S2 W2 mem2 md2 (ms_mem ms) _ HV HJ2 HM2)|].
  split; [exact (sl_sh_veq W2 mem2 (ms_mem ms) _ _ HV HSH2)|].
  split; [exact (sl_rbase_eq X pos regs2 (ms_regs ms) GK HRB2)|].
  replace (sbd_L X) with (e + 1) by lia. exact (sl_rec_veq X W2 mem2 (ms_mem ms) (e + 1) HV HR2).
- paj_run_to_shc RUNTOP HS HJ2 (AF_both3_sb_dec + SBD_PL); [cbn [ss_slp ss_mem]; apply awr_ok_nil|].
  pose proof (sl_veq_of_frame _ _ W2 mem2 (ms_mem ms) HFr (sl_nowr_slp _ E)) as HV.
  assert (GK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs2 r)
    by (intros r Hr; cbn [In] in Hr;
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        lazymatch goal with |- getr _ ?x = _ => let Q := fresh "Q" in prreg HS x Q; rewrite Q; apply EE; reflexivity end).
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  apply SRr_ret. pmkst HS.
  left. split; [lia|].
  exists pos, (ms_regs ms), ly2, S2, (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split.
  { unfold sbd_cfg, cfg_at, w64.
    replace (BASE + AF_both3_sb_dec + SBD_PL) with (BASE + 16544) by (unfold AF_both3_sb_dec, SBD_PL; lia). reflexivity. }
  split; [exact (sl_mid0_veq X pos ly2 S2 W2 mem2 md2 (ms_mem ms) _ HV HJ2 HM2)|].
  split; [exact (sl_sh_veq W2 mem2 (ms_mem ms) _ _ HV HSH2)|].
  split; [exact (sl_rbase_eq X pos regs2 (ms_regs ms) GK HRB2)|].
  split; [rewrite Q20; reflexivity|]. split; [rewrite Q21; reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (sl_veq_garr8 W2 mem2 (ms_mem ms) _ _ HV HGB2)|].
  exact (sl_rec_veq X W2 mem2 (ms_mem ms) (e + 1) HV HR2).
- paj_run_to_shc RUNTOP HS HJ2 (AF_both3_sb_dec + SBD_PL); [cbn [ss_slp ss_mem]; apply awr_ok_nil|].
  pose proof (sl_veq_of_frame _ _ W2 mem2 (ms_mem ms) HFr (sl_nowr_slp _ E)) as HV.
  assert (GK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs2 r)
    by (intros r Hr; cbn [In] in Hr;
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        lazymatch goal with |- getr _ ?x = _ => let Q := fresh "Q" in prreg HS x Q; rewrite Q; apply EE; reflexivity end).
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  apply SRr_ret. pmkst HS.
  left. split; [lia|].
  exists pos, (ms_regs ms), ly2, S2, (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split.
  { unfold sbd_cfg, cfg_at, w64.
    replace (BASE + AF_both3_sb_dec + SBD_PL) with (BASE + 16544) by (unfold AF_both3_sb_dec, SBD_PL; lia). reflexivity. }
  split; [exact (sl_mid0_veq X pos ly2 S2 W2 mem2 md2 (ms_mem ms) _ HV HJ2 HM2)|].
  split; [exact (sl_sh_veq W2 mem2 (ms_mem ms) _ _ HV HSH2)|].
  split; [exact (sl_rbase_eq X pos regs2 (ms_regs ms) GK HRB2)|].
  split; [rewrite Q20; reflexivity|]. split; [rewrite Q21; reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (sl_veq_garr8 W2 mem2 (ms_mem ms) _ _ HV HGB2)|].
  exact (sl_rec_veq X W2 mem2 (ms_mem ms) (e + 1) HV HR2).
Qed.
Theorem sbd_segL : sbd_segL_stmt B.
Proof.
intros X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 HX HL.
pose proof HL as (HM & HSH & HRB & H20 & H21 & Hj & He & HjeL & HGB & HR).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmd & _).
assert (HLen : 1 <= sbd_L X <= 3) by (unfold sbd_L, sbd_D; apply sl_D_len; exact Hmd).
assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
pose proof (sl_entry (si_fq X) X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 _ HX HL Hj3 eq_refl) as HS.
remember (Eimg (Ereg regs1 [Z_to_bv 64 (nth (Z.to_nat e) (sbd_D X) 0)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (nth (Z.to_nat e) (sbd_D X) 0))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
pose proof HRB as (_ & _ & _ & _ & _ & _ & G19 & _).
pose proof (proj1 HM) as HJ1.
pose proof (@SRr_run_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (si_fq X) _ _ _ _ _ B LAWS) as RUNC.
unfold sbd_cfg, cfg_at. change (w64 (BASE + AF_both3_sb_dec + SBD_PL)) with (Z_to_bv 64 (BASE + AF_both3_sb_dec + SBD_PL)).
rewrite <- Z.add_assoc.
destruct Hj3 as [-> | [-> | ->]].
all: paj_run_shc RUNP RUNC HS HJ1; [apply sl_awr_sl |].
all: pose proof (sl_veq_of_frame _ _ W1 memc1 (ms_mem ms) HFr (sl_nowr_sl _ E)) as HV0.
all: clear HF HFr.
all: pmkst HS; rewrite pa_sigma_sb_ch.
all: prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11;
  prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21.
all: assert (GKc : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs1 r)
  by (intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
      lazymatch goal with |- getr _ ?x = _ => let Q := fresh "Q" in prreg HS x Q; rewrite Q; apply EE; reflexivity end).
all: rewrite (EE 19%nat 19%bv eq_refl) in R10; rewrite E32 in R11.
all: eapply SRr_bind; [exact (sl_call (si_fq X) X pos _ e regs1 lyc1 Sc1 W1 memc1 mdc1 (ms_regs ms) (ms_mem ms) _
  HX HL HV0 HJ1 GKc R20 R21 R1 ltac:(rewrite R10; exact G19) R11) |].
all: intros W2 c2 _ (regs2 & mem2 & md2 & ly2 & S2 & -> & Hmid).
all: apply (sl_post X pos _ e regs2 ly2 S2 W2 mem2 md2 Hmid); lia.
Qed.
End h.
End f.
End d.
