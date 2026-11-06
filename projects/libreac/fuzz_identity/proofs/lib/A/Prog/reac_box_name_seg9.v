(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:137-139 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:56-61 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa0.v:172-173. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn9_dec_len : forall x, bn_ok x = true -> (1 <= length (bn_dec x 1) <= 2)%nat.
Proof.
intros x Hx. apply bn_ok_in in Hx.
assert (A : forallb (fun y => (1 <=? length (bn_dec y 1))%nat && (length (bn_dec y 1) <=? 2)%nat) bn_oks = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A x Hx). apply andb_true_iff in A as [A1 A2].
apply Nat.leb_le in A1. apply Nat.leb_le in A2. lia.
Qed.
Lemma rbn9_tk_len : forall s l, (length (bn_tk s l) <= length l)%nat.
Proof.
intros s l. revert s. induction l as [|c r IH]; intros s; cbn [bn_tk length]; [lia|].
destruct ((c =? 45) && negb s); cbn [length]; [specialize (IH true); lia | specialize (IH s); lia].
Qed.
Lemma rbn9_args : forall X : rbn_in, rbm_args X ->
  ri_name X <> 0 /\ ri_token X <> 0 /\ ri_display X <> 0 /\ ri_name_len X <> 0 /\ ri_token_len X <> 0 /\
  ri_display_len X <> 0 /\ bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true /\
  ((ri_i X =? 0) && (ri_o X =? 0)) = false.
Proof.
intros X H. unfold rbm_args, reac_box_name_c.bn_args_ok in H.
apply andb_true_iff in H as [H H9]. apply andb_true_iff in H as [H H8]. apply andb_true_iff in H as [H H7].
apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply negb_true_iff in H1, H2, H3, H4, H5, H6, H9. apply Z.eqb_neq in H1, H2, H3, H4, H5, H6.
repeat split; assumption.
Qed.
Lemma rbn9_NB_len : forall X : rbn_in, (length (rbm_NB X) <= 23)%nat.
Proof. intros X. unfold rbm_NB. rewrite length_firstn. lia. Qed.
Lemma rbn9_tok : forall X : rbn_in, rbm_tok X = 1.
Proof.
intros X. unfold rbm_tok, rbm_ovf, bn_TK.
pose proof (rbn9_tk_len false (rbm_NB X)). pose proof (rbn9_NB_len X).
destruct (23 <? Z.of_nat (length (bn_tk false (rbm_NB X)))) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.
Lemma rbn9_D9_len : forall X : rbn_in, rbm_args X ->
  Z.of_nat (length (rbm_D9 X)) =
    Z.of_nat (length (rbm_NB X)) + 8 + Z.of_nat (length (bn_dec (ri_i X) 1)) + Z.of_nat (length (bn_dec (ri_o X) 1)) /\
  Z.of_nat (length (rbm_D9 X)) <= 35.
Proof.
intros X HA. destruct (rbn9_args X HA) as (_ & _ & _ & _ & _ & _ & Hi & Ho & _).
pose proof (rbn9_dec_len _ Hi). pose proof (rbn9_dec_len _ Ho). pose proof (rbn9_NB_len X).
unfold rbm_D9. rewrite !length_app. cbn [length]. lia.
Qed.
Lemma rbn9_D9_ovf : forall X : rbn_in, rbm_args X ->
  rbm_ovf 47 (rbm_D9 X) = 0 /\ Z.min (Z.of_nat (length (rbm_D9 X))) 47 = Z.of_nat (length (rbm_D9 X)) /\
  firstn 47 (rbm_D9 X) = rbm_D9 X.
Proof.
intros X HA. destruct (rbn9_D9_len X HA) as [_ H]. unfold rbm_ovf.
split; [destruct (47 <? Z.of_nat (length (rbm_D9 X))) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]|].
split; [lia|]. apply firstn_all2. lia.
Qed.
Lemma rbn9_ovf01 : forall cap l, rbm_ovf cap l = 0 \/ rbm_ovf cap l = 1.
Proof. intros cap l. unfold rbm_ovf. destruct (cap <? Z.of_nat (length l)); [right | left]; reflexivity. Qed.
Lemma rbn9_acc : forall X : rbn_in, rbm_args X ->
  rbm_acc X = (rbm_ovf 23 (rbm_NM X) =? 0) && (Z.of_nat (length (rbm_NB X)) <? ri_name_len X) &&
    (Z.of_nat (length (rbm_TB X)) <? ri_token_len X) && (Z.of_nat (length (rbm_D9 X)) + 5 <? ri_display_len X).
Proof.
intros X HA. pose proof HA as HA'. destruct (rbn9_args X HA) as (_ & _ & _ & _ & _ & _ & Hi & Ho & Hz).
unfold rbm_acc, reac_box_name_c.bn_accept. unfold rbm_args in HA'. rewrite HA'.
unfold bn_ret. rewrite Hi, Ho, Hz. cbn [andb negb].
unfold rbm_ovf, rbm_TB, rbm_NB, rbm_D9, rbm_NB, rbm_NM.
destruct (Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X))) <=? 23) eqn:E.
- apply Z.leb_le in E.
  replace (23 <? Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)))) with false
    by (symmetry; apply Z.ltb_ge; lia).
  rewrite (firstn_all2 (n := 23%nat)) by lia.
  pose proof (rbn9_tk_len false (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X))) as T. unfold bn_TK.
  rewrite (firstn_all2 (n := 23%nat)) by lia.
  unfold bn_DP. rewrite !length_app. cbn [length]. cbn [Z.eqb andb].
  replace (Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) + (2 + (length (bn_dec (ri_i X) 1) +
    (6 + (length (bn_dec (ri_o X) 1) + 5)))))) with
    (Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) + (2 + (length (bn_dec (ri_i X) 1) +
    (6 + length (bn_dec (ri_o X) 1))))) + 5) by lia.
  reflexivity.
- apply Z.leb_gt in E.
  replace (23 <? Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)))) with true
    by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.
Lemma rbn9_acc_parts : forall X : rbn_in, rbm_args X -> rbm_ovf 23 (rbm_NM X) = 0 ->
  rbm_NB X = rbm_NM X /\ rbm_TB X = bn_TK (rbm_NM X) /\
  rbm_D9 X ++ [32; 111; 117; 116; 41] = bn_DP (rbm_NM X) (ri_i X) (ri_o X).
Proof.
intros X HA H0. unfold rbm_ovf in H0.
destruct (23 <? Z.of_nat (length (rbm_NM X))) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
assert (HNB : rbm_NB X = rbm_NM X) by (unfold rbm_NB; apply firstn_all2; lia).
split; [exact HNB|]. split.
- unfold rbm_TB. rewrite HNB. pose proof (rbn9_tk_len false (rbm_NM X)). unfold bn_TK. apply firstn_all2. lia.
- unfold rbm_D9, bn_DP. rewrite HNB. rewrite <- !app_assoc. reflexivity.
Qed.
Definition rbn9_kept (W : world SEGS) (m m' : word -> option byte) (Wr : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W) m a -> apresent (w_H W) m' a).
Lemma rbn9_kept_of_frame : forall E rs W (m m' : word -> option byte) (Wr : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> Wr a) -> rbn9_kept W m m' Wr.
Proof.
intros E rs W m m' Wr HF HG HW. split.
- intros a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. intros Hi. apply Hn, HW, Hi.
- intros a _ Hp. exact (apresent_grows _ _ _ _ HG Hp).
Qed.
Lemma rbn9_kept_trans : forall W m1 m2 m3 (Wr1 Wr2 : Z -> Prop),
  rbn9_kept W m1 m2 Wr1 -> rbn9_kept W m2 m3 Wr2 -> rbn9_kept W m1 m3 (fun a => Wr1 a \/ Wr2 a).
Proof.
intros W m1 m2 m3 Wr1 Wr2 [K1 P1] [K2 P2]. split.
- intros a Ha Hn. rewrite (K2 a Ha) by tauto. apply K1; tauto.
- intros a Ha Hp. apply P2, P1; assumption.
Qed.
Lemma rbn9_kept_mono : forall W m m' (Wr Wr' : Z -> Prop),
  rbn9_kept W m m' Wr -> (forall a, Wr a -> Wr' a) -> rbn9_kept W m m' Wr'.
Proof. intros W m m' Wr Wr' [K P] H. split; [intros a Ha Hn; apply K; [exact Ha | intros Hw; apply Hn, H, Hw] | exact P]. Qed.
Lemma rbn9_kept_refl : forall W m (Wr : Z -> Prop), rbn9_kept W m m Wr.
Proof. intros W m Wr. split; [reflexivity | intros a _ Hp; exact Hp]. Qed.
Lemma rbn9_kept_val : forall W m m' (Wr : Z -> Prop) a n v,
  rbn9_kept W m m' Wr -> (forall i, 0 <= i < Z.of_nat n -> ~ Wr (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' Wr a n v [K _] Hn H0 H1 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [|exact Hv].
intros i Hi. apply K; [lia | apply Hn; lia].
Qed.
Lemma rbn9_kept_garr : forall W m m' (Wr : Z -> Prop) a l,
  rbn9_kept W m m' Wr -> (forall i, 0 <= i < Z.of_nat (length l) -> ~ Wr (a + i)) -> 0 <= a ->
  a + Z.of_nat (length l) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' Wr a l HK Hn H0 H1 Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (rbn9_kept_val W m m' Wr _ 1 _ HK); [| lia | lia | exact Hv].
intros i Hi. replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hn. lia.
Qed.
Lemma rbn9_kept_step : forall E rs W (m1 m2 m3 : word -> option byte) (Wr : Z -> Prop),
  rbn9_kept W m1 m2 Wr -> frame_of E rs (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) ->
  mem_grows (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) -> (forall a, in_wrange E rs a -> Wr a) ->
  rbn9_kept W m1 m3 Wr.
Proof.
intros E rs W m1 m2 m3 Wr K HF HG HW.
apply (rbn9_kept_mono W m1 m3 (fun a => Wr a \/ Wr a)); [|tauto].
exact (rbn9_kept_trans W m1 m2 m3 Wr Wr K (rbn9_kept_of_frame E rs W m2 m3 Wr HF HG HW)).
Qed.
Definition rbn9b_r0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 184 144 148
    [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
     YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0));
     YP09.mkChunk 40 (CVal 8 (SLit 1)); YP09.mkChunk 48 (CVal 8 (SOff 19 128));
     YP09.mkChunk 56 (CVal 8 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 37 0));
     YP09.mkChunk 72 (CVal 8 (SOff 19 0)); YP09.mkChunk 144 (CVal 4 (SLit 0)); YP09.mkChunk 176 (CVal 4 (SLit 0))].
Definition rbn9b_regions : smem := [ rbn9b_r0; YP09.mkRegion (Some 38%nat) 0 1 0 1 [] ].
Definition rbn9b_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0); (38%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] []
    [ (SAlu ALU_ADD (SOff 20 0) (SOff 23 0), SOff 38 0) ].
Definition ss_rbn9b : sstate := mkSS (AF_reac_box_name + RBN_L7X) sr_atoms rbn9b_regions None rbn9b_facts.
Definition rbn9b_SH : list shent := [ mkSHE 38 0 1 ].
Definition rbn9b_Bx : sv := SOff 22 0.
Definition rbn9b_extra (d nm tk tkl dl nml t : Z) : list word := map (Z_to_bv 64) [d; nm; tk; tkl; dl; nml; t].
Definition ERB9b (regs : bvmap 5 word) (d nm tk tkl dl nml t : Z) : env := Eimg (Ereg regs (rbn9b_extra d nm tk tkl dl nml t)).
Lemma regs_ok_ERB9b : forall regs d nm tk tkl dl nml t, regs_ok (ERB9b regs d nm tk tkl dl nml t) sr_atoms regs.
Proof.
intros. unfold ERB9b. apply (regs_ok_agree 32 (Ereg regs (rbn9b_extra d nm tk tkl dl nml t))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9b_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc (A F nF d nm tk tkl dl nml : Z),
  getr regs 9 = w64 A -> getr regs 19 = w64 F -> getr regs 20 = w64 (F + 192) -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 23 = w64 nF ->
  A mod 32 = 0 -> 2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> F + 512 <= A ->
  4096 <= F -> F + 512 <= 2 ^ 47 - 1 -> 0 <= nF < 48 ->
  0 <= d < 2 ^ 64 -> 0 <= nm < 2 ^ 64 -> 0 <= tk < 2 ^ 64 -> 0 <= tkl < 2 ^ 64 -> 0 <= dl < 2 ^ 64 -> 0 <= nml < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 d -> val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 nm ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 8 tk -> val_mem SEGS (mrestrict (w_H W) memc) (A + 32) 8 tkl ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 40) 8 1 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 48) 8 (F + 128) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 56) 8 dl -> val_mem SEGS (mrestrict (w_H W) memc) (A + 64) 8 nml ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 72) 8 F -> val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 176) 4 0 ->
  (forall a, A + 144 <= a < A + 148 -> apresent (w_H W) memc a) -> apresent (w_H W) memc (F + 192 + nF) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (F + 192 + nF) 1 ->
  ~ (SHADOW_OFF <= F + 192 + nF < SHADOW_OFF + 17592186044416) ->
  st_ok_pi SEGS VAL (ERB9b regs d nm tk tkl dl nml (F + 192 + nF)) ss_rbn9b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7X))) memc (seg_rom SEGS))) /\
  sh_ok SEGS rbn9b_Bx rbn9b_SH (ERB9b regs d nm tk tkl dl nml (F + 192 + nF)) (mrestrict (w_H W) memc).
Proof.
intros W regs memc A F nF d nm tk tkl dl nml H9 H19 H20 H22 H23 HA32 HAlo HAhi HFA HF0 HF1 HnF
  Rd Rnm Rtk Rtkl Rdl Rnml M8 M16 M24 M32 M40 M48 M56 M64 M72 M144 M176 HP144 HPT HRT HTsh.
rewrite restrict_mkst_fx.
set (E := ERB9b regs d nm tk tkl dl nml (F + 192 + nF)).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rbn9b_extra d nm tk tkl dl nml (F + 192 + nF))) m)
  by (intros m Hm; subst E; unfold ERB9b; apply Eimg_low; exact Hm).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9b; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (rbn9b_extra d nm tk tkl dl nml (F + 192 + nF)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. cbn [Nat.add nth rbn9b_extra map] in E32, E33, E34, E35, E36, E37, E38. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (F + 192)) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 nF) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (CH : forall off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + off) 8 v -> YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) A (YP09.mkChunk off (CVal 8 e))).
{ intros off e v He Hv Hm. apply (chunk_ok_val SEGS E _ A off 8 e v He); [zside | zside | exact Hm]. }
split.
- unfold ss_rbn9b, rbn9b_regions, rbn9b_r0. apply pa_entry_st_ok_full.
  + apply regs_ok_ERB9b.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (apresent_writable SEGS). apply HP144. lia.
      -- repeat apply Forall_cons; try apply Forall_nil.
         ++ apply (CH 8 _ d); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M8].
         ++ apply (CH 16 _ nm); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M16].
         ++ apply (CH 24 _ tk); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M24].
         ++ apply (CH 32 _ tkl); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M32].
         ++ apply (CH 40 _ 1); [reflexivity | lia | exact M40].
         ++ apply (CH 48 _ (F + 128)); [|lia | exact M48].
            cbn [sv_denot]. rewrite E19, unsigned_lit_small by lia. reflexivity.
         ++ apply (CH 56 _ dl); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M56].
         ++ apply (CH 64 _ nml); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M64].
         ++ apply (CH 72 _ F); [cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M72].
         ++ apply (chunk_ok_val SEGS E _ A 144 4 (SLit 0) 0); [reflexivity | lia | zside | exact M144].
         ++ apply (chunk_ok_val SEGS E _ A 176 4 (SLit 0) 0); [reflexivity | lia | zside | exact M176].
    * rewrite (VB 38%nat (F + 192 + nF) E38) by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (F + 192 + nF + o) with (F + 192 + nF) by lia. apply (apresent_writable SEGS). exact HPT.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat A E9) by lia. rewrite (VB 38%nat (F + 192 + nF) E38) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
  + unfold rbn9b_facts. split; [|split].
    * cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
      rewrite E9, E22, E38, !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
      split; [split; [lia|]; split; [change (2 ^ 5) with 32; exact HA32 | lia]|].
      split; [split; [unfold SB, SHADOW_OFF; lia|]; split; [apply Z.mod_1_r | lia]|].
      split; [split; [lia|]; split; [apply Z.mod_1_r | lia]|]. exact I.
    * exact I.
    * cbn [f_alias alias_ok sv_denot]. split; [|exact I].
      rewrite E20, E23, E38. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. rewrite alu_add_small by (unfold YP0m.M64; lia). reflexivity.
- unfold rbn9b_SH, sh_ok. apply Forall_cons; [|apply Forall_nil].
  assert (HU : U E (SOff 38 0) = F + 192 + nF) by (shent_U_norm; reflexivity).
  assert (HUB : U E rbn9b_Bx = SHADOW_OFF) by (unfold rbn9b_Bx; shent_U_norm; reflexivity).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU, HUB. split.
  + replace (F + 192 + nF + 0) with (F + 192 + nF) by lia. replace (1 - 0) with 1 by lia. exact HRT.
  + intros a Ha. cbn [Z.min Z.max] in Ha. intros Hb. apply HTsh. lia.
Qed.
Definition rbn9_same (regs regs2 : bvmap 5 word) (l : list Z) : Prop :=
  forall r, In r l -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition RBN9_TAIL : Z := 0x8bc.
Definition RBN9_ACC : Z := 0x888.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Definition rbn9_jc STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
  (A F nF : Z) (regs2 : bvmap 5 word) mem2 mdc2 : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 mdc2 k /\
  rbn9_same regs regs2 [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] /\
  rbn9_kept W memc mem2 (fun a => A + 144 <= a < A + 148 \/ a = F + 192 + nF) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (F + 192 + nF) 1 0 /\
  val_mem SEGS (mrestrict (w_H W) mem2) (A + 144) 4 0.
Ltac r9ewu := cbn [ew ewset extK Nat.eqb];
  lazymatch goal with |- bv_unsigned (ew ?E ?n) = _ => lazymatch goal with Ex : ew E n = Z_to_bv 64 _ |- _ => rewrite Ex end end;
  rewrite unsigned_lit_small by lia; reflexivity.
Ltac r9awr HW144 HWT :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | r9ewu |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply HW144; lia |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 38%nat); [reflexivity | r9ewu |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; lazymatch type of HWT with awr_byte _ _ _ _ _ _ _ ?t => replace a with t by lia end; exact HWT |];
  apply awr_ok_nil.
Ltac r9wr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbv beta;
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    cbn [ew ewset extK Nat.eqb] in Hr;
    repeat match goal with Ex : ew _ _ = Z_to_bv 64 _ |- _ => progress rewrite Ex in Hr end;
    rewrite ?unsigned_lit_small in Hr by lia; lia |]); destruct Hin.
Ltac r9hc :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
  cbn [branch_taken sv_denot ew ewset extK Nat.eqb] in Hc; unfold bv_ltu in Hc;
  repeat match goal with Ex : ew ?E ?n = Z_to_bv 64 _ |- _ => progress rewrite Ex in Hc end;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc; rewrite ?unsigned_lit_small in Hc by lia end.
Ltac r9step KP :=
  lazymatch goal with HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ =>
  let K2 := fresh "KP" in
  pose proof (rbn9_kept_step _ _ _ _ _ _ _ KP HFr HG ltac:(r9wr)) as K2;
  clear KP HFr HG; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end); rename K2 into KP end.
Ltac r9same EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- getr _ (Z_to_bv 5 ?z) = _ =>
      let R := fresh "R" in prreg HS (Z_to_bv 5 z) R; rewrite R; apply EE; reflexivity end |]);
  destruct Hr.
Lemma rbn9_pc : forall (W : world SEGS) regs mem md Q p q, p = q ->
  SRr SEGS W (cfg_at SEGS p regs mem md) Q ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 q) mem (seg_rom SEGS)) md) Q.
Proof. intros W regs mem md Q p q -> H. exact H. Qed.
Ltac r9jc HS HJ KP EE E12 :=
  split; [exact HJ|]; split; [r9same EE|]; split; [exact KP|];
  let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in let V := fresh "V" in
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0; pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1;
  cbn [ms_mem restrict] in HR0, HR1;
  split;
  [ pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 1 (SLit 0) 0 HR1 ltac:(r9ewu) ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as V;
    rewrite Z.add_0_r in V; exact V
  | pose proof (field_of_region _ _ _ _ _ _ _ _ _ 144 4 (SOff 12 0) 0 HR0 ltac:(r9ewu) ltac:(left; reflexivity)
      ltac:(cbn [sv_denot ew ewset extK Nat.eqb]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia) ltac:(lia)) as V;
    exact V ].
Ltac r9go HS off :=
  pmkst HS;
  lazymatch goal with |- SRr _ ?W (mkCfg (mkst (ms_regs ?msx) _ (ms_mem ?msx) _) ?mdx) ?Q =>
  apply (rbn9_pc W (ms_regs msx) (ms_mem msx) mdx Q (BASE + AF_reac_box_name + off));
  [unfold AF_reac_box_name, RBN9_TAIL, RBN9_ACC; lia|] end.
Ltac r9finR HS HJ KP K EE E12 :=
  r9go HS RBN9_TAIL;
  apply K; [ r9jc HS HJ KP EE E12
           | let R := fresh "R" in prreg HS (21%bv : bv 5) R; rewrite R; unfold w64; apply bv_eq;
             rewrite !Z_to_bv_unsigned; reflexivity
           | ].
Ltac r9finA HS HJ KP K EE E12 :=
  r9go HS RBN9_ACC;
  apply K; [ r9jc HS HJ KP EE E12 | ].
Lemma rbn9_checks : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A F nF d nm tk tkl dl nml lnb ovn ltb : Z) Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> getr regs 19 = w64 F -> getr regs 20 = w64 (F + 192) -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 23 = w64 nF -> getr regs 12 = w64 0 -> getr regs 24 = w64 lnb -> getr regs 25 = w64 ovn -> getr regs 26 = w64 ltb ->
  A mod 32 = 0 -> 2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> F + 512 <= A ->
  4096 <= F -> F + 512 <= 2 ^ 47 - 1 -> 0 <= nF < 48 -> (ovn = 0 \/ ovn = 1) -> 0 <= lnb < 2 ^ 64 -> 0 <= ltb < 2 ^ 64 ->
  0 <= d < 2 ^ 64 -> 0 <= nm < 2 ^ 64 -> 0 <= tk < 2 ^ 64 -> 0 <= tkl < 2 ^ 64 -> 0 <= dl < 2 ^ 64 -> 0 <= nml < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 d -> val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 nm ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 8 tk -> val_mem SEGS (mrestrict (w_H W) memc) (A + 32) 8 tkl ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 40) 8 1 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 48) 8 (F + 128) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 56) 8 dl -> val_mem SEGS (mrestrict (w_H W) memc) (A + 64) 8 nml ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 72) 8 F -> val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 176) 4 0 ->
  (forall a, A + 144 <= a < A + 148 -> apresent (w_H W) memc a) -> apresent (w_H W) memc (F + 192 + nF) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (F + 192 + nF) 1 ->
  ~ (SHADOW_OFF <= F + 192 + nF < SHADOW_OFF + 17592186044416) ->
  (forall a, A + 144 <= a < A + 148 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (F + 192 + nF) ->
  (forall regs2 mem2 mdc2, rbn9_jc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A F nF regs2 mem2 mdc2 ->
     getr regs2 21 = w64 (-1) -> ~ (ovn = 0 /\ nF < dl /\ lnb < nml /\ ltb < tkl) ->
     SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN9_TAIL) regs2 mem2 mdc2) Q) ->
  (forall regs2 mem2 mdc2, rbn9_jc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A F nF regs2 mem2 mdc2 ->
     ovn = 0 /\ nF < dl /\ lnb < nml /\ ltb < tkl ->
     SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN9_ACC) regs2 mem2 mdc2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN_L7X) regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A F nF d nm tk tkl dl nml lnb ovn ltb Q HJ
  H9 H19 H20 H22 H23 H12 H24 H25 H26 HA32 HAlo HAhi HFA HF0 HF1 HnF Hovn Rlnb Rltb Rd Rnm Rtk Rtkl Rdl Rnml
  M8 M16 M24 M32 M40 M48 M56 M64 M72 M144 M176 HP144 HPT HRT HTsh HW144 HWT KREF KACC.
destruct (rbn9b_entry W regs memc A F nF d nm tk tkl dl nml H9 H19 H20 H22 H23 HA32 HAlo HAhi HFA HF0 HF1 HnF
  Rd Rnm Rtk Rtkl Rdl Rnml M8 M16 M24 M32 M40 M48 M56 M64 M72 M144 M176 HP144 HPT HRT HTsh) as [HS SHOK].
set (E := ERB9b regs d nm tk tkl dl nml (F + 192 + nF)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9b; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9b; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (rbn9b_extra d nm tk tkl dl nml (F + 192 + nF)) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ERB9b; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. cbn [Nat.add nth rbn9b_extra map] in E35, E36, E37, E38. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E12 : ew E 12 = Z_to_bv 64 0) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E23 : ew E 23 = Z_to_bv 64 nF) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 lnb) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 ovn) by (rewrite (EE 25%nat 25%bv eq_refl); exact H25).
assert (E26 : ew E 26 = Z_to_bv 64 ltb) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
clearbody E.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (rbn9_kept_refl W memc (fun a => A + 144 <= a < A + 148 \/ a = F + 192 + nF)) as KP.
unfold cfg_at. change (w64 (BASE + AF_reac_box_name + RBN_L7X)) with (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_L7X)).
rewrite <- Z.add_assoc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN9_TAIL).
{ r9awr HW144 HWT. }
r9step KP.
psrr_branch_pi RUNP BR HS; r9hc.
- assert (Hov1 : ovn = 1) by (destruct Hovn as [-> | ->]; [vm_compute in Hc; discriminate | reflexivity]). clear Hc.
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
  r9step KP. r9finR HS HJ KP KREF EE E12. lia.
- assert (Hov0 : ovn = 0) by (destruct Hovn as [-> | ->]; [reflexivity | vm_compute in Hc; discriminate]). clear Hc.
  paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
  r9step KP.
  psrr_branch_pi RUNP BR HS; r9hc.
  + apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
    r9step KP. r9finR HS HJ KP KREF EE E12. lia.
  + apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc2.
    paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
    r9step KP.
    psrr_branch_pi RUNP BR HS; r9hc.
    * apply negb_true_iff, Z.ltb_ge in Hc.
      paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
      r9step KP. r9finR HS HJ KP KREF EE E12. lia.
    * apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc3.
      paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
      r9step KP.
      psrr_branch_pi RUNP BR HS; r9hc.
      { vm_compute in Hc. discriminate Hc. }
      clear Hc.
      paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
      r9step KP.
      psrr_branch_pi RUNP BR HS; r9hc.
      -- apply negb_true_iff, Z.ltb_ge in Hc.
         paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_TAIL). { r9awr HW144 HWT. }
         r9step KP. r9finR HS HJ KP KREF EE E12. lia.
      -- apply negb_false_iff, Z.ltb_lt in Hc.
         paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN9_ACC). { r9awr HW144 HWT. }
         r9step KP. r9finA HS HJ KP KACC EE E12. lia.
Qed.
Definition rbn9d_regions : smem :=
  [ YP09.mkRegion (Some 18%nat) 0 64 4 30
      [YP09.mkChunk 4 (CVal 1 (SLit 5)); YP09.mkChunk 5 (CVal 1 (SLit 242)); YP09.mkChunk 6 (CVal 1 (SLit 242)); YP09.mkChunk 7 (CVal 1 (SLit 242)); YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0)); YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 11 (CVal 1 (SLit 242)); YP09.mkChunk 12 (CVal 1 (SLit 242)); YP09.mkChunk 13 (CVal 1 (SLit 242)); YP09.mkChunk 14 (CVal 1 (SLit 242)); YP09.mkChunk 15 (CVal 1 (SLit 242)); YP09.mkChunk 16 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 18 (CVal 1 (SLit 0)); YP09.mkChunk 19 (CVal 1 (SLit 242)); YP09.mkChunk 20 (CVal 1 (SLit 242)); YP09.mkChunk 21 (CVal 1 (SLit 242)); YP09.mkChunk 22 (CVal 1 (SLit 242)); YP09.mkChunk 23 (CVal 1 (SLit 242)); YP09.mkChunk 24 (CVal 1 (SLit 0)); YP09.mkChunk 25 (CVal 1 (SLit 0)); YP09.mkChunk 26 (CVal 1 (SLit 0)); YP09.mkChunk 27 (CVal 1 (SLit 0)); YP09.mkChunk 28 (CVal 1 (SLit 0)); YP09.mkChunk 29 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 9%nat) 72 80 0 0 [YP09.mkChunk 72 (CVal 8 (SOff 19 0))] ].
Definition ss_rbn9d : sstate := mkSS (AF_reac_box_name + RBN9_TAIL) sr_atoms rbn9d_regions None (mkFacts [] [] []).
Definition ERB9d (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma regs_ok_ERB9d : forall regs, regs_ok (ERB9d regs) sr_atoms regs.
Proof.
intros. unfold ERB9d. apply (regs_ok_agree 32 (Ereg regs [])).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9d_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc (A F SH : Z),
  getr regs 9 = w64 A -> getr regs 18 = w64 SH -> getr regs 19 = w64 F ->
  0 <= A -> A + 80 <= 2 ^ 64 -> 0 <= SH -> SH + 64 <= A + 72 -> 0 <= F < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 72) 8 F ->
  (forall a, SH + 4 <= a < SH + 30 -> apresent (w_H W) memc a) ->
  (forall j, 4 <= j < 30 -> val_mem SEGS (mrestrict (w_H W) memc) (SH + j) 1 (nth (Z.to_nat j) (rbn_sh true true true true) 0)) ->
  st_ok_pi SEGS VAL (ERB9d regs) ss_rbn9d
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN9_TAIL))) memc (seg_rom SEGS))).
Proof.
intros W regs memc A F SH H9 H18 H19 HA0 HA1 HS0 HSA HF M72 HP HSH.
rewrite restrict_mkst_fx.
set (E := ERB9d regs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9d; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SH) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold ss_rbn9d, rbn9d_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9d.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 18%nat SH E18) by lia. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
    * repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?j (CVal 1 (SLit ?v))) =>
        apply (chunk_ok_val SEGS E _ SH j 1 (SLit v) v); [reflexivity | lia | zside | exact (HSH j ltac:(lia))] end.
  + rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A 72 8 _ F); [cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M72].
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat A E9) by lia. rewrite (VB 18%nat SH E18) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn9_byte_lit : forall E m n b lo hi wlo whi cs od v w,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> byte_of_word (Z_to_bv 64 v) 0 = Z_to_bv 8 (le_byte w 1 0) ->
  val_mem SEGS m (b + od) 1 w.
Proof.
intros E m n b lo hi wlo whi cs od v w (_ & _ & _ & Hcs) Hn Hc Hv k Hk.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.r_base base_val YP09.c_off YP09.c_val] in Hb1, Hb2. rewrite Hn in Hb1, Hb2.
destruct k as [|k]; [|lia]. rewrite Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2.
cbn [YP09.cbyte sv_denot] in Hb1. injection Hb1 as <-. f_equal. exact Hv.
Qed.
Lemma rbn9_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A F SH : Z) Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> getr regs 18 = w64 SH -> getr regs 19 = w64 F ->
  0 <= A -> A + 80 <= 2 ^ 64 -> 0 <= SH -> SH + 64 <= A + 72 -> 0 <= F < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 72) 8 F ->
  (forall a, SH + 4 <= a < SH + 30 -> apresent (w_H W) memc a) ->
  (forall a, SH + 4 <= a < SH + 30 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall j, 4 <= j < 30 -> val_mem SEGS (mrestrict (w_H W) memc) (SH + j) 1 (nth (Z.to_nat j) (rbn_sh true true true true) 0)) ->
  (forall regs2 mem2 mdc2,
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 mdc2 k ->
     rbn9_same regs regs2 [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27] ->
     getr regs2 26 = w64 F ->
     rbn9_kept W memc mem2 (fun a => SH + 4 <= a < SH + 30) ->
     (forall j, 4 <= j < 30 ->
        val_mem SEGS (mrestrict (w_H W) mem2) (SH + j) 1 (nth (Z.to_nat j) (rbn_sh false false false false) 0)) ->
     SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN_P10) regs2 mem2 mdc2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN9_TAIL) regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A F SH Q HJ H9 H18 H19 HA0 HA1 HS0 HSA HF M72 HP HW HSH K.
pose proof (rbn9d_entry W regs memc A F SH H9 H18 H19 HA0 HA1 HS0 HSA HF M72 HP HSH) as HS.
set (E := ERB9d regs) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9d; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9d; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SH) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
clearbody E.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (rbn9_kept_refl W memc (fun a => SH + 4 <= a < SH + 30)) as KP.
unfold cfg_at. change (w64 (BASE + AF_reac_box_name + RBN9_TAIL)) with (Z_to_bv 64 (BASE + AF_reac_box_name + RBN9_TAIL)).
rewrite <- Z.add_assoc.
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_P10).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat); [reflexivity | r9ewu |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply HW; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
r9step KP.
pmkst HS.
lazymatch goal with |- SRr _ ?W (mkCfg (mkst (ms_regs ?msx) _ (ms_mem ?msx) _) ?mdx) ?Q =>
  apply (rbn9_pc W (ms_regs msx) (ms_mem msx) mdx Q (BASE + AF_reac_box_name + RBN_P10));
  [unfold AF_reac_box_name, RBN_P10; lia|] end.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
apply K.
- exact HJ.
- r9same EE.
- let R := fresh "R" in prreg HS (26%bv : bv 5) R; rewrite R; rewrite E19; reflexivity.
- exact KP.
- intros j Hj. assert (Hjj : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/
    j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/
    j = 26 \/ j = 27 \/ j = 28 \/ j = 29) by lia.
  repeat (destruct Hjj as [-> | Hjj];
    [eapply (rbn9_byte_lit _ _ _ _ _ _ _ _ _ _ _ _ HR0 ltac:(r9ewu));
     [cbn [In]; repeat (first [left; reflexivity | right]) | apply bv_eq; vm_compute; reflexivity] |]).
  subst j. eapply (rbn9_byte_lit _ _ _ _ _ _ _ _ _ _ _ _ HR0 ltac:(r9ewu));
  [cbn [In]; repeat (first [left; reflexivity | right]) | apply bv_eq; vm_compute; reflexivity].
Qed.
Definition rbn9_cpy (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (m : word -> option byte) (A d x n : Z) : Prop :=
  0 <= n < 2 ^ 32 /\ 0 <= d /\ d + n <= 2 ^ 63 /\
  (forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (A - ESTACK <= a < A)) /\
  amem_range d n /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF d n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) d n) /\
  0 <= x /\ x + n <= 2 ^ 63 /\
  (forall a, x <= a < x + n -> aview SEGS (w_H W) m a <> None /\ ~ (A - ESTACK <= a < A)) /\
  (d + n <= x \/ x + n <= d) /\ amem_range x n /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) x n).
Lemma rbn9_amem_sh : forall y p n, amem_range p n -> 0 <= p -> p <= y < p + n ->
  kLowMemEnd <= shadow_of_addr SHADOW_OFF y < kHighMemBeg.
Proof.
intros y p n Ham Hp Hy. unfold shadow_of_addr.
pose proof (Z.div_mod y 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as M1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_amem_hull : forall s p n, amem_range p n -> 0 <= p -> 0 < n ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighMemBeg.
Proof.
intros s p n Ham Hp Hn Hs. unfold shadow_addr in Hs.
pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_amem_out : forall y p n, amem_range p n -> 0 <= p -> kLowMemEnd <= y < kHighMemBeg -> ~ (p <= y < p + n).
Proof. intros y p n Ham Hp Hy Hc. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. Qed.
Lemma rbn9_cpy_kept : forall STK sp0 FP ly S own lyc Sc W m m' A d x n d' n',
  rbn9_cpy STK sp0 FP ly S own lyc Sc W m A d x n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d' <= a < d' + n') -> ~ (A - ESTACK <= a < A) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  amem_range d' n' -> 0 <= d' -> (x + n <= d' \/ d' + n' <= x) -> kHighMemBeg <= A - ESTACK ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W m' A d x n.
Proof.
intros STK sp0 FP ly S own lyc Sc W m m' A d x n d' n'
  (Hn & Hd0 & Hdn & Hdw & Hdam & Hdra & Hdhv & Hx0 & Hxn & Hxs & Hdx & Hxam & Hxra & Hxhv) HK Ham' Hd0' Hdis HA.
assert (KS : forall y, kLowMemEnd <= y < kHighMemBeg -> aview SEGS (w_H W) m' y = aview SEGS (w_H W) m y).
{ intros y Hy. apply HK; [unfold kLowMemEnd, kHighMemBeg in Hy; lia | exact (rbn9_amem_out y d' n' Ham' Hd0' Hy) | lia]. }
split; [exact Hn|]. split; [exact Hd0|]. split; [exact Hdn|]. split; [exact Hdw|]. split; [exact Hdam|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact Hdra].
  intros y Hy. apply KS. exact (rbn9_amem_sh y d n Hdam Hd0 Hy). }
split.
{ intros Hp s Hs. rewrite (KS s (rbn9_amem_hull s d n Hdam Hd0 Hp Hs)). exact (Hdhv Hp s Hs). }
split; [exact Hx0|]. split; [exact Hxn|].
split.
{ intros a Ha. destruct (Hxs a Ha) as [Hv Hw]. split; [|exact Hw]. rewrite HK; [exact Hv | lia | lia | exact Hw]. }
split; [exact Hdx|]. split; [exact Hxam|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact Hxra].
  intros y Hy. apply KS. exact (rbn9_amem_sh y x n Hxam Hx0 Hy). }
intros Hp s Hs. rewrite (KS s (rbn9_amem_hull s x n Hxam Hx0 Hp Hs)). exact (Hxhv Hp s Hs).
Qed.
Lemma rbn9_cpy_kept2 : forall STK sp0 FP ly S own lyc Sc W m m' A d x n (Wr : Z -> Prop),
  rbn9_cpy STK sp0 FP ly S own lyc Sc W m A d x n -> rbn9_kept W m m' Wr ->
  (forall a, Wr a -> ~ (kLowMemEnd <= a < kHighMemBeg)) -> (forall a, x <= a < x + n -> ~ Wr a) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W m' A d x n.
Proof.
intros STK sp0 FP ly S own lyc Sc W m m' A d x n Wr
  (Hn & Hd0 & Hdn & Hdw & Hdam & Hdra & Hdhv & Hx0 & Hxn & Hxs & Hdx & Hxam & Hxra & Hxhv) [HK _] HWb HWx.
assert (KS : forall y, kLowMemEnd <= y < kHighMemBeg -> aview SEGS (w_H W) m' y = aview SEGS (w_H W) m y).
{ intros y Hy. apply HK; [unfold kLowMemEnd, kHighMemBeg in Hy; lia | intros Hw; exact (HWb y Hw Hy)]. }
split; [exact Hn|]. split; [exact Hd0|]. split; [exact Hdn|]. split; [exact Hdw|]. split; [exact Hdam|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact Hdra].
  intros y Hy. apply KS. exact (rbn9_amem_sh y d n Hdam Hd0 Hy). }
split.
{ intros Hp s Hs. rewrite (KS s (rbn9_amem_hull s d n Hdam Hd0 Hp Hs)). exact (Hdhv Hp s Hs). }
split; [exact Hx0|]. split; [exact Hxn|].
split.
{ intros a Ha. destruct (Hxs a Ha) as [Hv Hw]. split; [|exact Hw]. rewrite HK; [exact Hv | lia | exact (HWx a Ha)]. }
split; [exact Hdx|]. split; [exact Hxam|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact Hxra].
  intros y Hy. apply KS. exact (rbn9_amem_sh y x n Hxam Hx0 Hy). }
intros Hp s Hs. rewrite (KS s (rbn9_amem_hull s x n Hxam Hx0 Hp Hs)). exact (Hxhv Hp s Hs).
Qed.
Lemma rbn9_kept_call : forall (W : world SEGS) (m1 m2 m3 : word -> option byte) (Wr : Z -> Prop) d n A,
  rbn9_kept W m1 m2 Wr ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (A - ESTACK <= a < A) ->
     aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
  (forall a, apresent (w_H W) m2 a -> apresent (w_H W) m3 a) ->
  (forall a, d <= a < d + n -> Wr a) -> (forall a, A - ESTACK <= a < A -> Wr a) ->
  rbn9_kept W m1 m3 Wr.
Proof.
intros W m1 m2 m3 Wr d n A [K P] HE HP H1 H2. split.
- intros a Ha Hn. rewrite HE; [apply K; [exact Ha | exact Hn] | exact Ha | |]; intros Hc; apply Hn; auto.
- intros a Ha Hp. apply HP, P; assumption.
Qed.
Lemma rbn9_kept_one : forall (W : world SEGS) (m2 m3 : word -> option byte) d n A,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (A - ESTACK <= a < A) ->
     aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
  (forall a, apresent (w_H W) m2 a -> apresent (w_H W) m3 a) ->
  rbn9_kept W m2 m3 (fun a => d <= a < d + n \/ A - ESTACK <= a < A).
Proof. intros W m2 m3 d n A HE HP. split; [intros a Ha Hn; apply HE; [exact Ha | | ]; intros Hc; apply Hn; tauto | intros a _ Hp; exact (HP a Hp)]. Qed.
Lemma rbn9_cp_run : forall (W : world SEGS) (m1 m2 memc : word -> option byte) d x n,
  (forall j, 0 <= j < n -> aview SEGS (w_H W) m1 (d + j) = aview SEGS (w_H W) memc (x + j)) ->
  rbn9_kept W m1 m2 (fun _ => False) -> 0 <= d -> d + n <= 2 ^ 64 ->
  forall j, 0 <= j < n -> aview SEGS (w_H W) m2 (d + j) = aview SEGS (w_H W) memc (x + j).
Proof. intros W m1 m2 memc d x n H [K _] Hd Hdn j Hj. rewrite (K (d + j) ltac:(lia) (fun c => c)). apply H, Hj. Qed.
Lemma rbn9_cp_call : forall (W : world SEGS) (m1 m2 memc : word -> option byte) d x n d' n' A,
  (forall j, 0 <= j < n -> aview SEGS (w_H W) m1 (d + j) = aview SEGS (w_H W) memc (x + j)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d' <= a < d' + n') -> ~ (A - ESTACK <= a < A) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (d + n <= d' \/ d' + n' <= d) -> (forall j, 0 <= j < n -> ~ (A - ESTACK <= d + j < A)) ->
  0 <= d -> d + n <= 2 ^ 64 ->
  forall j, 0 <= j < n -> aview SEGS (w_H W) m2 (d + j) = aview SEGS (w_H W) memc (x + j).
Proof.
intros W m1 m2 memc d x n d' n' A H HE Hdd Hw Hd Hdn j Hj.
rewrite (HE (d + j) ltac:(lia) ltac:(lia) (Hw j Hj)). apply H, Hj.
Qed.
Definition rbn9c_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 8 56 0 0
      [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
       YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 19 128))] ].
Definition ss_rbn9c : sstate := mkSS (AF_reac_box_name + RBN9_ACC) sr_atoms rbn9c_regions None (mkFacts [] [] []).
Definition ERB9c (regs : bvmap 5 word) (d3 d1 d2 : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [d3; d1; d2])).
Lemma regs_ok_ERB9c : forall regs d3 d1 d2, regs_ok (ERB9c regs d3 d1 d2) sr_atoms regs.
Proof.
intros. unfold ERB9c. apply (regs_ok_agree 32 (Ereg regs (map (Z_to_bv 64) [d3; d1; d2]))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9c_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc (A F d1 d2 d3 : Z),
  getr regs 9 = w64 A -> getr regs 19 = w64 F -> 0 <= A -> A + 56 <= 2 ^ 64 -> 0 <= F -> F + 128 < 2 ^ 64 ->
  0 <= d1 < 2 ^ 64 -> 0 <= d2 < 2 ^ 64 -> 0 <= d3 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 d3 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 d1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 8 d2 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 48) 8 (F + 128) ->
  st_ok_pi SEGS VAL (ERB9c regs d3 d1 d2) ss_rbn9c
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN9_ACC))) memc (seg_rom SEGS))).
Proof.
intros W regs memc A F d1 d2 d3 H9 H19 HA0 HA1 HF0 HF1 R1 R2 R3 M8 M16 M24 M48.
rewrite restrict_mkst_fx.
set (E := ERB9c regs d3 d1 d2).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9c; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [d3; d1; d2]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ERB9c; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth map] in E32, E33, E34. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
unfold ss_rbn9c, rbn9c_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9c.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ A 8 8 _ d3); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M8].
  + apply (chunk_ok_val SEGS E _ A 16 8 _ d1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M16].
  + apply (chunk_ok_val SEGS E _ A 24 8 _ d2); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M24].
  + apply (chunk_ok_val SEGS E _ A 48 8 _ (F + 128)); [cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; reflexivity | zside | zside | exact M48].
- cbn [pairwise_disjoint]. split; exact I.
- split; [exact I|]. split; exact I.
Qed.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
Ltac r9norm H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val sv_denot ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in H;
  repeat (match goal with Ex : ew ?E ?n = Z_to_bv 64 _ |- _ => progress rewrite Ex in H end);
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H; rewrite ?unsigned_lit_small in H by lia.
Ltac r9rk Hfrc XF :=
  cbn [ms_mem restrict mkst]; apply Forall_cons; [|apply Forall_nil];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; r9norm Ha;
    apply (mbyte_of_aview SEGS); apply Hfrc; [lia | | lia];
    let Hd := fresh "Hd" in intros Hd; apply (proj2 (XF a ltac:(lia))); lia
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; r9norm Ha; exfalso; lia ].
Ltac r9after HS HP2 Hfrc XF kk :=
  lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
  lazymatch type of Hfrc with forall a, _ -> _ -> _ -> aview _ (w_H ?Wx) ?mem2 a = _ =>
  let HS2 := fresh "HS2" in
  jafter_call_keep_pi HS kk regs2 (mrestrict (w_H Wx) mem2) HP2 [0]%nat HS2;
  let HRK := fresh "HRK" in
  match type of HS2 with ?tq -> _ => assert (HRK : tq) by (r9rk Hfrc XF) end;
  specialize (HS2 HRK); clear HRK;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  let HEI2 := fresh "HEI" in
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?k0 ?ws) _ _ =>
    lazymatch goal with HEIo : img_env _ _ Eo |- _ =>
      assert (HEI2 : img_env VAL A_LIM (havoc Eo k0 ws)) by (apply img_env_havoc; [exact HEIo | cbv; lia]) end end
  end end.
Ltac r9run3 KP FR :=
  lazymatch goal with HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ =>
  pose proof (rbn9_kept_of_frame _ _ _ _ _ (fun _ => False) HFr HG ltac:(r9wr)) as FR;
  clear HFr HG; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end);
  let K2 := fresh "KP" in
  pose proof (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ KP FR) ltac:(intros a [Ha | []]; exact Ha)) as K2;
  clear KP; rename K2 into KP end.
Lemma rbn9_copies : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A F d1 d2 d3 lnb ltb nF : Z) Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 2 = w64 A -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 9 = w64 A -> getr regs 19 = w64 F -> getr regs 20 = w64 (F + 192) -> getr regs 23 = w64 nF ->
  getr regs 24 = w64 lnb -> getr regs 26 = w64 ltb -> getr regs 27 = w64 (F + 64) ->
  0 <= A -> A + 56 <= 2 ^ 64 -> 0 <= F -> F + 512 <= 2 ^ 63 ->
  0 <= d1 < 2 ^ 64 -> 0 <= d2 < 2 ^ 64 -> 0 <= d3 < 2 ^ 64 -> 0 <= lnb < 64 -> 0 <= ltb < 64 -> 0 <= nF < 64 ->
  (A - sp0) mod 16 = 0 -> A <= sp0 -> ESTACK - (A - sp0) <= STK -> kHighMemBeg <= A - ESTACK ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 d3 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 d1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 8 d2 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 48) 8 (F + 128) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W memc A d1 (F + 64) (lnb + 1) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W memc A d2 (F + 128) (ltb + 1) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W memc A d3 (F + 192) (nF + 1) ->
  (d1 + lnb + 1 <= d2 \/ d2 + ltb + 1 <= d1) -> (d1 + lnb + 1 <= d3 \/ d3 + nF + 1 <= d1) ->
  (d2 + ltb + 1 <= d3 \/ d3 + nF + 1 <= d2) ->
  (forall a, (d1 <= a < d1 + lnb + 1 \/ d2 <= a < d2 + ltb + 1 \/ d3 <= a < d3 + nF + 1) ->
     ~ (F <= a < F + 512) /\ ~ (A <= a < A + 56)) ->
  (forall regs2 mem2 mdc2,
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 mdc2 k ->
     rbn9_same regs regs2 [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] -> getr regs2 21 = w64 0 ->
     rbn9_kept W memc mem2
       (fun a => d1 <= a < d1 + lnb + 1 \/ d2 <= a < d2 + ltb + 1 \/ d3 <= a < d3 + nF + 1 \/ A - ESTACK <= a < A) ->
     (forall i, 0 <= i < lnb + 1 -> aview SEGS (w_H W) mem2 (d1 + i) = aview SEGS (w_H W) memc (F + 64 + i)) ->
     (forall i, 0 <= i < ltb + 1 -> aview SEGS (w_H W) mem2 (d2 + i) = aview SEGS (w_H W) memc (F + 128 + i)) ->
     (forall i, 0 <= i < nF + 1 -> aview SEGS (w_H W) mem2 (d3 + i) = aview SEGS (w_H W) memc (F + 192 + i)) ->
     SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN9_TAIL) regs2 mem2 mdc2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN9_ACC) regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A F d1 d2 d3 lnb ltb nF Q HJ
  H2 H3 H4 H9 H19 H20 H23 H24 H26 H27 HA0 HA1 HF0 HF1 R1 R2 R3 Rl1 Rl2 Rl3 Ho16 Hosp Hostk HAhi
  M8 M16 M24 M48 C1 C2 C3 D12 D13 D23 XF K.
pose proof (rbn9c_entry W regs memc A F d1 d2 d3 H9 H19 HA0 HA1 HF0 ltac:(lia) R1 R2 R3 M8 M16 M24 M48) as HS.
set (E := ERB9c regs d3 d1 d2) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9c; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9c; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [d3; d1; d2]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ERB9c; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth map] in E32, E33, E34. clear EX.
assert (E2 : ew E 2 = Z_to_bv 64 A) by (rewrite (EE 2%nat 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (F + 192)) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E23 : ew E 23 = Z_to_bv 64 nF) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 lnb) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E26 : ew E 26 = Z_to_bv 64 ltb) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = Z_to_bv 64 (F + 64)) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
clearbody E.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Hes : ESTACK = 4096) by reflexivity.
set (Wr3 := fun a => d1 <= a < d1 + lnb + 1 \/ d2 <= a < d2 + ltb + 1 \/ d3 <= a < d3 + nF + 1 \/ A - ESTACK <= a < A).
pose proof C1 as (_ & Hd10 & Hd1n & Hd1w & Hd1am & _ & _ & _ & _ & Hs1w & _).
pose proof C2 as (_ & Hd20 & Hd2n & Hd2w & Hd2am & _ & _ & _ & _ & Hs2w & _).
pose proof C3 as (_ & Hd30 & Hd3n & Hd3w & Hd3am & _ & _ & _ & _ & Hs3w & _).
assert (HWb : forall a, Wr3 a -> ~ (kLowMemEnd <= a < kHighMemBeg)).
{ intros a Ha Hb. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - exact (rbn9_amem_out a d1 (lnb + 1) Hd1am Hd10 Hb ltac:(lia)).
  - exact (rbn9_amem_out a d2 (ltb + 1) Hd2am Hd20 Hb ltac:(lia)).
  - exact (rbn9_amem_out a d3 (nF + 1) Hd3am Hd30 Hb ltac:(lia)).
  - unfold kHighMemBeg in *. lia. }
assert (HWF : forall a, F <= a < F + 512 -> ~ (A - ESTACK <= a < A) -> ~ Wr3 a).
{ intros a Ha Hw Hc. destruct Hc as [Hc | [Hc | [Hc | Hc]]];
  [apply (proj1 (XF a ltac:(tauto))) | apply (proj1 (XF a ltac:(tauto))) | apply (proj1 (XF a ltac:(tauto))) | apply Hw];
  first [exact Ha | exact Hc]. }
assert (HWx1 : forall a, F + 64 <= a < F + 64 + (lnb + 1) -> ~ Wr3 a)
  by (intros a Ha; apply HWF; [lia | exact (proj2 (Hs1w a Ha))]).
assert (HWx2 : forall a, F + 128 <= a < F + 128 + (ltb + 1) -> ~ Wr3 a)
  by (intros a Ha; apply HWF; [lia | exact (proj2 (Hs2w a Ha))]).
assert (HWx3 : forall a, F + 192 <= a < F + 192 + (nF + 1) -> ~ Wr3 a)
  by (intros a Ha; apply HWF; [lia | exact (proj2 (Hs3w a Ha))]).
pose proof (rbn9_kept_refl W memc Wr3) as KP.
unfold cfg_at. change (w64 (BASE + AF_reac_box_name + RBN9_ACC)) with (Z_to_bv 64 (BASE + AF_reac_box_name + RBN9_ACC)).
rewrite <- Z.add_assoc.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
r9step KP.
pose proof (rbn9_cpy_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 KP HWb HWx1) as C1'.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
r9norm Ra0. r9norm Ra1. r9norm Ra2. r9norm Rsp. r9norm Rgp. r9norm Rtp.
rewrite (EE 3%nat 3%bv eq_refl) in Rgp. rewrite (EE 4%nat 4%bv eq_refl) in Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  assert (HspT : spZ rT = sp0 + (A - sp0)) by (unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by lia; lia) end.
destruct C1' as (Cn & Cd0 & Cdn & Cdw & Cdam & Cdra & Cdhv & Cx0 & Cxn & Cxs & Cdx & Cxam & Cxra & Cxhv).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA IS___asan_memcpy) AMEMCPY W rT mT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k d1 (F + 64) (lnb + 1) (A - sp0) _ HJ) end;
  [ rewrite Ra0; reflexivity | rewrite Ra1; reflexivity | rewrite Ra2; reflexivity | exact Cn | exact Cd0 | exact Cdn
  | exact HspT | exact Ho16 | lia | exact Hostk | rewrite Rgp; exact H3 | rewrite Rtp; exact H4 | exact Rra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; replace (sp0 + (A - sp0)) with A by lia; exact (Cdw a Ha)
  | exact Cdam | exact Cdra | exact Cdhv
  | split; [exact Cx0|]; split; [exact Cxn|]; split;
    [intros a Ha; rewrite HspT; replace (sp0 + (A - sp0)) with A by lia; exact (Cxs a Ha)|];
    split; [exact Cdx|]; split; [exact Cxam|]; split; [exact Cxra | exact Cxhv] ]. }
clear Cn Cd0 Cdn Cdw Cdam Cdra Cdhv Cx0 Cxn Cxs Cdx Cxam Cxra Cxhv.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfrc & Hpres2).
replace (sp0 + (A - sp0)) with A in Hfrc by lia.
assert (CP1 : forall j, 0 <= j < lnb + 1 -> aview SEGS (w_H W) mem2 (d1 + j) = aview SEGS (w_H W) memc (F + 64 + j)).
{ intros j Hj. rewrite (Heff j Hj). apply (proj1 KP); [lia | apply HWx1; lia]. }
pose proof (rbn9_kept_call W memc _ mem2 Wr3 d1 (lnb + 1) A KP Hfrc Hpres2
  ltac:(intros a Ha; unfold Wr3; lia) ltac:(intros a Ha; unfold Wr3; lia)) as KP2. clear KP. rename KP2 into KP.
r9after HS HP2 Hfrc XF 40%nat.
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
r9run3 KP FR.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP1 FR ltac:(lia) ltac:(lia)) as CP1b. clear CP1 FR. rename CP1b into CP1.
pose proof (rbn9_cpy_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C2 KP HWb HWx2) as C2'.
pmkst HS.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2.
prreg HS (1%bv : bv 5) Rrb. prreg HS (2%bv : bv 5) Rspb. prreg HS (3%bv : bv 5) Rgpb. prreg HS (4%bv : bv 5) Rtpb.
r9norm Rb0. r9norm Rb1. r9norm Rb2. r9norm Rspb. r9norm Rgpb. r9norm Rtpb.
rewrite (EE 3%nat 3%bv eq_refl) in Rgpb. rewrite (EE 4%nat 4%bv eq_refl) in Rtpb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  assert (HspT2 : spZ rT = sp0 + (A - sp0)) by (unfold spZ; rewrite Rspb; rewrite unsigned_lit_small by lia; lia) end.
destruct C2' as (Cn & Cd0 & Cdn & Cdw & Cdam & Cdra & Cdhv & Cx0 & Cxn & Cxs & Cdx & Cxam & Cxra & Cxhv).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA IS___asan_memcpy) AMEMCPY W rT mT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k d2 (F + 128) (ltb + 1) (A - sp0) _ HJ2) end;
  [ rewrite Rb0; reflexivity | rewrite Rb1; reflexivity | rewrite Rb2; reflexivity | exact Cn | exact Cd0 | exact Cdn
  | exact HspT2 | exact Ho16 | lia | exact Hostk | rewrite Rgpb; exact H3 | rewrite Rtpb; exact H4 | exact Rrb
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; replace (sp0 + (A - sp0)) with A by lia; exact (Cdw a Ha)
  | exact Cdam | exact Cdra | exact Cdhv
  | split; [exact Cx0|]; split; [exact Cxn|]; split;
    [intros a Ha; rewrite HspT2; replace (sp0 + (A - sp0)) with A by lia; exact (Cxs a Ha)|];
    split; [exact Cdx|]; split; [exact Cxam|]; split; [exact Cxra | exact Cxhv] ]. }
clear Cn Cd0 Cdn Cdw Cdam Cdra Cdhv Cx0 Cxn Cxs Cdx Cxam Cxra Cxhv.
intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hb0' & Heff2 & Hfrc2 & Hpres3).
replace (sp0 + (A - sp0)) with A in Hfrc2 by lia.
assert (CP2 : forall j, 0 <= j < ltb + 1 -> aview SEGS (w_H W) mem3 (d2 + j) = aview SEGS (w_H W) memc (F + 128 + j)).
{ intros j Hj. rewrite (Heff2 j Hj). apply (proj1 KP); [lia | apply HWx2; lia]. }
pose proof (rbn9_cp_call _ _ _ _ _ _ _ _ _ _ CP1 Hfrc2 ltac:(lia) ltac:(intros j Hj; exact (proj2 (Hd1w (d1 + j) ltac:(lia))))
  ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_kept_call W memc _ mem3 Wr3 d2 (ltb + 1) A KP Hfrc2 Hpres3
  ltac:(intros a Ha; unfold Wr3; lia) ltac:(intros a Ha; unfold Wr3; lia)) as KP2. clear KP. rename KP2 into KP.
r9after HS HP3 Hfrc2 XF 60%nat.
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
r9run3 KP FR.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP1 FR ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP2 FR ltac:(lia) ltac:(lia)) as CP2b. clear CP2 FR. rename CP2b into CP2.
pose proof (rbn9_cpy_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C3 KP HWb HWx3) as C3'.
pmkst HS.
prreg HS (10%bv : bv 5) Rc0. prreg HS (11%bv : bv 5) Rc1. prreg HS (12%bv : bv 5) Rc2.
prreg HS (1%bv : bv 5) Rrc. prreg HS (2%bv : bv 5) Rspc. prreg HS (3%bv : bv 5) Rgpc. prreg HS (4%bv : bv 5) Rtpc.
r9norm Rc0. r9norm Rc1. r9norm Rc2. r9norm Rspc. r9norm Rgpc. r9norm Rtpc.
rewrite (EE 3%nat 3%bv eq_refl) in Rgpc. rewrite (EE 4%nat 4%bv eq_refl) in Rtpc.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  assert (HspT3 : spZ rT = sp0 + (A - sp0)) by (unfold spZ; rewrite Rspc; rewrite unsigned_lit_small by lia; lia) end.
destruct C3' as (Cn & Cd0 & Cdn & Cdw & Cdam & Cdra & Cdhv & Cx0 & Cxn & Cxs & Cdx & Cxam & Cxra & Cxhv).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA IS___asan_memcpy) AMEMCPY W rT mT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k d3 (F + 192) (nF + 1) (A - sp0) _ HJ3) end;
  [ rewrite Rc0; reflexivity | rewrite Rc1; reflexivity | rewrite Rc2; reflexivity | exact Cn | exact Cd0 | exact Cdn
  | exact HspT3 | exact Ho16 | lia | exact Hostk | rewrite Rgpc; exact H3 | rewrite Rtpc; exact H4 | exact Rrc
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; replace (sp0 + (A - sp0)) with A by lia; exact (Cdw a Ha)
  | exact Cdam | exact Cdra | exact Cdhv
  | split; [exact Cx0|]; split; [exact Cxn|]; split;
    [intros a Ha; rewrite HspT3; replace (sp0 + (A - sp0)) with A by lia; exact (Cxs a Ha)|];
    split; [exact Cdx|]; split; [exact Cxam|]; split; [exact Cxra | exact Cxhv] ]. }
clear Cn Cd0 Cdn Cdw Cdam Cdra Cdhv Cx0 Cxn Cxs Cdx Cxam Cxra Cxhv.
intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hc0' & Heff3 & Hfrc3 & Hpres4).
replace (sp0 + (A - sp0)) with A in Hfrc3 by lia.
assert (CP3 : forall j, 0 <= j < nF + 1 -> aview SEGS (w_H W) mem4 (d3 + j) = aview SEGS (w_H W) memc (F + 192 + j)).
{ intros j Hj. rewrite (Heff3 j Hj). apply (proj1 KP); [lia | apply HWx3; lia]. }
pose proof (rbn9_cp_call _ _ _ _ _ _ _ _ _ _ CP1 Hfrc3 ltac:(lia) ltac:(intros j Hj; exact (proj2 (Hd1w (d1 + j) ltac:(lia))))
  ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_cp_call _ _ _ _ _ _ _ _ _ _ CP2 Hfrc3 ltac:(lia) ltac:(intros j Hj; exact (proj2 (Hd2w (d2 + j) ltac:(lia))))
  ltac:(lia) ltac:(lia)) as CP2b. clear CP2. rename CP2b into CP2.
pose proof (rbn9_kept_call W memc _ mem4 Wr3 d3 (nF + 1) A KP Hfrc3 Hpres4
  ltac:(intros a Ha; unfold Wr3; lia) ltac:(intros a Ha; unfold Wr3; lia)) as KP2. clear KP. rename KP2 into KP.
r9after HS HP4 Hfrc3 XF 80%nat.
paj_run_to_sh RUNTOP HS HJ4 (AF_reac_box_name + RBN9_TAIL).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
r9run3 KP FR.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP1 FR ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP2 FR ltac:(lia) ltac:(lia)) as CP2b. clear CP2. rename CP2b into CP2.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP3 FR ltac:(lia) ltac:(lia)) as CP3b. clear CP3 FR. rename CP3b into CP3.
r9go HS RBN9_TAIL.
apply K.
- assumption.
- r9same EE.
- let R := fresh "R" in prreg HS (21%bv : bv 5) R; rewrite R; reflexivity.
- exact KP.
- intros j Hj. apply CP1. lia.
- intros j Hj. apply CP2. lia.
- intros j Hj. apply CP3. lia.
Qed.
Lemma rbn9_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
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
Lemma rbn9_ra_frame : forall W1 (m : word -> option byte) F sh lo hi,
  rbn_shadow_at W1 m (shadow_addr F) sh -> F mod 8 = 0 -> 0 <= lo -> lo <= hi -> hi <= Z.of_nat (length sh) ->
  (forall j, lo <= j < hi -> nth (Z.to_nat j) sh 0 = 0) ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 8 * lo) (8 * (hi - lo)).
Proof.
intros W1 m F sh lo hi Hsh HF8 Hlo Hlh Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr F + (x - F) / 8).
{ unfold shadow_of_addr, shadow_addr.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
  assert (Q : x / 8 = (x - F) / 8 + F / 8).
  { replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. reflexivity. }
  lia. }
rewrite Ex. assert (Hj : lo <= (x - F) / 8 < hi).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite (Hsh ((x - F) / 8) ltac:(lia)). rewrite (Hz _ Hj). reflexivity.
Qed.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis L7F : rbn_L7_fits B.
Definition rbn9a_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 128 148 0 0
      [YP09.mkChunk 128 (CVal 8 (SLit 48)); YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 144 (CVal 4 (SLit 0))] ].
Definition ss_rbn9a : sstate := mkSS (AF_reac_box_name + RBN_P9) sr_atoms rbn9a_regions None (mkFacts [] [] []).
Definition ERB9a (regs : bvmap 5 word) (n0 : Z) : env := Eimg (Ereg regs [Z_to_bv 64 n0]).
Lemma regs_ok_ERB9a : forall regs n0, regs_ok (ERB9a regs n0) sr_atoms regs.
Proof.
intros. unfold ERB9a. apply (regs_ok_agree 32 (Ereg regs [Z_to_bv 64 n0])).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9a_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc (A n0 : Z),
  getr regs 9 = w64 A -> 0 <= A -> A + 148 <= 2 ^ 64 -> 0 <= n0 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 48 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 0 ->
  st_ok_pi SEGS VAL (ERB9a regs n0) ss_rbn9a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P9))) memc (seg_rom SEGS))).
Proof.
intros W regs memc A n0 H9 HA0 HA1 Rn0 M128 M136 M144.
rewrite restrict_mkst_fx.
set (E := ERB9a regs n0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9a; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 n0)
  by (subst E; unfold ERB9a; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n0] 0)).
unfold ss_rbn9a, rbn9a_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9a.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ A 128 8 (SLit 48) 48); [reflexivity | zside | zside | exact M128].
  + apply (chunk_ok_val SEGS E _ A 136 8 _ n0); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M136].
  + apply (chunk_ok_val SEGS E _ A 144 4 (SLit 0) 0); [reflexivity | lia | zside | exact M144].
- cbn [pairwise_disjoint]. split; exact I.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn9_garr8_app : forall (m : word -> option byte) a l1 l2,
  garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl | Hl].
- rewrite app_nth1 by exact Hl. exact (H1 j Hl).
- rewrite app_nth2 by exact Hl. destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma rbn9_sh_kept : forall (W1 : world SEGS) (m m' : word -> option byte) q l (Wr : Z -> Prop),
  rbn_shadow_at W1 m q l -> rbn9_kept W1 m m' Wr -> 0 <= q -> q + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length l) -> ~ Wr (q + j)) -> rbn_shadow_at W1 m' q l.
Proof. intros W1 m m' q l Wr Hs [K _] H0 H1 Hn j Hj. rewrite (K (q + j) ltac:(lia) (Hn j Hj)). exact (Hs j Hj). Qed.
Lemma rbn9_acc_lens : forall X : rbn_in, rbm_acc X = true ->
  rbm_args X /\ Z.of_nat (length (rbm_NM X)) + 1 <= Z.min (ri_name_len X) 24 /\
  Z.of_nat (length (bn_TK (rbm_NM X))) + 1 <= Z.min (ri_token_len X) 24 /\
  Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) + 1 <= Z.min (ri_display_len X) 48.
Proof.
intros X Hacc.
assert (HA : rbm_args X).
{ unfold rbm_acc, reac_box_name_c.bn_accept in Hacc. unfold rbm_args.
  do 4 (apply andb_true_iff in Hacc as [Hacc _]). exact Hacc. }
pose proof Hacc as Hacc'. rewrite (rbn9_acc X HA) in Hacc'.
apply andb_true_iff in Hacc' as [Hacc' H4]. apply andb_true_iff in Hacc' as [Hacc' H3].
apply andb_true_iff in Hacc' as [H1 H2].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4.
destruct (rbn9_acc_parts X HA H1) as (E1 & E2 & E3).
destruct (rbn9_D9_len X HA) as (_ & HD).
pose proof (rbn9_NB_len X) as HNB.
assert (HL3 : Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) = Z.of_nat (length (rbm_D9 X)) + 5)
  by (rewrite <- E3, length_app; cbn [length]; lia).
rewrite E1 in H2, HNB. rewrite E2 in H3.
pose proof (rbn9_tk_len false (rbm_NM X)) as HT. unfold bn_TK in H3 |- *.
split; [exact HA|]. split; [lia|]. split; [lia|]. lia.
Qed.
Lemma rbn9_aview_val1 : forall H (m : word -> option byte) a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
rewrite V0. cbn [option_map]. f_equal.
assert (Hle : YO0f.le_byte v 1 0 = v).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity. }
rewrite Hle, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma rbn9_sh_same : forall k, (k < 4 \/ 30 <= k < 64)%nat ->
  nth k (rbn_sh true true true true) 0 = nth k (rbn_sh false false false false) 0.
Proof. intros k Hk. do 64 (destruct k as [|k]; [first [reflexivity | lia] |]). lia. Qed.
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac r9ar T := lazymatch T with
  | ?a /\ ?b => r9ar a; r9ar b
  | ?a \/ ?b => r9ar a; r9ar b
  | ~ ?a => r9ar a
  | @eq Z _ _ => idtac
  | Z.le _ _ => idtac
  | Z.lt _ _ => idtac
  | Z.ge _ _ => idtac
  | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac
  | le _ _ => idtac
  | lt _ _ => idtac
  | False => idtac
  | True => idtac
  end.
Ltac r9lia :=
  repeat match goal with H : ?T |- _ =>
    lazymatch type of T with Prop => tryif r9ar T then fail else clear H end end;
  lia.
Lemma rbn9_req : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma rbn9_mb_eq : forall H H' (m m' : word -> option byte) a a',
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rbn9_garr8_move : forall (H H' : word -> bool) (m m' : word -> option byte) p p' L,
  (forall i, 0 <= i < Z.of_nat (length L) -> aview SEGS H' m' (p' + i) = aview SEGS H m (p + i)) ->
  garr8 SEGS (mrestrict H m) p L -> garr8 SEGS (mrestrict H' m') p' L.
Proof.
intros H H' m m' p p' L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. pose proof (Hv k Hk) as Hb.
rewrite (rbn9_mb_eq H H' m m' (p + Z.of_nat j + Z.of_nat k) (p' + Z.of_nat j + Z.of_nat k)); [exact Hb|].
replace (p' + Z.of_nat j + Z.of_nat k) with (p' + (Z.of_nat j + Z.of_nat k)) by lia.
replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia.
apply HE. lia.
Qed.
Lemma rbn9_val1_of_aview : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate].
injection Hv as <-. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
assert (Hle : YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity. }
rewrite Hle, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma rbn9_hull_frame : forall (rd : reader) F x n,
  F mod 8 = 0 -> (forall i, 0 <= i < 64 -> rd (shadow_addr F + i) <> None) ->
  F + 64 <= x -> x + n <= F + 240 -> 0 < n -> shadow_hull_vis rd x n.
Proof.
intros rd F x n HF8 HP Hx Hxn Hn s Hs.
replace s with (shadow_addr F + (s - shadow_addr F)) by lia. apply HP.
unfold shadow_addr in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D0. rewrite HF8, Z.add_0_r in D0.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_amem_frame : forall F x n, in_app F 512 -> F <= x -> x + n <= F + 512 -> amem_range x n.
Proof.
intros F x n [_ H] H1 H2. pose proof asan_consts as (C1 & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H. lia.
Qed.
Lemma rbn9_app_sh : forall x, app_addr x -> ~ (kLowShadowBeg <= x < kHighMemBeg).
Proof. intros x [_ [H | [H _]]] Hc; lia. Qed.
Lemma rbn9_ra_true : forall W1 (m : word -> option byte) F,
  rbn_shadow_at W1 m (shadow_addr F) (rbn_sh true true true true) -> F mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 64) 24 /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 128) 24 /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 192) 48.
Proof.
intros W1 m F Hs HF8.
assert (L64 : Z.of_nat (length (rbn_sh true true true true)) = 64) by reflexivity.
split; [|split].
- replace (F + 64) with (F + 8 * 8) by lia. replace 24 with (8 * (11 - 8)) by lia.
  apply (rbn9_ra_frame W1 m F _ 8 11 Hs HF8); [lia | lia | rewrite L64; lia |].
  intros j Hj. assert (j = 8 \/ j = 9 \/ j = 10) as Hjj by lia. destruct Hjj as [-> | [-> | ->]]; reflexivity.
- replace (F + 128) with (F + 8 * 16) by lia. replace 24 with (8 * (19 - 16)) by lia.
  apply (rbn9_ra_frame W1 m F _ 16 19 Hs HF8); [lia | lia | rewrite L64; lia |].
  intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as Hjj by lia. destruct Hjj as [-> | [-> | ->]]; reflexivity.
- replace (F + 192) with (F + 8 * 24) by lia. replace 48 with (8 * (30 - 24)) by lia.
  apply (rbn9_ra_frame W1 m F _ 24 30 Hs HF8); [lia | lia | rewrite L64; lia |].
  intros j Hj. assert (j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29) as Hjj by lia.
  destruct Hjj as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.
Lemma rbn9_closed : forall X, rbm_args X -> 0 <= ri_name X -> 0 <= ri_token X -> 0 <= ri_display X ->
  ~ YI16.sink_open_fp (rbn_FPX X).
Proof.
intros X HA H1 H2 H3 (r & Hr & H0). destruct (rbn9_args X HA) as (Hn & Ht & Hd & _).
unfold rbn_FPX, rbn_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia.
Qed.
Definition rbn9_W (X : rbn_in) (pos a : Z) : Prop :=
  (rbn_F X pos + 192 <= a < rbn_F X pos + 240) \/ (rbn_A X - ESTACK <= a < rbn_A X + 148) \/
  (rbn_SH X pos + 4 <= a < rbn_SH X pos + 30) \/ rbn_wr X a.
Lemma rbn9_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh -> forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM c p.
destruct HM as (_ & (_ & L1 & _) & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F1. reflexivity.
Qed.
Lemma rbn9_A_rng : forall X, rbn_cx B G X ->
  alloc_ceiling + 8496 <= rbn_SP X /\ rbn_SP X - 319 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X <= 2 ^ 47 /\ rbn_A X mod 32 = 0 /\ rbn_SP X mod 16 = 0.
Proof.
intros X HX. destruct HX as ((_ & _ & _ & _ & _ & (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
unfold rbn_A, rbn_SP. rewrite WS in Hslo.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity | exact Hal].
Qed.
Lemma rbn9_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh m md,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m md 0 ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) m a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W1) m (rbn_SH X pos + i)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh m md HM HJm.
pose proof (rbn9_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM 3 pos) as FA.
pose proof HJm as (HAR1 & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & Hspr).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_SH, rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
split.
- intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha.
- intros i Hi. exact (proj1 (Hspr i ltac:(change (512 / 8) with 64; lia))).
Qed.
Lemma rbn9_blk : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh q N a,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  In (q, N) (ablocks B (ri_lyc X) (ri_Sc X)) -> q <= a < q + req_size N ->
  ~ in_img SEGS a /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512) /\ 4096 <= a /\ a < alloc_ceiling /\ app_addr a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh q N a HX HM Hin Ha.
pose proof (rbn9_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM 3 pos) as FA.
pose proof HX as ((HAR0 & _) & _).
pose proof HM as (_ & HJ1 & Hperm & _).
pose proof HJ1 as (HAR1 & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
assert (Hb1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR0 Hin) as (_ & Hq4096 & Hqc & Hqapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hb1 Hin3) as Hd.
rewrite FA in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd.
split; [exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_introl (ex_intro _ q (ex_intro _ N (conj Hin Ha))))))|].
split; [unfold rbn_F; lia|]. split; [lia|]. split; [lia|]. exact (in_app_addr _ _ a Hqapp Ha).
Qed.
Lemma rbn9_wr_blk : forall X a, rbn_cx B G X -> rbn_wr X a ->
  exists q N, In (q, N) (ablocks B (ri_lyc X) (ri_Sc X)) /\ q <= a < q + req_size N.
Proof.
intros X a HX [Hacc Ha].
destruct (rbn9_acc_lens X Hacc) as (HA & L1 & L2 & L3).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hargs & _).
destruct (Hargs HA) as (_ & (q1 & N1 & B1 & B1a & B1b) & (q2 & N2 & B2 & B2a & B2b) & (q3 & N3 & B3 & B3a & B3b) & _).
pose proof (rbn9_req N1). pose proof (rbn9_req N2). pose proof (rbn9_req N3).
destruct Ha as [Ha | [Ha | Ha]].
- exists q1, N1. split; [exact B1 | lia].
- exists q2, N2. split; [exact B2 | lia].
- exists q3, N3. split; [exact B3 | lia].
Qed.
Lemma rbn9_lit : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh m md,
  rbn_cx B G X -> rbm_args X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m md 0 ->
  rbn_lsrc W1 m (VAL (A_OBJ 24)) (rbn_lit7 ++ [0]) /\ VAL (A_OBJ 24) mod 8 = 0 /\
  (forall a, VAL (A_OBJ 24) <= a < VAL (A_OBJ 24) + 6 -> in_img SEGS a) /\
  IMG_LO + 64 <= VAL (A_OBJ 24) /\ VAL (A_OBJ 24) + 70 <= IMG_TOP.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh m md HX HA HM HJm.
pose proof HM as (HW1 & _). subst W1. clear HM.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _ & _ & _ & R16 & _ & _ & _ & _ & Rd & _ & _ & Himg & _).
clear HX.
destruct Himg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H24al & L1 & L2 & _ & Lg & (q & z & Hqz & Hq1 & Hq2) & Lfix & _).
change (Z.of_nat (length [32; 111; 117; 116; 41])) with 5 in L2, Hq2, Lfix.
pose proof HJm as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HCL : ~ YI16.sink_open_fp (rbn_FPX X)) by (apply rbn9_closed; [exact HA | lia | lia | lia]).
split; [|split; [exact H24al | split; [intros a Ha; exact (proj1 (Lfix a ltac:(lia))) | lia]]].
unfold rbn_lsrc. change (Z.of_nat (length (rbn_lit7 ++ [0]))) with 6.
split.
{ apply (rbn9_garr8_move (w_H (ri_W X)) (w_H (ri_W X)) (ri_memc X) m (VAL (A_OBJ 24)) (VAL (A_OBJ 24))); [|exact Lg].
  intros i Hi. change (Z.of_nat (length (rbn_lit7 ++ [0]))) with 6 in Hi.
  destruct (Lfix (VAL (A_OBJ 24) + i) ltac:(lia)) as (Hi1 & Hi2 & Hi3).
  apply F3; [exact Hi1 | exact Hi2 | exact Hi3 | apply fp_spares_closed; exact HCL]. }
split; [lia|]. split; [lia|]. split; [lia|].
exact (ro_usable_glob SEGS B G lyc1 Sc1 (ri_W X) m md q z (VAL (A_OBJ 24)) 6 GM Hqz HAR1 Hq1 ltac:(lia)).
Qed.
Lemma rbn9_head : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 Q,
  rbn_cx B G X -> rbn_st9 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall regs3 mem3 mdc3,
     ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
       [(3, pos)] lyc1 Sc1 W1 mem3 mdc3 0 ->
     rbn9_same regs1 regs3 [1; 2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27] ->
     getr regs3 23 = w64 (Z.of_nat (length (rbm_D9 X)) + 5) -> getr regs3 12 = w64 0 ->
     rbn9_kept W1 memc1 mem3 (fun a => rbn_F X pos + 192 <= a < rbn_F X pos + 240) ->
     garr8 SEGS (mrestrict (w_H W1) mem3) (rbn_F X pos + 192) (rbm_D9 X ++ rbn_lit7) ->
     SRr SEGS W1 (rbn_cfg RBN_L7X regs3 mem3 mdc3) Q) ->
  SRr SEGS W1 (rbn_cfg RBN_P9 regs1 memc1 mdc1) Q.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 Q HX Hst K.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR7 & AR8).
pose proof Hst as (HM & _).
pose proof (rbn9_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as FA.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
destruct Hst as (_ & (H2 & H3 & H4 & H8 & H9 & H19 & H22) & H18 & H27 & H24 & H25 & H20 & H26 & H21 & HC & G64 & G128 & G192 & HA).
pose proof HM as (HW1 & HJ & _ & _ & _ & _ & _ & Hsh).
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HM HJ) as (HF4096 & HFceil & HF32 & HFapp & HFpr & HSpr).
unfold rbn_locs6, rbn_locs4, rbn_rec2 in HC. cbn [rbn_cells app] in HC.
destruct HC as (C8 & C16 & C32 & C56 & C64 & C80 & C88 & C152 & C160 & C168 & C176 & C24 & C48 & C72 & C120 & C128 & C136 & C144 & C40 & _).
destruct (rbn9_D9_ovf X HA) as (Hov47 & Hmin & Hfirst). rewrite Hov47 in C144. rewrite Hmin in C136. rewrite Hfirst in G192.
destruct (rbn9_D9_len X HA) as (_ & HD9).
set (n0 := Z.of_nat (length (rbm_D9 X))) in *.
assert (En0 : n0 = Z.of_nat (length (rbm_D9 X))) by reflexivity.
assert (Hn0 : 0 <= n0) by (rewrite En0; lia).
set (A := rbn_A X) in *. set (F := rbn_F X pos) in *.
assert (EA : A = rbn_A X) by reflexivity. assert (EF : F = rbn_F X pos) by reflexivity.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(r9lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by r9lia. apply Z.mod_mul. lia. }
pose proof (rbn9a_entry W1 regs1 memc1 A n0 H9 ltac:(r9lia) ltac:(r9lia) ltac:(r9lia) C128 C136 C144) as HS.
set (E := ERB9a regs1 n0) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9a; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB9a; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 n0)
  by (subst E; unfold ERB9a; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 [Z_to_bv 64 n0] 0)).
clearbody E.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
unfold rbn_cfg, cfg_at. change (w64 (BASE + AF_reac_box_name + RBN_P9)) with (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_P9)).
rewrite <- Z.add_assoc.
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_L7).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
lazymatch goal with HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ =>
  pose proof (rbn9_kept_of_frame _ _ _ _ _ (fun _ => False) HFr HG ltac:(r9wr)) as FR; clear HFr HG end.
assert (SAME0 : rbn9_same regs1 (ms_regs ms) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]) by r9same EE.
pmkst HS.
prreg HS (23%bv : bv 5) Q23. prreg HS (12%bv : bv 5) Q12. prreg HS (15%bv : bv 5) Q15.
prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13.
rewrite E32 in Q23. rewrite (img_env_atomP E 265 HEI ltac:(unfold A_TEXT, A_LIM; lia)) in Q13.
change 265%nat with (A_OBJ 24) in Q13.
pose proof HJ as HJc.
destruct (rbn9_lit X pos lyc1 Sc1 W1 memc1 mdc1 _ (ms_mem ms) _ HX HA HM HJc) as (Hlsrc & H24al & Limg & Lb1 & Lb2).
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ (ms_mem ms) _ HM HJc) as (_ & _ & _ & _ & HFpr2 & _).
assert (HRA2 : range_addressable (aview SEGS (w_H W1) (ms_mem ms)) SHADOW_OFF (F + 192) 48).
{ refine (proj2 (proj2 (rbn9_ra_true W1 (ms_mem ms) F _ HF8))).
  apply (rbn9_sh_kept W1 memc1 (ms_mem ms) _ _ (fun _ => False) Hsh FR); [ | | tauto].
  - unfold rbn_SH. fold F. unfold shadow_addr, SHADOW_OFF. r9lia.
  - change (Z.of_nat (length (rbn_sh true true true true))) with 64.
    unfold rbn_SH. fold F. unfold shadow_addr, SHADOW_OFF. r9lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdx) _ =>
  apply (rbn9_pc W1 (ms_regs ms) (ms_mem ms) mdx Q (BASE + AF_reac_box_name + RBN_L7));
  [unfold AF_reac_box_name, RBN_L7; lia|] end.
eapply SRr_bind.
{ apply (L7F REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 (ms_mem ms) _ 0 (ms_regs ms) A (F + 192) n0 0 ltac:(r9lia)).
  - exact HJc.
  - exact Hlsrc.
  - exact H24al.
  - r9lia.
  - r9lia.
  - right. r9lia.
  - split; [r9lia|]. split; [r9lia|]. split; [apply (in_app_sub _ _ _ _ HFapp); r9lia|]. split.
    + exact HRA2.
    + intros a Ha. split; [|exact (proj1 (HFpr2 a ltac:(r9lia)))].
      right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with F.
      change (fs_frame_bytes 3) with 512. r9lia.
  - destruct (Z_le_gt_dec (VAL (A_OBJ 24) + 6) (F + 192)) as [Hl | Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec (F + 192 + 48) (VAL (A_OBJ 24))) as [Hr | Hr]; [right; exact Hr|].
    exfalso. set (x := Z.max (VAL (A_OBJ 24)) (F + 192)).
    apply (proj2 (HFpr x ltac:(unfold x; r9lia))). apply Limg. unfold x. r9lia.
  - apply (rbn9_kept_val W1 memc1 (ms_mem ms) (fun _ => False) _ 8 _ FR); [tauto | r9lia | r9lia | exact C120].
  - right. r9lia.
  - r9lia.
  - left; reflexivity.
  - rewrite Q23. reflexivity.
  - rewrite Q12. reflexivity.
  - rewrite Q15. reflexivity.
  - exact (eq_trans (SAME0 21 ltac:(cbn; tauto)) H21).
  - rewrite Q14. reflexivity.
  - rewrite Q11. reflexivity.
  - rewrite Q13. reflexivity.
  - exact (eq_trans (SAME0 9 ltac:(cbn; tauto)) H9).
  - exact (eq_trans (SAME0 22 ltac:(cbn; tauto)) H22). }
intros W' c' _ (-> & regs3 & mem3 & md3 & Hc2 & HJ3 & HKR & HOUT & HFR3 & HG3). subst c'.
assert (KD : rbn9_kept W1 memc1 mem3 (fun a => F + 192 + n0 <= a < F + 192 + n0 + 5)).
{ unfold rbn_lit7 in HFR3. cbn [length] in HFR3. change (Z.of_nat 5) with 5 in HFR3.
  split.
  - intros a Ha Hn. rewrite (HFR3 a Ha Hn). exact (proj1 FR a Ha (fun c => c)).
  - intros a Ha Hp. apply (apresent_transfer SEGS (w_H W1) (w_H W1) (ms_mem ms) mem3 a); [r9lia | | | exact (proj2 FR a Ha Hp)].
    + intros Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. r9lia.
    + apply HFR3; r9lia. }
apply K.
- exact HJ3.
- intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [rewrite HKR; [apply SAME0; cbn; tauto | r9lia | cbn; r9lia] |]). destruct Hr.
- pose proof (Forall_inv HOUT) as O23. cbn [fst snd] in O23. exact O23.
- pose proof (Forall_inv (Forall_inv_tail HOUT)) as O12. cbn [fst snd] in O12. exact O12.
- apply (rbn9_kept_mono W1 memc1 mem3 _ _ KD). intros a Ha. cbv beta in Ha |- *. r9lia.
- apply rbn9_garr8_app.
  + apply (rbn9_kept_garr W1 memc1 mem3 _ _ _ KD); [intros j Hj; cbv beta; r9lia | r9lia | r9lia | exact G192].
  + exact HG3.
Qed.
Lemma rbn9_cpy_mk : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh m md q N d xo n,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m md 0 ->
  In (q, N) (ablocks B (ri_lyc X) (ri_Sc X)) -> q <= d -> d + n <= q + req_size N ->
  (forall a, d <= a < d + n -> inFP (rbn_FPX X) a) ->
  64 <= xo -> xo + n <= 240 -> 0 < n < 2 ^ 32 ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (rbn_F X pos + xo) n ->
  rbn9_cpy REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1 m (rbn_A X) d
    (rbn_F X pos + xo) n.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh m md q N d xo n HX HM HJm Hin Hqd Hdn HFP Hxo Hxn Hn HRA.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR7 & AR8).
pose proof (rbn9_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM 3 pos) as FA.
pose proof HM as (_ & HJ1 & Hperm & _).
pose proof HJ1 as (HAR1 & _ & _ & _ & _ & Hfrs1 & _).
pose proof HJm as (HARm & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; apply in_or_app; left; left; reflexivity).
assert (Hb1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ m md HM HJm) as (HF4096 & HFceil & HF32 & HFapp & HFpr & HSpr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hb1) as (_ & Hq4096 & Hqc & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hb1 Hin3) as Hd.
rewrite FA in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd.
change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos) in Hd.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [|lia]. right; left. split; [exact (HFP a Ha)|]. exists q, N. split; [exact Hb1 | lia]. }
split; [exact (amem_range_of_block SEGS B LAWS lyc1 Sc1 W1 m md q N d n HARm Hb1 Hqd Hdn)|].
split; [exact (range_addressable_of_block SEGS B LAWS lyc1 Sc1 W1 m md q N d n HARm Hb1 Hqd Hdn)|].
split; [intros Hn0; exact (shadow_hull_vis_of_block SEGS B LAWS lyc1 Sc1 W1 m md q N d n HARm Hb1 Hqd Hdn Hn0)|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [|lia]. exact (aview_some_of_apresent SEGS _ _ _ (proj1 (HFpr a ltac:(lia)))). }
split; [lia|].
split; [exact (rbn9_amem_frame (rbn_F X pos) (rbn_F X pos + xo) n HFapp ltac:(lia) ltac:(lia))|].
split; [exact HRA|].
intros Hn0. apply (rbn9_hull_frame _ (rbn_F X pos)); [exact HF8 | | lia | lia | exact Hn0].
intros i Hi. exact (aview_some_of_apresent SEGS _ _ _ (HSpr i Hi)).
Qed.
Lemma rbn9_close : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs6 mem6 mdc6,
  rbn_cx B G X -> rbn_st9 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem6 mdc6 0 ->
  rbn9_kept W1 memc1 mem6 (rbn9_W X pos) ->
  (forall j, 4 <= j < 30 ->
     val_mem SEGS (mrestrict (w_H W1) mem6) (rbn_SH X pos + j) 1 (nth (Z.to_nat j) (rbn_sh false false false false) 0)) ->
  rbn9_same regs1 regs6 [2; 3; 4; 8; 9; 18; 19; 22] -> getr regs6 26 = w64 (rbn_F X pos) ->
  getr regs6 21 = w64 (if rbm_acc X then 0 else -1) ->
  (rbm_acc X = true ->
     garr8 SEGS (mrestrict (w_H W1) mem6) (ri_name X) (rbm_NM X ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) mem6) (ri_token X) (bn_TK (rbm_NM X) ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) mem6) (ri_display X) (bn_DP (rbm_NM X) (ri_i X) (ri_o X) ++ [0])) ->
  rbn_st10 B X pos regs6 lyc1 Sc1 W1 mem6 mdc6.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs6 mem6 mdc6 HX Hst HJ6 KP HSH6 SAME H26 H21 HG.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR7 & AR8).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct Hst as (HM & (H2 & H3 & H4 & H8 & H9 & H19 & H22) & H18 & _).
pose proof (rbn9_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as FA.
pose proof HM as (HW1 & HJ1 & Hperm & Hro & HK & Hfr & Hfl & Hsh).
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HM HJ1) as (HF4096 & HFceil & HF32 & HFapp & HFpr & HSpr).
assert (ESH : rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8) by reflexivity.
assert (HSHb : 0x7fff8000 + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 0x10007fff8000).
{ rewrite ESH. unfold SHADOW_OFF. r9lia. }
assert (GF : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> ~ (kLowShadowBeg <= a < kHighMemBeg)).
{ intros a Ha. exact (rbn9_app_sh a (in_app_addr _ _ a HFapp Ha)). }
assert (WRF : forall a, rbn_wr X a ->
  ~ in_img SEGS a /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512) /\ 4096 <= a /\ a < alloc_ceiling /\
  ~ (kLowShadowBeg <= a < kHighMemBeg)).
{ intros a Hw. destruct (rbn9_wr_blk X a HX Hw) as (q & N & Hq & Hqa).
  destruct (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q N a HX HM Hq Hqa) as (B1 & B2 & B3 & B4 & B5).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. exact (rbn9_app_sh a B5). }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ rbn9_W X pos a -> aview SEGS (w_H W1) mem6 a = aview SEGS (w_H W1) memc1 a)
  by exact (proj1 KP).
assert (Himg : forall a, in_img SEGS a -> ~ rbn9_W X pos a).
{ intros a Hi Hw. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  destruct Hw as [Hw | [Hw | [Hw | Hw]]].
  - exact (proj2 (HFpr a ltac:(r9lia)) Hi).
  - r9lia.
  - r9lia.
  - exact (proj1 (WRF a Hw) Hi). }
assert (HSHn : forall j, 0 <= j < 64 -> ~ (rbn_F X pos <= rbn_SH X pos + j < rbn_F X pos + 512)).
{ intros j Hj Hc. apply (GF _ Hc). unfold kLowShadowBeg, kHighMemBeg. r9lia. }
split.
{ split; [exact HW1|]. split; [exact HJ6|]. split; [exact Hperm|].
  split.
  { intros a Hro0 Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    pose proof (pa_segs_low a Hia) as Hlow.
    rewrite (KV a ltac:(unfold kLowMemEnd in Hlow; r9lia) (Himg a Hia)). exact (Hro a Hro0 Ho He). }
  split.
  { intros a HFP Hblk Hnw. pose proof Hblk as (q & N & Hq & Hqa).
    pose proof (rbn9_req N) as RS.
    destruct (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q N a HX HM Hq ltac:(r9lia)) as (_ & Hnf & Ha4 & Hac & Hap).
    pose proof (rbn9_app_sh a Hap) as Hns.
    rewrite (KV a ltac:(r9lia)).
    + exact (HK a HFP Hblk (fun c => c)).
    + intros [Hw | [Hw | [Hw | Hw]]]; [r9lia | r9lia | | exact (Hnw Hw)].
      apply Hns. unfold kLowShadowBeg, kHighMemBeg. r9lia. }
  split.
  { unfold rbn_frame. intros j r Hj.
    assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length rbn_saved_regs) with 13%nat in Hj13.
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem6); [|exact (Hfr j r Hj)].
    intros kk Hkk. apply KV; [unfold rbn_SP in *; r9lia|].
    intros [Hw | [Hw | [Hw | Hw]]]; [unfold rbn_SP in *; r9lia | unfold rbn_SP in *; r9lia | unfold rbn_SP in *; r9lia |].
    destruct (WRF _ Hw) as (_ & _ & _ & Hac & _). unfold rbn_SP in *. r9lia. }
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem6); [|exact Hfl].
    intros kk Hkk. apply KV; [unfold rbn_FL in *; r9lia|].
    intros [Hw | [Hw | [Hw | Hw]]]; [r9lia | r9lia | |].
    - apply (HSHn (rbn_F X pos + 504 + kk - rbn_SH X pos)); r9lia.
    - destruct (WRF _ Hw) as (_ & Hn & _). apply Hn. r9lia. }
  intros j Hj. change (length (rbn_sh false false false false)) with 64%nat in Hj.
  destruct (Z_lt_ge_dec j 4) as [Hj4 | Hj4]; [|destruct (Z_lt_ge_dec j 30) as [Hj30 | Hj30]].
  - rewrite (KV (rbn_SH X pos + j)); [ | r9lia |].
    + rewrite (Hsh j ltac:(change (length (rbn_sh true true true true)) with 64%nat; lia)).
      rewrite rbn9_sh_same by lia. reflexivity.
    + intros [Hw | [Hw | [Hw | Hw]]]; [apply (HSHn j); r9lia | r9lia | r9lia |].
      destruct (WRF _ Hw) as (_ & _ & _ & _ & Hb). apply Hb. unfold kLowShadowBeg, kHighMemBeg. r9lia.
  - apply rbn9_aview_val1; [exact (HSH6 j ltac:(lia))|].
    assert (Hk : (Z.to_nat j < 64)%nat) by lia.
    generalize (Z.to_nat j) Hk. intros k Hk'. do 64 (destruct k as [|k]; [cbn; lia|]). lia.
  - rewrite (KV (rbn_SH X pos + j)); [ | r9lia |].
    + rewrite (Hsh j ltac:(change (length (rbn_sh true true true true)) with 64%nat; lia)).
      rewrite rbn9_sh_same by lia. reflexivity.
    + intros [Hw | [Hw | [Hw | Hw]]]; [apply (HSHn j); r9lia | r9lia | r9lia |].
      destruct (WRF _ Hw) as (_ & _ & _ & _ & Hb). apply Hb. unfold kLowShadowBeg, kHighMemBeg. r9lia. }
split.
{ split; [exact (eq_trans (SAME 2 ltac:(cbn; tauto)) H2)|]. split; [exact (eq_trans (SAME 3 ltac:(cbn; tauto)) H3)|].
  split; [exact (eq_trans (SAME 4 ltac:(cbn; tauto)) H4)|]. split; [exact (eq_trans (SAME 8 ltac:(cbn; tauto)) H8)|].
  split; [exact (eq_trans (SAME 9 ltac:(cbn; tauto)) H9)|]. split; [exact (eq_trans (SAME 19 ltac:(cbn; tauto)) H19)|].
  exact (eq_trans (SAME 22 ltac:(cbn; tauto)) H22). }
split; [exact (eq_trans (SAME 18 ltac:(cbn; tauto)) H18)|].
split; [exact H26|]. split; [exact H21|]. exact HG.
Qed.

Lemma rbn9_same3 : forall r0 r1 r2 r3 l0 l1 l2 r,
  rbn9_same r0 r1 l0 -> rbn9_same r1 r2 l1 -> rbn9_same r2 r3 l2 -> In r l0 -> In r l1 -> In r l2 ->
  getr r3 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Proof. intros r0 r1 r2 r3 l0 l1 l2 r S1 S2 S3 I1 I2 I3. rewrite (S3 r I3), (S2 r I2), (S1 r I1). reflexivity. Qed.
Lemma rbn9_same4 : forall r0 r1 r2 r3 r4 l0 l1 l2 l3 r,
  rbn9_same r0 r1 l0 -> rbn9_same r1 r2 l1 -> rbn9_same r2 r3 l2 -> rbn9_same r3 r4 l3 ->
  In r l0 -> In r l1 -> In r l2 -> In r l3 -> getr r4 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Proof.
intros r0 r1 r2 r3 r4 l0 l1 l2 l3 r S1 S2 S3 S4 I1 I2 I3 I4.
rewrite (S4 r I4), (S3 r I3), (S2 r I2), (S1 r I1). reflexivity.
Qed.
Lemma rbn_seg9 : rbn_seg9_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX Hst.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR7 & AR8).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hst as (HM & (H2 & H3 & H4 & H8 & H9 & H19 & H22) & H18 & H27 & H24 & H25 & H20 & H26 & H21 & HC & G64 & G128 & G192 & HA).
pose proof HM as (HW1 & HJ1 & Hperm & _ & _ & _ & _ & Hsh).
pose proof (rbn9_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM 3 pos) as FA.
change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos) in FA.
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HM HJ1) as (HF4096 & HFceil & HF32 & HFapp & _ & _).
unfold rbn_locs6, rbn_locs4, rbn_rec2 in HC. cbn [rbn_cells app] in HC.
destruct HC as (C8 & C16 & C32 & C56 & C64 & C80 & C88 & C152 & C160 & C168 & C176 & C24 & C48 & C72 & C120 & C128 & C136 & C144 & C40 & _).
rewrite rbn9_tok in C40.
destruct (rbn9_D9_ovf X HA) as (Hov47 & _ & _). rewrite Hov47 in C144.
destruct (rbn9_D9_len X HA) as (_ & HD9).
pose proof (rbn9_NB_len X) as HNB.
assert (HTB : (length (rbm_TB X) <= 23)%nat) by (unfold rbm_TB; rewrite length_firstn; lia).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _ & R15 & _ & R16 & _ & R17 & _ & _ & Rd & _ & Rdl & _).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(r9lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by r9lia. apply Z.mod_mul. lia. }
assert (HSHb : 0x7fff8000 + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 0x10007fff8000).
{ assert (ESH : rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8) by reflexivity. rewrite ESH. unfold SHADOW_OFF. r9lia. }
assert (HSHn : forall j, 0 <= j < 64 -> ~ (rbn_F X pos <= rbn_SH X pos + j < rbn_F X pos + 512)).
{ intros j Hj Hc. apply (rbn9_app_sh _ (in_app_addr _ _ _ HFapp Hc)). unfold kLowShadowBeg, kHighMemBeg. r9lia. }
apply (rbn9_head X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ HX Hst).
intros regs3 mem3 mdc3 HJ3 SAME3 H23_3 H12_3 KD3 GD3.
remember (Z.of_nat (length (rbm_D9 X)) + 5) as nF eqn:EnF.
assert (HnF : 5 <= nF <= 40) by r9lia.
assert (KC3 : forall a n v, val_mem SEGS (mrestrict (w_H W1) memc1) a n v -> rbn_A X <= a ->
  a + Z.of_nat n <= rbn_A X + 184 -> val_mem SEGS (mrestrict (w_H W1) mem3) a n v).
{ intros a n v Hv Ha1 Ha2. apply (rbn9_kept_val _ _ _ _ _ _ _ KD3); [intros i Hi; cbv beta; r9lia | r9lia | r9lia | exact Hv]. }
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem3 mdc3 HM HJ3) as (_ & _ & _ & _ & HFpr3 & _).
assert (Hsh3 : rbn_shadow_at W1 mem3 (rbn_SH X pos) (rbn_sh true true true true)).
{ apply (rbn9_sh_kept W1 memc1 mem3 _ _ _ Hsh KD3);
    [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
  intros j Hj Hc. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta in Hc.
  apply (HSHn j); r9lia. }
pose proof (rbn9_ra_true W1 mem3 (rbn_F X pos) Hsh3 HF8) as (_ & _ & RAD3).
apply (rbn9_checks REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
  [(3, pos)] lyc1 Sc1 W1 mem3 mdc3 0 regs3 (rbn_A X) (rbn_F X pos) nF (ri_display X) (ri_name X) (ri_token X)
  (ri_token_len X) (ri_display_len X) (ri_name_len X) (Z.of_nat (length (rbm_NB X))) (rbm_ovf 23 (rbm_NM X))
  (Z.of_nat (length (rbm_TB X))) _ HJ3).
- exact (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9).
- exact (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19).
- exact (eq_trans (SAME3 20 ltac:(cbn; tauto)) H20).
- exact (eq_trans (SAME3 22 ltac:(cbn; tauto)) H22).
- exact H23_3.
- exact H12_3.
- exact (eq_trans (SAME3 24 ltac:(cbn; tauto)) H24).
- exact (eq_trans (SAME3 25 ltac:(cbn; tauto)) H25).
- exact (eq_trans (SAME3 26 ltac:(cbn; tauto)) H26).
- exact AR7.
- r9lia.
- r9lia.
- r9lia.
- exact HF4096.
- r9lia.
- r9lia.
- exact (rbn9_ovf01 23 (rbm_NM X)).
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- apply KC3; [exact C8 | r9lia | r9lia].
- apply KC3; [exact C16 | r9lia | r9lia].
- apply KC3; [exact C24 | r9lia | r9lia].
- apply KC3; [exact C32 | r9lia | r9lia].
- apply KC3; [exact C40 | r9lia | r9lia].
- apply KC3; [exact C48 | r9lia | r9lia].
- apply KC3; [exact C56 | r9lia | r9lia].
- apply KC3; [exact C64 | r9lia | r9lia].
- apply KC3; [exact C72 | r9lia | r9lia].
- apply KC3; [exact C144 | r9lia | r9lia].
- apply KC3; [exact C176 | r9lia | r9lia].
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPW3 & _).
  apply HPW3. r9lia.
- exact (proj1 (HFpr3 (rbn_F X pos + 192 + nF) ltac:(r9lia))).
- apply (range_addressable_sub _ _ (rbn_F X pos + 192) 48); [exact RAD3 | r9lia | r9lia].
- unfold SHADOW_OFF. intros Hc.
  apply (rbn9_app_sh (rbn_F X pos + 192 + nF) (in_app_addr _ _ (rbn_F X pos + 192 + nF) HFapp ltac:(r9lia))).
  unfold kLowShadowBeg, kHighMemBeg. r9lia.
- intros a Ha. left. r9lia.
- right; right; right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite FA. change (fs_frame_bytes 3) with 512. r9lia.
- intros regs4 mem4 mdc4 (HJ4 & SAME4 & K4 & V4 & V144) H21_4 Hnacc.
  assert (HREF : rbm_acc X = false).
  { destruct (rbm_acc X) eqn:E; [|reflexivity]. exfalso. apply Hnacc.
    rewrite (rbn9_acc X HA) in E.
    apply andb_true_iff in E as [E E4]. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
    apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.ltb_lt in E3. apply Z.ltb_lt in E4.
    rewrite EnF. split; [exact E1|]. split; [exact E4|]. split; [exact E2 | exact E3]. }
  pose proof (rbn9_kept_trans _ _ _ _ _ _ KD3 K4) as K14.
  destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem4 mdc4 HM HJ4) as (_ & _ & _ & _ & _ & HSpr4).
  assert (Hsh4 : rbn_shadow_at W1 mem4 (rbn_SH X pos) (rbn_sh true true true true)).
  { apply (rbn9_sh_kept W1 memc1 mem4 _ _ _ Hsh K14);
      [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
    intros j Hj. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta.
    intros [Hc | [Hc | Hc]]; [apply (HSHn j); r9lia | r9lia | apply (HSHn j); r9lia]. }
  apply (rbn9_tail REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem4 mdc4 0 regs4 (rbn_A X) (rbn_F X pos) (rbn_SH X pos) _ HJ4).
  + exact (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9)).
  + exact (eq_trans (SAME4 18 ltac:(cbn; tauto)) (eq_trans (SAME3 18 ltac:(cbn; tauto)) H18)).
  + exact (eq_trans (SAME4 19 ltac:(cbn; tauto)) (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19)).
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + apply (rbn9_kept_val _ _ _ _ _ _ _ K14); [intros i Hi; cbv beta; r9lia | r9lia | r9lia | exact C72].
  + intros a Ha. replace a with (rbn_SH X pos + (a - rbn_SH X pos)) by r9lia. apply HSpr4. r9lia.
  + intros a Ha. right; right; right. exists 3, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite FA. change (fs_frame_bytes 3 / 8) with 64. unfold rbn_SH in Ha. r9lia.
  + intros j Hj. apply rbn9_val1_of_aview.
    exact (Hsh4 j ltac:(change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia)).
  + intros regs6 mem6 mdc6 HJ6 SAME6 H26_6 K6 HSH6.
    apply SRr_ret. exists pos, regs6, lyc1, Sc1, mem6, mdc6. split; [reflexivity|].
    apply (rbn9_close X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs6 mem6 mdc6 HX Hst HJ6).
    * apply (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ K14 K6)).
      intros a Ha. cbv beta in Ha. unfold rbn9_W.
      destruct Ha as [[Ha | [Ha | Ha]] | Ha]; [left; r9lia | right; left; r9lia | left; r9lia | right; right; left; r9lia].
    * exact HSH6.
    * intros r Hr. apply (rbn9_same3 regs1 regs3 regs4 regs6 _ _ _ r SAME3 SAME4 SAME6); cbn [In] in Hr |- *; tauto.
    * exact H26_6.
    * rewrite HREF. exact (eq_trans (SAME6 21 ltac:(cbn; tauto)) H21_4).
    * intros Hc. rewrite HREF in Hc. discriminate.
- intros regs4 mem4 mdc4 (HJ4 & SAME4 & K4 & V4 & V144) Hacc.
  destruct Hacc as (E1 & E4 & E2 & E3).
  assert (HACC : rbm_acc X = true).
  { rewrite (rbn9_acc X HA). rewrite E1. rewrite EnF in E4.
    rewrite (proj2 (Z.ltb_lt _ _) E2), (proj2 (Z.ltb_lt _ _) E3), (proj2 (Z.ltb_lt _ _) E4). reflexivity. }
  destruct (rbn9_acc_parts X HA E1) as (ENB & ETB & EDP).
  destruct (rbn9_acc_lens X HACC) as (_ & L1 & L2 & L3).
  assert (LDP : Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) = nF)
    by (rewrite <- EDP, length_app; cbn [length]; r9lia).
  assert (Hlnb : Z.of_nat (length (rbm_NB X)) = Z.of_nat (length (rbm_NM X))) by (rewrite ENB; reflexivity).
  assert (Hltb : Z.of_nat (length (rbm_TB X)) = Z.of_nat (length (bn_TK (rbm_NM X)))) by (rewrite ETB; reflexivity).
  pose proof (rbn9_kept_trans _ _ _ _ _ _ KD3 K4) as K14.
  pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hargs & _).
  destruct (Hargs HA) as (_ & (q1 & N1 & B1 & B1a & B1b) & (q2 & N2 & B2 & B2a & B2b) & (q3 & N3 & B3 & B3a & B3b) & HD12 & HD13 & HD23).
  clear Hargs.
  pose proof (rbn9_req N1) as RS1. pose proof (rbn9_req N2) as RS2. pose proof (rbn9_req N3) as RS3.
  pose proof HX as ((HAR0 & _) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q1 N1 HAR0 B1) as (_ & Q1a & Q1b & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q2 N2 HAR0 B2) as (_ & Q2a & Q2b & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q3 N3 HAR0 B3) as (_ & Q3a & Q3b & _).
  assert (BK1 : forall a, ri_name X <= a < ri_name X + Z.min (ri_name_len X) 24 -> app_addr a)
    by (intros a Ha; apply (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q1 N1 a HX HM B1); r9lia).
  assert (BK2 : forall a, ri_token X <= a < ri_token X + Z.min (ri_token_len X) 24 -> app_addr a)
    by (intros a Ha; apply (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q2 N2 a HX HM B2); r9lia).
  assert (BK3 : forall a, ri_display X <= a < ri_display X + Z.min (ri_display_len X) 48 -> app_addr a)
    by (intros a Ha; apply (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q3 N3 a HX HM B3); r9lia).
  assert (BF1 : forall a, ri_name X <= a < ri_name X + Z.min (ri_name_len X) 24 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512))
    by (intros a Ha; apply (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q1 N1 a HX HM B1); r9lia).
  assert (BF2 : forall a, ri_token X <= a < ri_token X + Z.min (ri_token_len X) 24 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512))
    by (intros a Ha; apply (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q2 N2 a HX HM B2); r9lia).
  assert (BF3 : forall a, ri_display X <= a < ri_display X + Z.min (ri_display_len X) 48 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512))
    by (intros a Ha; apply (rbn9_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q3 N3 a HX HM B3); r9lia).
  assert (Hsh4 : rbn_shadow_at W1 mem4 (rbn_SH X pos) (rbn_sh true true true true)).
  { apply (rbn9_sh_kept W1 memc1 mem4 _ _ _ Hsh K14);
      [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
    intros j Hj. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta.
    intros [Hc | [Hc | Hc]]; [apply (HSHn j); r9lia | r9lia | apply (HSHn j); r9lia]. }
  pose proof (rbn9_ra_true W1 mem4 (rbn_F X pos) Hsh4 HF8) as (RA64 & RA128 & RA192).
  assert (KC4 : forall a n v, val_mem SEGS (mrestrict (w_H W1) memc1) a n v -> rbn_A X <= a ->
    a + Z.of_nat n <= rbn_A X + 144 -> val_mem SEGS (mrestrict (w_H W1) mem4) a n v).
  { intros a n v Hv Ha1 Ha2. apply (rbn9_kept_val _ _ _ _ _ _ _ K14); [intros i Hi; cbv beta; r9lia | r9lia | r9lia | exact Hv]. }
  apply (rbn9_copies REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem4 mdc4 0 regs4 (rbn_A X) (rbn_F X pos) (ri_name X) (ri_token X) (ri_display X)
    (Z.of_nat (length (rbm_NB X))) (Z.of_nat (length (rbm_TB X))) nF _ HJ4).
  + exact (eq_trans (SAME4 2 ltac:(cbn; tauto)) (eq_trans (SAME3 2 ltac:(cbn; tauto)) H2)).
  + exact (eq_trans (SAME4 3 ltac:(cbn; tauto)) (eq_trans (SAME3 3 ltac:(cbn; tauto)) H3)).
  + exact (eq_trans (SAME4 4 ltac:(cbn; tauto)) (eq_trans (SAME3 4 ltac:(cbn; tauto)) H4)).
  + exact (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9)).
  + exact (eq_trans (SAME4 19 ltac:(cbn; tauto)) (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19)).
  + exact (eq_trans (SAME4 20 ltac:(cbn; tauto)) (eq_trans (SAME3 20 ltac:(cbn; tauto)) H20)).
  + exact (eq_trans (SAME4 23 ltac:(cbn; tauto)) H23_3).
  + exact (eq_trans (SAME4 24 ltac:(cbn; tauto)) (eq_trans (SAME3 24 ltac:(cbn; tauto)) H24)).
  + exact (eq_trans (SAME4 26 ltac:(cbn; tauto)) (eq_trans (SAME3 26 ltac:(cbn; tauto)) H26)).
  + exact (eq_trans (SAME4 27 ltac:(cbn; tauto)) (eq_trans (SAME3 27 ltac:(cbn; tauto)) H27)).
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + unfold kHighMemBeg. r9lia.
  + apply KC4; [exact C8 | r9lia | r9lia].
  + apply KC4; [exact C16 | r9lia | r9lia].
  + apply KC4; [exact C24 | r9lia | r9lia].
  + apply KC4; [exact C48 | r9lia | r9lia].
  + apply (rbn9_cpy_mk X pos lyc1 Sc1 W1 memc1 mdc1 _ mem4 mdc4 q1 N1 (ri_name X) 64 (Z.of_nat (length (rbm_NB X)) + 1)
      HX HM HJ4 B1); [r9lia | r9lia | | r9lia | r9lia | r9lia |
      apply (range_addressable_sub _ _ (rbn_F X pos + 64) 24); [exact RA64 | r9lia | r9lia]].
    intros a Ha. destruct (rbn9_args X HA) as (Hn0 & _).
    exists (ri_name X, if ri_name X =? 0 then ri_name X else ri_name X + Z.min (ri_name_len X) 24).
    split; [unfold rbn_FPX, rbn_fp; cbn [In]; left; reflexivity |].
    cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) Hn0). r9lia.
  + apply (rbn9_cpy_mk X pos lyc1 Sc1 W1 memc1 mdc1 _ mem4 mdc4 q2 N2 (ri_token X) 128 (Z.of_nat (length (rbm_TB X)) + 1)
      HX HM HJ4 B2); [r9lia | r9lia | | r9lia | r9lia | r9lia |
      apply (range_addressable_sub _ _ (rbn_F X pos + 128) 24); [exact RA128 | r9lia | r9lia]].
    intros a Ha. destruct (rbn9_args X HA) as (_ & Ht0 & _).
    exists (ri_token X, if ri_token X =? 0 then ri_token X else ri_token X + Z.min (ri_token_len X) 24).
    split; [unfold rbn_FPX, rbn_fp; cbn [In]; right; left; reflexivity |].
    cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) Ht0). r9lia.
  + apply (rbn9_cpy_mk X pos lyc1 Sc1 W1 memc1 mdc1 _ mem4 mdc4 q3 N3 (ri_display X) 192 (nF + 1)
      HX HM HJ4 B3); [r9lia | r9lia | | r9lia | r9lia | r9lia |
      apply (range_addressable_sub _ _ (rbn_F X pos + 192) 48); [exact RA192 | r9lia | r9lia]].
    intros a Ha. destruct (rbn9_args X HA) as (_ & _ & Hd0 & _).
    exists (ri_display X, if ri_display X =? 0 then ri_display X else ri_display X + Z.min (ri_display_len X) 48).
    split; [unfold rbn_FPX, rbn_fp; cbn [In]; right; right; left; reflexivity |].
    cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) Hd0). r9lia.
  + destruct HD12 as [Hd | Hd]; [left | right]; r9lia.
  + destruct HD13 as [Hd | Hd]; [left | right]; r9lia.
  + destruct HD23 as [Hd | Hd]; [left | right]; r9lia.
  + intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    * split; [apply BF1; r9lia | r9lia].
    * split; [apply BF2; r9lia | r9lia].
    * split; [apply BF3; r9lia | r9lia].
  + intros regs5 mem5 mdc5 HJ5 SAME5 H21_5 K5 CP1 CP2 CP3.
    destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem5 mdc5 HM HJ5) as (_ & _ & _ & _ & _ & HSpr5).
    assert (Hsh5 : rbn_shadow_at W1 mem5 (rbn_SH X pos) (rbn_sh true true true true)).
    { apply (rbn9_sh_kept W1 mem4 mem5 _ _ _ Hsh4 K5);
        [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
      intros j Hj. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta.
      intros [Hc | [Hc | [Hc | Hc]]].
      - apply (rbn9_app_sh _ (BK1 (rbn_SH X pos + j) ltac:(r9lia))). unfold kLowShadowBeg, kHighMemBeg. r9lia.
      - apply (rbn9_app_sh _ (BK2 (rbn_SH X pos + j) ltac:(r9lia))). unfold kLowShadowBeg, kHighMemBeg. r9lia.
      - apply (rbn9_app_sh _ (BK3 (rbn_SH X pos + j) ltac:(r9lia))). unfold kLowShadowBeg, kHighMemBeg. r9lia.
      - r9lia. }
    apply (rbn9_tail REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
      [(3, pos)] lyc1 Sc1 W1 mem5 mdc5 0 regs5 (rbn_A X) (rbn_F X pos) (rbn_SH X pos) _ HJ5).
    * exact (eq_trans (SAME5 9 ltac:(cbn; tauto)) (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9))).
    * exact (eq_trans (SAME5 18 ltac:(cbn; tauto)) (eq_trans (SAME4 18 ltac:(cbn; tauto)) (eq_trans (SAME3 18 ltac:(cbn; tauto)) H18))).
    * exact (eq_trans (SAME5 19 ltac:(cbn; tauto)) (eq_trans (SAME4 19 ltac:(cbn; tauto)) (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19))).
    * r9lia.
    * r9lia.
    * r9lia.
    * r9lia.
    * r9lia.
    * apply (rbn9_kept_val _ _ _ _ _ _ _ K5); [intros i Hi; cbv beta; r9lia | r9lia | r9lia |].
      apply KC4; [exact C72 | r9lia | r9lia].
    * intros a Ha. replace a with (rbn_SH X pos + (a - rbn_SH X pos)) by r9lia. apply HSpr5. r9lia.
    * intros a Ha. right; right; right. exists 3, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite FA. change (fs_frame_bytes 3 / 8) with 64. unfold rbn_SH in Ha. r9lia.
    * intros j Hj. apply rbn9_val1_of_aview.
      exact (Hsh5 j ltac:(change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia)).
    * intros regs6 mem6 mdc6 HJ6 SAME6 H26_6 K6 HSH6.
      apply SRr_ret. exists pos, regs6, lyc1, Sc1, mem6, mdc6. split; [reflexivity|].
      assert (NSH : forall a, app_addr a -> ~ (rbn_SH X pos + 4 <= a < rbn_SH X pos + 30)).
      { intros a Ha Hc. apply (rbn9_app_sh _ Ha). unfold kLowShadowBeg, kHighMemBeg. r9lia. }
      apply (rbn9_close X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs6 mem6 mdc6 HX Hst HJ6).
      -- apply (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ K14 K5) K6)).
         intros a Ha. cbv beta in Ha. unfold rbn9_W.
         destruct Ha as [[[Ha | [Ha | Ha]] | [Ha | [Ha | [Ha | Ha]]]] | Ha].
         ++ left; r9lia.
         ++ right; left; r9lia.
         ++ left; r9lia.
         ++ right; right; right. split; [exact HACC|]. left. r9lia.
         ++ right; right; right. split; [exact HACC|]. right; left. r9lia.
         ++ right; right; right. split; [exact HACC|]. right; right. r9lia.
         ++ right; left; r9lia.
         ++ right; right; left; r9lia.
      -- exact HSH6.
      -- intros r Hr. apply (rbn9_same4 regs1 regs3 regs4 regs5 regs6 _ _ _ _ r SAME3 SAME4 SAME5 SAME6);
           cbn [In] in Hr |- *; tauto.
      -- exact H26_6.
      -- rewrite HACC. exact (eq_trans (SAME6 21 ltac:(cbn; tauto)) H21_5).
      -- intros _. split; [|split].
         ++ apply (rbn9_garr8_move (w_H W1) (w_H W1) mem4 mem6 (rbn_F X pos + 64) (ri_name X)).
            ** intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
               rewrite (proj1 K6 (ri_name X + i)); [apply CP1; r9lia | r9lia |].
               apply NSH. apply BK1. r9lia.
            ** rewrite <- ENB. apply (rbn9_kept_garr W1 memc1 mem4 _ _ _ K14); [ | | | exact G64].
               --- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. cbv beta. r9lia.
               --- r9lia.
               --- rewrite length_app. cbn [length]. r9lia.
         ++ apply (rbn9_garr8_move (w_H W1) (w_H W1) mem4 mem6 (rbn_F X pos + 128) (ri_token X)).
            ** intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
               rewrite (proj1 K6 (ri_token X + i)); [apply CP2; r9lia | r9lia |].
               apply NSH. apply BK2. r9lia.
            ** rewrite <- ETB. apply (rbn9_kept_garr W1 memc1 mem4 _ _ _ K14); [ | | | exact G128].
               --- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. cbv beta.
                   pose proof HTB. r9lia.
               --- r9lia.
               --- rewrite length_app. cbn [length]. r9lia.
         ++ apply (rbn9_garr8_move (w_H W1) (w_H W1) mem4 mem6 (rbn_F X pos + 192) (ri_display X)).
            ** intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
               rewrite (proj1 K6 (ri_display X + i)); [apply CP3; r9lia | r9lia |].
               apply NSH. apply BK3. r9lia.
            ** rewrite <- EDP. apply rbn9_garr8_app.
               --- apply (rbn9_kept_garr W1 mem3 mem4 _ _ _ K4); [ | r9lia | rewrite length_app; cbn [length]; r9lia | exact GD3].
                   intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. cbv beta. r9lia.
               --- intros j Hj. cbn [length] in Hj. assert (Hj0 : j = 0%nat) by lia. subst j. cbn [nth].
                   split; [|lia].
                   replace (rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X ++ [32; 111; 117; 116; 41])) + Z.of_nat 0)
                     with (rbn_F X pos + 192 + nF) by (rewrite length_app; cbn [length]; r9lia).
                   exact V4.
Qed.
End h.
End f.
End d.
