(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit H_scanner_get_token H_map_str_to_int H_parse_uric H_match_A H_match_X H_presp_seg H_phdr_seg H_phdr H_pent_seg H_pent_kit H_germ_GL H_pparse_stmt PZDef.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueA0_T.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Agree.
Context {HC : HasCeiling}.
Variable P : Z -> Prop.
Variables m m' : mem.
Hypothesis AG : gagree_on P m m'.
Hypothesis HP : forall a, pz_band a -> P a.

#[using="HP"] Lemma HPsh : forall a, 0x7fffa000 <= a < 0x800b9200 -> P a.
Proof. intros a Ha. apply HP. unfold pz_band. lia. Qed.

#[using="P AG HP"] Lemma shw_agree_img : forall A n, shw m A n -> 0x10000 <= A -> A + n <= 0x609000 -> shw m' A n.
Proof.
  intros A n (ACC & SR & W) HA HN. split; [| split; [| exact W]].
  - intros a Ha. destruct (ACC a Ha) as (k & BA & HK). exists k. split; [| exact HK].
    eapply bytes_at_gagree; [exact AG| exact BA|]. cbn [length]. intros x Hx. apply HPsh. unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
  - intros Hn a Ha. destruct (SR Hn a Ha) as [v Hv]. exists v.
    eapply gagree_mrd; [exact AG| | | exact Hv]; [unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia|].
    apply HPsh. unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

#[using="AG"] Lemma u64arr_agree : forall A ws, u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr asegs m' A ws.
Proof.
  intros A ws [B W] H. split.
  - eapply bytes_at_gagree; [exact AG| exact B|]. rewrite u64s_length. intros a Ha. apply H. lia.
  - eapply wr_at_gagree; [exact AG| exact W| exact H].
Qed.

#[using="P AG HP"] Lemma table_strings_agree : forall ws ne, table_strings_A m ws ne -> table_strings_A m' ws ne.
Proof.
  intros ws ne H i Hi. destruct (H i Hi) as (S & str & slack & E & B & NZ & PAD & LO & HI & SHW).
  exists S, str, slack. repeat (split; [assumption|]). apply shw_agree_img; [exact SHW| lia| lia].
Qed.

#[using="P AG HP"] Lemma gstA_agree : forall GL, Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL -> gstA GL m -> gstA GL m'.
Proof.
  intros GL HR HG. unfold gstA in *. rewrite Forall_forall in *. intros xn Hin. destruct (HR xn Hin) as [R1 R2].
  apply shw_agree_img; [exact (HG xn Hin)| exact R1| exact R2].
Qed.
End Agree.

Section AgreeTop.
Context {HC : HasCeiling}.

Ltac rc_ag AG HP := eapply rw_cells_gagree; [exact AG| eassumption| cbn [cells_size csize Nat.add]; intros a Ha; apply HP; unfold pz_band; lia].
Ltac sh_ag AG HP := eapply (shw_agree_img _ _ _ AG HP); [eassumption| unfold SEPTAB_A, A0_ERRNO, A0_FMT_SSCANF_VER; lia| unfold SEPTAB_A, A0_ERRNO, A0_FMT_SSCANF_VER; lia].

#[using="Type"] Theorem PZ_of_agree : forall GL (P : Z -> Prop) (m m' : mem),
  gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ_of GL m -> PZ_of GL m'.
Proof.
  intros GL P m m' AG HP (ws & mws & cslack & LWS & IDS & MOK & GLR & HM).
  exists ws, mws, cslack. split; [exact LWS|]. split; [exact IDS|]. split; [exact MOK|]. split; [exact GLR|].
  destruct HM as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20).
  unfold pz_mem.

  split.
  { destruct A1 as ((HU & HS & HT) & S1 & S2 & CB & CL & S3 & ZB & S4). unfold H_phdr.phdr_statics, H_phdr_seg.hstat.
    split; [split; [| split]|].
    - eapply (u64arr_agree _ _ _ AG); [exact HU|]. rewrite LWS. intros a Ha. apply HP. unfold pz_band. lia.
    - sh_ag AG HP.
    - exact (table_strings_agree _ _ _ AG HP _ _ HT).
    - split; [sh_ag AG HP|]. split; [sh_ag AG HP|]. split; [exact CB|]. split; [exact CL|]. split; [sh_ag AG HP|].
      split; [| sh_ag AG HP].
      eapply bytes_at_gagree; [exact AG| exact ZB|]. cbn [length]. intros a Ha. apply HP. unfold pz_band. lia. }
  split; [exact (gstA_agree _ _ _ AG HP GL GLR A2)|].
  split; [sh_ag AG HP|]. split; [sh_ag AG HP|].
  split.
  { destruct A5 as (G1 & G2 & G3 & G4). unfold H_pent_seg.pstatE. split; [rc_ag AG HP|]. split; [rc_ag AG HP|]. split; [sh_ag AG HP| rc_ag AG HP]. }
  split; [sh_ag AG HP|]. split; [sh_ag AG HP|]. split; [sh_ag AG HP|]. split; [sh_ag AG HP|]. split; [sh_ag AG HP|].
  split.
  { destruct MOK as [LM _]. eapply (u64arr_agree _ _ _ AG); [exact A11|]. rewrite LM. intros a Ha. apply HP. unfold pz_band. lia. }
  split; [sh_ag AG HP|].
  split; [exact (table_strings_agree _ _ _ AG HP _ _ A13)|].
  split; [sh_ag AG HP|]. split; [sh_ag AG HP|]. split; [sh_ag AG HP|]. split; [sh_ag AG HP|].
  split; [rc_ag AG HP|].
  split; [destruct A19 as [gv G]; exists gv; rc_ag AG HP|].
  sh_ag AG HP.
Qed.
End AgreeTop.

Definition fact_k (f : mfact) : option (Z * Z) :=
  match f with MCell (ZLit a) 1%nat (ZLit k) => Some (a, k) | _ => None end.
Lemma fact_k_sound : forall V (m : mem) f a k, mfact_ok asegs V m f -> fact_k f = Some (a, k) -> bytes_at asegs m a [Z_to_bv 8 k].
Proof.
  intros V m f a k OK E. destruct f as [e w v|e n|e w v|e n|e n c|lo hi|e n|e n|e n]; cbn [fact_k] in E; try discriminate.
  destruct e as [z0| | | | |]; try discriminate. destruct w as [|[|w]]; try discriminate. destruct v as [k0| | | | |]; try discriminate.
  injection E as <- <-. cbn [mfact_ok zv cellw] in OK. destruct OK as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Fixpoint acc_chk (l : list mfact) (fuel : nat) (A hi : Z) : bool :=
  if hi <=? A then true else
  match fuel with
  | O => false
  | S fuel' =>
      let gend := Z.min hi (8 * (A / 8) + 8) in
      let x := A / 8 + 0x7fff8000 in
      (cover true l 2 x (x + 1)
       || existsb (fun f => match fact_k f with Some (a, k) => (a =? x) && (0 <? k) && (k <? 8) && ((gend - 1) mod 8 <? k) | None => false end) l)
      && acc_chk l fuel' gend hi
  end.
Lemma acc_chk_sound : forall V (m : mem) l fuel A hi, Forall (mfact_ok asegs V m) l -> 0 <= A -> hi <= 2^61 -> acc_chk l fuel A hi = true ->
  forall a, A <= a < hi -> acc m a.
Proof.
  intros V m l fuel. induction fuel as [|fuel IH]; intros A hi HF HA HH H a Ha; cbn [acc_chk] in H;
    (destruct (Z.leb_spec0 hi A); [lia|]); [discriminate|].
  apply andb_prop in H as [H1 H2].
  set (gend := Z.min hi (8 * (A / 8) + 8)) in *. set (x := A / 8 + 0x7fff8000) in *.
  destruct (Z.lt_ge_cases a gend) as [LT|GE]; [| apply (IH gend hi HF ltac:(subst gend; Z.div_mod_to_equations; lia) HH H2 a); lia].
  assert (SA : sh a = x) by (unfold sh, SHADOW_OFF; subst x gend; Z.div_mod_to_equations; lia).
  apply orb_prop in H1 as [C|E].
  - destruct (cover_sound V m true l 2 x (x + 1) HF C x ltac:(lia)) as [_ Z0]. specialize (Z0 eq_refl).
    exists 0. split; [| left; reflexivity]. rewrite SA. split; [subst x; Z.div_mod_to_equations; lia|]. split; [cbn [length]; subst x; Z.div_mod_to_equations; lia|].
    intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r. exact Z0.
  - apply existsb_exists in E as (f & Hin & Hf). destruct (fact_k f) as [[a0 k]|] eqn:FK; [| discriminate].
    apply andb_prop in Hf as [Hf K4]. apply andb_prop in Hf as [Hf K3]. apply andb_prop in Hf as [K1 K2].
    apply Z.eqb_eq in K1. apply Z.ltb_lt in K2. apply Z.ltb_lt in K3. apply Z.ltb_lt in K4. subst a0.
    pose proof (fact_k_sound V m f x k (proj1 (Forall_forall _ _) HF f Hin) FK) as B.
    exists k. split; [rewrite SA; exact B|]. right. split; [lia|]. subst gend. Z.div_mod_to_equations. lia.
Qed.

Lemma shw_init : forall V (m : mem) l A n f1 f2, Forall (mfact_ok asegs V m) l -> 0 < n -> 4096 <= A -> A + n <= 0x7fff7000 ->
  acc_chk l f1 A (A + n) = true ->
  cover false l f2 (sh A - sh A mod 8) (sh (A + n - 1) - sh (A + n - 1) mod 8 + 8) = true ->
  shw m A n.
Proof.
  intros V m l A n f1 f2 HF Hn HA HN C1 C2. split; [| split].
  - exact (acc_chk_sound V m l f1 A (A + n) HF ltac:(lia) ltac:(lia) C1).
  - intros _ a Ha. exact (proj1 (cover_sound V m false l f2 _ _ HF C2 a Ha)).
  - split; [lia| left; lia].
Qed.
Ltac shw_lit V m HM A n := apply (shw_init V m _ A n 400%nat 400%nat HM); [lia| lia| lia| vm_compute; reflexivity| vm_compute; reflexivity].

Definition HDR_WS_A : list word := map (Z_to_bv 64)
  [0x213e0; 25; 0x21400; 27; 0x21420; 26; 0x21440; 28; 0x21460; 29; 0x21480; 1; 0x214a0; 2; 0x214c0; 30; 0x21500; 31; 0x21540; 3; 0x21560; 32; 0x215a0; 33; 0x215c0; 4; 0x215e0; 5; 0x21600; 6; 0x21620; 7; 0x21640; 34; 0x21660; 11; 0x21680; 12; 0x216a0; 13; 0x216c0; 14; 0x216e0; 15; 0x21700; 35; 0x21720; 17; 0x21740; 16; 0x21760; 18; 0x21780; 19; 0x217a0; 20; 0x217c0; 36; 0x217e0; 21; 0x21800; 22; 0x21840; 24; 0x21860; 23]%Z.
Definition MT_WS_A : list word := map (Z_to_bv 64)
  [0x21b00; 1; 0x21b20; 2; 0x21b40; 3; 0x21b60; 5; 0x21b80; 9; 0x21ba0; 8; 0x21bc0; 4; 0x21be0; 6; 0x21c00; 7; 0x21bc0; 11; 0x21c20; 0]%Z.

Fixpoint img_cstrA (S : Z) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom asegs (wa S) with
           | Some b => if (bv_unsigned b =? 0)%Z then [] else b :: img_cstrA (S + 1) f
           | None => []
           end
  end.
Definition img_padA (S : Z) (len : nat) : list byte :=
  match image_bytes asegs (S + Z.of_nat len + 1) (Z.to_nat ((- (S + Z.of_nat len + 1)) mod 8)) with Some bs => bs | None => [] end.
Lemma notin_zeroA : forall (l : list byte), existsb (fun b => (bv_unsigned b =? 0)%Z) l = false -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H IN. apply Bool.not_true_iff_false in H. apply H. apply existsb_exists. exists (Z_to_bv 8 0). split; [exact IN| reflexivity].
Qed.
Lemma rodata_bytes_atA : forall (m : mem) A bs,
  mem_inv asegs m -> ro_bytes_b asegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z -> bytes_at asegs m A bs.
Proof.
  intros m A bs MI RB HA HL. pose proof (ro_cells_image asegs m A bs MI RB HA HL) as [_ B].
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Fixpoint allzA (p : Z -> Prop) (n : nat) (j : Z) : Prop :=
  match n with O => True | S n' => p j /\ allzA p n' (j + 1) end.
Lemma allzA_sound : forall p n j, allzA p n j -> forall i, (j <= i < j + Z.of_nat n)%Z -> p i.
Proof.
  induction n as [|n IH]; intros j H i Hi; [cbn in Hi; lia|]. destruct H as [H0 H1].
  destruct (Z.eq_dec i j) as [->|NE]; [exact H0|]. apply (IH (j + 1)%Z H1). lia.
Qed.

Section Init.
Context {HC : HasCeiling}.
Variable V : nat -> Z.
Variable m : mem.
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.

Definition entry_okA (ws : list word) (i : Z) : Prop :=
  exists S str slack,
    nth_error ws (Z.to_nat (2 * i)) = Some (Z_to_bv 64 S)
    /\ (forall m', mem_inv asegs m' -> bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack)) /\ ~ In (Z_to_bv 8 0) str
    /\ ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z
    /\ 0x10000 <= S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x609000
    /\ shw m S (Z.of_nat (length str) + 1).
Ltac zlen_liaA := repeat match goal with |- context [Z.of_nat ?l] => let v := eval vm_compute in (Z.of_nat l) in change (Z.of_nat l) with v end; first [lia | (Z.div_mod_to_equations; lia)].
Ltac solve_entryA S :=
  exists S, (img_cstrA S 40), (img_padA S (length (img_cstrA S 40)));
  split; [vm_compute; reflexivity|];
  split; [intros m' MI; apply (rodata_bytes_atA m'); [exact MI| vm_compute; reflexivity| lia| zlen_liaA]|];
  split; [apply notin_zeroA; vm_compute; reflexivity|];
  split; [zlen_liaA|]; split; [lia|]; split; [zlen_liaA|];
  let n := eval vm_compute in (Z.of_nat (length (img_cstrA S 40)) + 1) in
  change (Z.of_nat (length (img_cstrA S 40)) + 1) with n; shw_lit V m HM S n.

Lemma hdr_entriesA : forall i, (0 <= i < 33)%Z -> entry_okA HDR_WS_A i.
Proof using HM.
  apply (allzA_sound (entry_okA HDR_WS_A) 33 0). cbn [allzA Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- entry_okA _ ?i =>
         let S := eval vm_compute in (match nth_error HDR_WS_A (Z.to_nat (2 * i)) with Some w => bv_unsigned w | None => 0%Z end) in
         solve_entryA S end.
Qed.
Lemma mt_entriesA : forall i, (0 <= i < 11)%Z -> entry_okA MT_WS_A i.
Proof using HM.
  apply (allzA_sound (entry_okA MT_WS_A) 11 0). cbn [allzA Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- entry_okA _ ?i =>
         let S := eval vm_compute in (match nth_error MT_WS_A (Z.to_nat (2 * i)) with Some w => bv_unsigned w | None => 0%Z end) in
         solve_entryA S end.
Qed.
#[using="Type"] Lemma hdr_idsA : forall i, (0 <= i < 33)%Z -> exists id, nth_error HDR_WS_A (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 64 id) /\ (0 <= id < 64)%Z.
Proof.
  apply (allzA_sound _ 33 0). cbn [allzA Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- exists id, nth_error _ ?k = _ /\ _ =>
         let v := eval vm_compute in (match nth_error HDR_WS_A k with Some w => bv_unsigned w | None => 0%Z end) in
         exists v; split; [vm_compute; reflexivity| lia] end.
Qed.
#[using="Type"] Lemma mt_idsA : forall i, (0 <= i < 11)%Z -> exists id, nth_error MT_WS_A (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 64 id) /\ (0 <= id <= 11)%Z.
Proof.
  apply (allzA_sound _ 11 0). cbn [allzA Z.add Pos.add Pos.succ].
  repeat lazymatch goal with |- _ /\ _ => split | |- True => exact I end.
  all: lazymatch goal with |- exists id, nth_error _ ?k = _ /\ _ =>
         let v := eval vm_compute in (match nth_error MT_WS_A k with Some w => bv_unsigned w | None => 0%Z end) in
         exists v; split; [vm_compute; reflexivity| lia] end.
Qed.

Lemma u64arr_img : forall A ws,
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (length (u64s ws)) <=? hi') | _ => false end) asan_mem_facts = true ->
  img_bytes_b A (u64s ws) = true -> 0xa9000 <= A -> A + 8 * Z.of_nat (length ws) <= 0x609000 -> u64arr asegs m A ws.
Proof using HM.
  intros A ws HE HB HA HH. pose proof (u64s_length ws) as L. split.
  - eapply aimg_bytes; [exact HM| exact HE| exact HB| lia| lia].
  - apply a0_rw_image_wr_at; lia.
Qed.

Theorem PZ_of_init : forall GL, Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL -> gstA GL m -> PZ_of GL m.
Proof using HM.
  intros GL GLR GST.
  exists HDR_WS_A, MT_WS_A, (match image_bytes asegs 0x218e3 5 with Some bs => bs | None => [] end).
  split; [reflexivity|]. split; [exact hdr_idsA|]. split; [split; [reflexivity| exact mt_idsA]|]. split; [exact GLR|].
  unfold pz_mem.

  split.
  { unfold H_phdr.phdr_statics, H_phdr_seg.hstat.
    split; [split; [| split]|].
    - apply u64arr_img; [vm_compute; reflexivity| vm_compute; reflexivity| lia| cbn; lia].
    - shw_lit V m HM 0xae6c0 528.
    - intros i Hi. destruct (hdr_entriesA i Hi) as (S & str & slack & H1 & H2 & H3 & H4 & H5 & H6 & H7). exists S, str, slack. repeat (split; [assumption|]). exact H7.
    - split; [unfold SEPTAB_A; shw_lit V m HM 0x219c0 20|]. split; [shw_lit V m HM 0x218c0 8|].
      split; [intros m' MI; apply (rodata_bytes_atA m'); [exact MI| vm_compute; reflexivity| lia| zlen_liaA]|].
      split; [zlen_liaA|]. split; [shw_lit V m HM 0x218e0 3|].
      split; [| shw_lit V m HM 0x5e5f80 1].
      aimg V m HM 0x5e5f80 [C1 (Z_to_bv 8 0)] ZC. destruct ZC as [[_ ZB] _]. cbn [cells_bytes cbytes] in ZB. rewrite app_nil_r in ZB. exact ZB. }
  split; [exact GST|].
  split; [shw_lit V m HM 0x21a00 7|]. split; [shw_lit V m HM 0x21a60 3|].
  split.
  { unfold H_pent_seg.pstatE. aimg V m HM 0xaad50 [C8 (Z_to_bv 64 0xaea60)] G1. aimg V m HM 0xaea60 [C8 (Z_to_bv 64 64000)] G2. aimg V m HM 0x5e5fc0 [C1 (Z_to_bv 8 0)] G4.
    split; [exact G1|]. split; [exact G2|]. split; [shw_lit V m HM 0xaea60 8| exact G4]. }
  split; [shw_lit V m HM 0x21880 16|]. split; [shw_lit V m HM 0x218a0 11|].
  split; [shw_lit V m HM 0x21a80 10|]. split; [shw_lit V m HM 0x21aa0 22|]. split; [unfold A0_FMT_SSCANF_VER; shw_lit V m HM 0x21ae0 8|].
  split; [apply u64arr_img; [vm_compute; reflexivity| vm_compute; reflexivity| lia| cbn; lia]|].
  split; [shw_lit V m HM 0xae960 176|].
  split; [intros i Hi; destruct (mt_entriesA i Hi) as (S & str & slack & H1 & H2 & H3 & H4 & H5 & H6 & H7); exists S, str, slack; repeat (split; [assumption|]); exact H7|].
  split; [shw_lit V m HM 0x21ca0 6|]. split; [shw_lit V m HM 0xaea40 4|]. split; [shw_lit V m HM 0x21c80 10|]. split; [shw_lit V m HM 0x21cc0 13|].
  split; [aimg V m HM 0xaad48 [C8 (Z_to_bv 64 0xaea40)] G; exact G|].
  split; [exists (Z_to_bv 64 0xffffffff); aimg V m HM 0xaea40 [C4 (Z_to_bv 64 0xffffffff)] G; exact G|].
  unfold A0_ERRNO. shw_lit V m HM 0x5e68cc 4.
Qed.
End Init.

Theorem PZ_agree : forall (P : Z -> Prop) (m m' : mem), gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
Proof. intros P m m' AG HP H. exact (PZ_of_agree GL_germ P m m' AG HP H). Qed.

Theorem PZ_INIT : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> PZ m.
Proof.
  intros V m HM. apply (PZ_of_init V m HM GL_germ GL_germ_image).
  unfold gstA, GL_germ. constructor; [| constructor]. cbn [fst snd]. shw_lit V m HM 0x21900 8.
Qed.
