(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit H_scanner_get_token H_map_str_to_int H_parse_uric H_match_A H_match_X H_presp_seg H_phdr_seg H_phdr H_pent_seg H_pent_kit H_germ_GL H_pparse_stmt PZDef.
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

