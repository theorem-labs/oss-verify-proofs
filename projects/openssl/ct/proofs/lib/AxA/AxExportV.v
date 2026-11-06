(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Mem Frame RzCPS.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxBytes AxMem AxZZ AxScan AxState AxSys AxAcct AxMeasure AxLz AxGrant AxPostFix AxFd AxModelRel.
From OSSVerify.Proofs.openssl.ct.lib.AxA Require Import AxExport AxExportM AxExportH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section ExportV.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable X : list (Z * Z).

Let HM : MR segs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.

(* [comment removed for export] *)
Definition AF : list (Z * Z) := A' ρ W J ++ X.

Local Notation mX := (AxExport.mX ms model AF).
Local Notation vis := (AxExport.vis model AF).

Lemma allowed_l (p : word) : page_allowedb (A' ρ W J) p = true -> page_allowedb AF p = true.
Proof. unfold page_allowedb, AF. rewrite existsb_app. intros ->. reflexivity. Qed.

Lemma allowed_r (p : word) : page_allowedb X p = true -> page_allowedb AF p = true.
Proof. unfold page_allowedb, AF. rewrite existsb_app. intros ->. apply orb_true_r. Qed.

Lemma HID_AF (a : word) : RzCPS.HID (A' ρ W J) model a = false -> RzCPS.HID AF model a = false.
Proof.
  intros H. destruct (RzCPS.HID AF model a) eqn:E; [|reflexivity].
  rewrite (RzCPS.HID_mono (A' ρ W J) AF model a allowed_l E) in H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma vis_X (lo hi z : Z) : In (lo, hi) X -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= z < hi -> 0 <= z < 2 ^ 47 ->
  RzCPS.HID AF model (wz z) = false.
Proof.
  intros HIn Hlo Hhi Hz Hr. pose proof (u_wz' z Hr) as Eu.
  destruct (page_in_aligned (wz z) lo hi Hlo Hhi ltac:(rewrite Eu; exact Hz)) as [P1 P2].
  unfold RzCPS.HID, mkH. rewrite (allowed_r (page_base (wz z))).
  - rewrite andb_false_r. cbn [orb]. apply Z.leb_gt. rewrite Eu. lia.
  - unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact HIn|]. cbn [fst snd]. unfold page_size.
    apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vis_w (f : lin) (n : Z) : bool :=
  existsb (fun w => teqb (snd (fst w)) (snd f) &&& (fst (fst w) <=? fst f) &&& (fst f + n <=? fst (fst w) + snd w) &&& w_ok w) W.

(* [comment removed for export] *)
Definition vis_img (top : Z) (f : lin) (n : Z) : bool :=
  match snd f with [] => (fst f + n <=? top) &&& big_top_ok B top | _ => false end.

(* [comment removed for export] *)
Definition vis_stk (f : lin) : bool :=
  teqb (snd (am_atop (a_model B))) (snd f) &&& (fst (am_atop (a_model B)) <=? fst f).

Definition vis_ok (top : Z) (f : lin) (n : Z) : bool :=
  match lrange (a_facts B) f with
  | Some (lo, hi) => (0 <=? lo) &&& (hi + n <=? 140737488355328) &&& (vis_w f n ||| vis_img top f n ||| vis_stk f)
  | None => false
  end.

Lemma not_in_entries_vis (z : Z) : 0 <= z < 2 ^ 47 ->
  (forall e, In e (am_maps (a_model B)) -> BIGMIN <= ae_size e -> ~ (ent_lo ρ e <= z < ent_hi ρ e)) ->
  RzCPS.HID AF model (wz z) = false.
Proof. intros Hz H. apply HID_AF. exact (vis_notbig segs fs0 LIM ρ B ms model HR W J z Hz H). Qed.

Theorem vis_ok_sound (top : Z) (f : lin) (n : Z) : vis_ok top f n = true ->
  0 <= leval ρ f /\ leval ρ f + n <= 2 ^ 47 /\ vis (leval ρ f) (leval ρ f + n).
Proof.
  unfold vis_ok. destruct (lrange (a_facts B) f) as [[lo hi]|] eqn:El; [|discriminate]. intros H.
  apply land_true in H as [H Hv]. apply land_true in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (lrange_sound ρ _ _ Hsat _ El) as Xr. cbn [fst snd] in Xr. change (2 ^ 47) with 140737488355328.
  split; [lia|]. split; [lia|]. intros z Hz.
  apply lor_true in Hv as [Hv|Hv]; [apply lor_true in Hv as [Hv|Hv]|].
  - (* [comment removed for export] *)
    unfold vis_w in Hv. apply existsb_exists in Hv as [w [Hw Hb]].
    apply land_true in Hb as [Hb Hok]. apply land_true in Hb as [Hb H5]. apply land_true in Hb as [H3 H4].
    apply teqb_eq in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
    apply HID_AF. apply (vis_win ρ model W J w z Hw Hok ltac:(lia)).
    destruct w as [[cw tw] nw]. destruct f as [cf tf]. unfold leval in *. cbn [fst snd] in *. subst tw. lia.
  - (* [comment removed for export] *)
    unfold vis_img in Hv. destruct f as [c ts]. cbn [fst snd] in *. destruct ts; [|discriminate Hv].
    apply land_true in Hv as [H3 Hbt]. apply Z.leb_le in H3. unfold leval in Hz, Xr. cbn [fst snd teval] in Hz, Xr.
    apply not_in_entries_vis; [lia|]. intros e He Hbig Hin.
    pose proof (ex_big_top segs fs0 LIM ρ B ms model HR top Hbt e He Hbig) as Y. unfold ent_lo in Hin. lia.
  - (* [comment removed for export] *)
    unfold vis_stk in Hv. apply land_true in Hv as [H3 H4]. apply teqb_eq in H3. apply Z.leb_le in H4.
    apply not_in_entries_vis; [lia|]. intros e He _ Hin.
    pose proof (mr_top segs fs0 ρ _ model HM (ent_val ρ e) (MR_ent_in segs fs0 ρ _ model e HM He)) as Ht.
    pose proof (MR_ent segs fs0 ρ _ model e HM He) as Hok.
    rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok), (mr_atop segs fs0 ρ _ model HM) in Ht.
    unfold ent_lo, ent_hi in Hin. destruct (am_atop (a_model B)) as [ca ta]. destruct f as [cf tf]. unfold leval in *. cbn [fst snd] in *. subst ta. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis Hpos : forall C, In C (a_mem B) -> 0 < to_Z (rg_n C).
Hypothesis HwL : has_wit (a_facts B) ls_beg ls_end (a_mem B) = true.
Hypothesis HwH : has_wit (a_facts B) hs_beg hs_hi (a_mem B) = true.

Let Hrm : RMem segs ρ (a_mem B) (ms_mem ms) := r_mem _ _ _ _ _ _ _ HR.
Let Hhs : hs_ok ρ (a_mem B) (ms_mem ms) := r_hs _ _ _ _ _ _ _ HR.

(* [comment removed for export] *)
Theorem sh_present (z : Z) : in_ss z -> ms_mem ms (wz z) <> None.
Proof.
  intros [Hz|Hz].
  - destruct (has_wit_sound ρ _ ls_beg ls_end _ Hsat ltac:(unfold ls_beg; lia) ltac:(unfold ls_end, FastWord.two64; lia) HwL) as (W0 & w0 & HW0 & Hs0 & Hin0 & Hr0).
    apply (ss_mapped segs Hlow ρ _ _ W0 w0 z Hrm Hhs HW0 Hs0 Hin0). left. split; assumption.
  - destruct (has_wit_sound ρ _ hs_beg hs_hi _ Hsat ltac:(unfold hs_beg; lia) ltac:(unfold hs_hi, FastWord.two64; lia) HwH) as (W0 & w0 & HW0 & Hs0 & Hin0 & Hr0).
    apply (ss_mapped segs Hlow ρ _ _ W0 w0 z Hrm Hhs HW0 Hs0 Hin0). right. split; assumption.
Qed.

(* [comment removed for export] *)
Theorem sh_bg_zero (z : Z) : in_ss z -> (forall C, In C (a_mem B) -> is_shadow C = true -> ~ in_rg ρ C z) ->
  ms_mem ms (wz z) = Some (Z_to_bv 8 0).
Proof.
  intros Hz Hout. destruct (hs_old_of_pos ρ _ _ Hpos Hhs) as (_ & Hbg & _).
  destruct (Hbg z Hz Hout) as [Hn|H0]; [exfalso; exact (sh_present z Hz Hn) | exact H0].
Qed.

(* [comment removed for export] *)
Lemma sh_zero_in (C : region) (z : Z) : In C (a_mem B) -> is_shadow C = true -> iall cell_is0 (rg_cells C) = true -> in_rg ρ C z ->
  ms_mem ms (wz z) = Some (Z_to_bv 8 0).
Proof.
  intros HC HsC Ez HinC.
  assert (HeC : is_entry C = false) by (unfold is_shadow, is_entry in *; destruct (rg_kind C); try reflexivity; discriminate HsC).
  destruct Hrm as [Hrok HF]. pose proof (proj1 (Forall_forall _ _) HF C HC) as HRC. rewrite (RRegion_ne segs ρ _ C HeC) in HRC.
  destruct (regions_ok_in ρ _ C Hrok HC) as (W1 & W2 & _). unfold in_rg in HinC.
  pose proof (smod_range ρ (rg_ts C) (rg_bo C)) as Sb. fold (rbase ρ C) in Sb.
  set (y := of_Z (z - rbase ρ C)). assert (Ey : to_Z y = z - rbase ρ C) by (unfold y; apply phi_of_Z_small; lia).
  destruct (HRC y ltac:(lia)) as [[b [Hb Hx]] _]. replace (rbase ρ C + to_Z y) with z in Hb by lia.
  assert (Hb0 : rbyte segs C y = BL 0%uint63).
  { unfold rbyte. unfold get_cell_opt. destruct (iget (rg_d C) (rg_cells C) (y >> 3)%uint63) as [c|] eqn:Eg.
    - apply (cell_is0_byte c _ (iall_iget cell_is0 _ _ _ c Ez Eg)). apply i2n_lt8.
    - unfold is_shadow in HsC. destruct (rg_kind C); try discriminate HsC. reflexivity. }
  rewrite Hb0 in Hx. rewrite (xb_lit ρ _ b Hx) in Hb. change (to_Z 0%uint63) with 0 in Hb.
  assert (Hss : in_ss z).
  { destruct (r_comp _ _ _ _ _ _ _ HR C HC HsC z ltac:(unfold in_rg; lia)) as [S _]. exact S. }
  apply (rv_shadow segs Hlow ms z _ ltac:(unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, FastWord.two64 in *; lia) Hb).
Qed.

Lemma in_sh_dec_l (l0 : list region) (z : Z) : (exists C, In C l0 /\ is_shadow C = true /\ in_rg ρ C z)
                          \/ (forall C, In C l0 -> is_shadow C = true -> ~ in_rg ρ C z).
Proof.
  clear. induction l0 as [|C l IH]; [right; intros C []|].
  destruct IH as [[C0 [H0 Y]]|IH]; [left; exists C0; split; [right; exact H0 | exact Y]|].
  destruct (is_shadow C) eqn:Es.
  - unfold in_rg. destruct (Z_le_dec (rbase ρ C) z) as [L1|L1]; [destruct (Z_lt_dec z (rbase ρ C + to_Z (rg_n C))) as [L2|L2]|].
    + left. exists C. split; [left; reflexivity | split; [exact Es | lia]].
    + right. intros C0 [<-|H0] Hs0; [unfold in_rg; lia | exact (IH C0 H0 Hs0)].
    + right. intros C0 [<-|H0] Hs0; [unfold in_rg; lia | exact (IH C0 H0 Hs0)].
  - right. intros C0 [<-|H0] Hs0; [rewrite Es in Hs0; discriminate | exact (IH C0 H0 Hs0)].
Qed.

Definition in_sh_dec (z : Z) := in_sh_dec_l (a_mem B) z.

(* [comment removed for export] *)
Theorem sh_vis (z : Z) : in_ss z -> RzCPS.HID AF model (wz z) = false ->
  (exists b, Mem.mrd segs mX (wz z) = Some b) /\ wview segs mX (wz z) <> None /\ mX (wz z) <> None.
Proof.
  intros Hz Hv. pose proof (sh_present z Hz) as Hp.
  assert (E : mX (wz z) = ms_mem ms (wz z)) by (unfold AxExport.mX, mrestrict; rewrite Hv; reflexivity).
  destruct (ms_mem ms (wz z)) as [b|] eqn:Eb; [|contradiction].
  split; [exists b; unfold Mem.mrd; rewrite E; reflexivity|]. split; [unfold wview; rewrite E; discriminate | rewrite E; discriminate].
Qed.

Corollary sh_stk (lo hi : Z) : (forall z, lo <= z < hi -> in_ss z) -> vis lo hi -> 0 <= lo -> hi <= 2 ^ 64 -> Frame.stk segs mX lo hi.
Proof.
  intros Hss Hvis H0 H1. unfold Frame.stk. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (sh_vis a (Hss a Ha) (Hvis a Ha)) as (Hb & Hw & _). split; [exact Hw | exact Hb].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition app_hi (C : region) : lin := laddc (lscale 8 (laddc (wZ (rg_bo C), rg_ts C) (- sh_off))) (8 * to_Z (rg_n C)).

Definition below_atop (C : region) : bool :=
  match lrange (a_facts B) (wZ (rg_bo C), rg_ts C) with
  | Some (lo, hi) =>
      (0 <=? lo) &&& (hi <? 18446744073709551616)
      &&& (match lrange (a_facts B) (lsub (am_atop (a_model B)) (app_hi C)) with Some (l, _) => 0 <=? l | None => false end
           ||| existsb (fun e => match lrange (a_facts B) (lsub (laddc (ae_base e) (ae_size e)) (app_hi C)) with
                                 | Some (l, _) => 0 <=? l | None => false end) (am_maps (a_model B)))
  | None => false
  end.

Definition stksh_ok : bool :=
  match lrange (a_facts B) (am_atop (a_model B)) with
  | Some (lo, _) => (hs_beg <=? lo / 8 + sh_off)
  | None => false
  end
  &&& forallb (fun C => negb (is_shadow C) ||| iall cell_is0 (rg_cells C) ||| below_atop C) (a_mem B).

Lemma leval_app_hi (C : region) : leval ρ (app_hi C) = 8 * (wZ (rg_bo C) + teval ρ (rg_ts C) - sh_off + to_Z (rg_n C)).
Proof.
  unfold app_hi. rewrite leval_laddc, leval_lscale, leval_laddc. unfold leval. cbn [fst snd]. lia.
Qed.

Theorem stack_shadow_zero : stksh_ok = true ->
  forall z, alloc_top (m_vmmaps model) / 8 + sh_off <= z < hs_hi -> ms_mem ms (wz z) = Some (Z_to_bv 8 0).
Proof.
  unfold stksh_ok. intros H z Hz. apply land_true in H as [Ha Hall]. rewrite forallb_forall in Hall.
  rewrite (mr_atop segs fs0 ρ _ model HM) in Hz.
  destruct (lrange (a_facts B) (am_atop (a_model B))) as [[alo ahi]|] eqn:Ea; [|discriminate Ha]. apply Z.leb_le in Ha.
  pose proof (lrange_sound ρ _ _ Hsat _ Ea) as Xa. cbn [fst snd] in Xa.
  assert (Hss : in_ss z).
  { right. split; [|lia]. pose proof (Z.div_le_mono alo (leval ρ (am_atop (a_model B))) 8 ltac:(lia) ltac:(lia)). lia. }
  destruct (in_sh_dec z) as [[C [HC [HsC HinC]]]|Hout]; [|exact (sh_bg_zero z Hss Hout)].
  specialize (Hall C HC). rewrite HsC in Hall. cbn [negb] in Hall. cbv iota in Hall.
  apply lor_true in Hall as [Hall|Hall].
  - exact (sh_zero_in C z HC HsC Hall HinC).
  - exfalso. unfold below_atop in Hall.
    destruct (lrange (a_facts B) (wZ (rg_bo C), rg_ts C)) as [[lo hi]|] eqn:El; [|discriminate Hall].
    apply land_true in Hall as [Hall Hb]. apply land_true in Hall as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
    pose proof (lrange_sound ρ _ _ Hsat _ El) as Xc. cbn [fst snd] in Xc. unfold leval in Xc. cbn [fst snd] in Xc.
    assert (Eb : rbase ρ C = wZ (rg_bo C) + teval ρ (rg_ts C)).
    { unfold rbase, smod. rewrite Z.mod_small by (unfold FastWord.two64; lia). lia. }
    assert (Hle : leval ρ (app_hi C) <= leval ρ (am_atop (a_model B))).
    { apply lor_true in Hb as [Hb|Hb].
      - destruct (lrange (a_facts B) (lsub (am_atop (a_model B)) (app_hi C))) as [[l h]|] eqn:E1; [|discriminate Hb]. apply Z.leb_le in Hb.
        pose proof (lrange_sound ρ _ _ Hsat _ E1) as Y. cbn [fst snd] in Y. rewrite leval_lsub in Y. lia.
      - apply existsb_exists in Hb as [e [He Hb]].
        destruct (lrange (a_facts B) (lsub (laddc (ae_base e) (ae_size e)) (app_hi C))) as [[l h]|] eqn:E1; [|discriminate Hb]. apply Z.leb_le in Hb.
        pose proof (lrange_sound ρ _ _ Hsat _ E1) as Y. cbn [fst snd] in Y. rewrite leval_lsub, leval_laddc in Y.
        pose proof (mr_top segs fs0 ρ _ model HM (ent_val ρ e) (MR_ent_in segs fs0 ρ _ model e HM He)) as Ht.
        pose proof (MR_ent segs fs0 ρ _ model e HM He) as Hok.
        rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok), (mr_atop segs fs0 ρ _ model HM) in Ht. lia. }
    rewrite leval_app_hi in Hle. unfold in_rg in HinC. rewrite Eb in HinC.
    pose proof (Z.div_le_lower_bound (leval ρ (am_atop (a_model B))) 8 (wZ (rg_bo C) + teval ρ (rg_ts C) - sh_off + to_Z (rg_n C)) ltac:(lia) Hle). lia.
Qed.

End ExportV.
