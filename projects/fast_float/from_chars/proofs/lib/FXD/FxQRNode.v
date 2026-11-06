(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChEnt FxChStart.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition lal64 (b : lin) : bool := (forallb (fun p => Z.eqb (snd p mod 64) 0) (l_t b) && Z.eqb (l_c b mod 64) 0)%bool.
Definition qcr_z1 (fs : list fact) (rgs : list region) (b : lin) (nhi : Z) (R0 : region) : bool :=
  let base := rg_base R0 in
  if lal64 base then
    let '(dlo, dhi) := irange fs (lsub b base) in
    if (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool then
      match srl_lin fs 3 base with
      | Some q => existsb (zero_ov fs (laddc q (SH_OFF + 8 * (dlo / 64))) (8 * ((dhi + nhi - 1) / 64 - dlo / 64 + 1))) rgs
      | None => false
      end
    else false
  else false.
Definition qcr_zero (fs : list fact) (rgs : list region) (b : lin) (nhi : Z) : bool :=
  match is_const b with
  | Some c => let lo := 8 * ((SH_OFF + c / 8) / 8) in let hi := 8 * ((SH_OFF + (c + nhi - 1) / 8) / 8) + 8 in
              existsb (zero_ov fs (lconst lo) (hi - lo)) rgs
  | None => existsb (qcr_z1 fs rgs b nhi) rgs
  end.
Definition qcr_chk (img : tree Z) (q : qsite) (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (qs_rB q)) in
  match s_resv S, is_const (rget (s_regs S) (rkey (qs_rP q))) with
  | RNone, Some P =>
      let '(nlo, nhi) := irange fs (lsub (rget (s_regs S) (rkey (qs_rA q))) b) in
      (Z.eqb (s_pc S) (qs_pc0 q) && Z.leb 1 nlo && Z.leb nhi 64 && lwf (s_next S) b &&
       match load_at img fs rgs (lconst P) SZ8 false with Some (Some sl) => lin_eqb sl (lconst SH_OFF) | _ => false end &&
       Z.leb (snd (irange fs (rget (s_regs S) (rkey (qs_rA q))))) 0x800000000000 &&
       Z.leb (snd (irange fs b)) 0x800000000000 &&
       qcr_zero fs rgs b nhi)%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Lemma hull_bounds : forall B n, 0 <= B -> 1 <= n <= 64 -> B + n <= 0x800000000000 ->
  0 <= 8 * ((SH_OFF + B / 8) / 8) /\ 8 * ((SH_OFF + B / 8) / 8) + 8 < two64.
Proof.
  intros B n HB Hn HBn. assert (0 <= B / 8 <= B) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof (Z.mul_div_le (SH_OFF + B / 8) 8 ltac:(lia)). assert (0 <= (SH_OFF + B / 8) / 8) by (apply Z.div_pos; unfold SH_OFF; lia).
  unfold SH_OFF, two64 in *. lia.
Qed.
Lemma hull_bounds2 : forall B n, 0 <= B -> 1 <= n <= 64 -> B + n <= 0x800000000000 ->
  0 <= 8 * ((SH_OFF + (B + n - 1) / 8) / 8) /\ 8 * ((SH_OFF + (B + n - 1) / 8) / 8) + 8 < two64.
Proof. intros B n HB Hn HBn. exact (hull_bounds (B + n - 1) 1 ltac:(lia) ltac:(lia) ltac:(lia)). Qed.
Lemma sh8 : forall g, 0 <= g -> 8 * ((SH_OFF + g) / 8) = SH_OFF + 8 * (g / 8).
Proof. intros g Hg. replace (SH_OFF + g) with (g + 268431360 * 8) by (unfold SH_OFF; lia). rewrite Z.div_add by lia. unfold SH_OFF. lia. Qed.
Lemma div64 : forall x, 0 <= x -> x / 8 / 8 = x / 64.
Proof. intros x Hx. rewrite Z.div_div by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hull_pt : forall B n x, 0 <= B -> 1 <= n ->
  (8 * ((SH_OFF + B / 8) / 8) <= x < 8 * ((SH_OFF + B / 8) / 8) + 8 \/
   8 * ((SH_OFF + (B + n - 1) / 8) / 8) <= x < 8 * ((SH_OFF + (B + n - 1) / 8) / 8) + 8) ->
  SH_OFF + 8 * (B / 64) <= x < SH_OFF + 8 * ((B + n - 1) / 64) + 8.
Proof.
  intros B n x HB Hn Hx. rewrite !sh8 in Hx by (apply Z.div_pos; lia). rewrite !div64 in Hx by lia.
  assert (B / 64 <= (B + n - 1) / 64) by (apply Z.div_le_mono; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma hull_off : forall Base D n dlo dhi nhi, 0 <= Base -> Base mod 64 = 0 -> dlo <= D <= dhi -> 0 <= dlo -> 1 <= n <= nhi ->
  SH_OFF + Base / 8 + 8 * (dlo / 64) <= SH_OFF + 8 * ((Base + D) / 64) /\
  SH_OFF + 8 * ((Base + D + n - 1) / 64) + 8 <= SH_OFF + Base / 8 + 8 * (dlo / 64) + 8 * ((dhi + nhi - 1) / 64 - dlo / 64 + 1).
Proof.
  intros Base D n dlo dhi nhi HB Hal HD Hdlo Hn.
  pose proof (Z.div_mod Base 64 ltac:(lia)) as Hdm. rewrite Hal, Z.add_0_r in Hdm. set (G := Base / 64) in *.
  assert (E8 : Base / 8 = 8 * G) by (rewrite Hdm; replace (64 * G) with (0 + (8 * G) * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  assert (E1 : (Base + D) / 64 = G + D / 64) by (rewrite Hdm; replace (64 * G + D) with (D + G * 64) by lia; rewrite Z.div_add by lia; lia).
  assert (E2 : (Base + D + n - 1) / 64 = G + (D + n - 1) / 64) by (rewrite Hdm; replace (64 * G + D + n - 1) with ((D + n - 1) + G * 64) by lia; rewrite Z.div_add by lia; lia).
  assert (dlo / 64 <= D / 64) by (apply Z.div_le_mono; lia).
  assert ((D + n - 1) / 64 <= (dhi + nhi - 1) / 64) by (apply Z.div_le_mono; lia).
  rewrite E8, E1, E2. lia.
Qed.
Lemma tsum_al64 : forall E t, forallb (fun p => Z.eqb (snd p mod 64) 0) t = true -> tsum E t mod 64 = 0.
Proof.
  intros E t. induction t as [|[x c] t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. cbn [tsum]. rewrite Z.add_mod by lia. rewrite (IH H2), Z.add_0_r. rewrite Z.mul_mod by lia. cbn [snd] in H1. rewrite H1. reflexivity.
Qed.
Lemma lal64_sound : forall E b, lal64 b = true -> uE E b mod 64 = 0.
Proof.
  intros E b H. unfold lal64 in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H2.
  unfold uE, lden. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite <- (Zmod_div_mod 64 two64 (lz E b)) by (first [lia | exists 288230376151711744; reflexivity | unfold two64; lia]).
  unfold lz. rewrite Z.add_mod by lia. rewrite (tsum_al64 E _ H1), H2. reflexivity.
Qed.

(* [comment removed for export] *)
Section WordsR.
Variables (b : word) (n : Z).
Hypothesis Hb0 : 0 <= bv_unsigned b.
Hypothesis Hn : 1 <= n <= 64.
Hypothesis Hbn : bv_unsigned b + n <= 0x800000000000.
Let sh := Z_to_bv 64 SH_OFF.
#[using="n Hb0 Hn Hbn"] Lemma qrX_u : bv_unsigned (qX sh b) = SH_OFF + bv_unsigned b / 8.
Proof. LiaFast.lf_pins (fun (n Hb0 Hn Hbn : LiaFast.U) => LiaFast.u0).
  unfold qX, v_add, v_srli. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (H0 : 0 <= bv_unsigned b / 8 <= bv_unsigned b) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (u_small (bv_unsigned b / 8)) by (unfold two64 in *; lia).
  unfold sh. rewrite (u_small SH_OFF) by (unfold SH_OFF, two64; lia). apply u_small. unfold SH_OFF, two64 in *. lia.
Qed.
#[using="Hb0 Hn Hbn"] Lemma qrlast_u : bv_unsigned (qlast b n) = bv_unsigned b + n - 1.
Proof. LiaFast.lf_pins (fun (Hb0 Hn Hbn : LiaFast.U) => LiaFast.u0).
  unfold qlast, v_addi, v_add. rewrite (u_small n) by (unfold two64; lia).
  rewrite (u_small (bv_unsigned b + n)) by (unfold two64; lia). apply u_small. unfold two64 in *. lia.
Qed.
#[using="Hb0 Hn Hbn"] Lemma qrY_u : bv_unsigned (qY sh b n) = SH_OFF + (bv_unsigned b + n - 1) / 8.
Proof. LiaFast.lf_pins (fun (Hb0 Hn Hbn : LiaFast.U) => LiaFast.u0).
  unfold qY, v_add, v_srli. rewrite qrlast_u. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (H0 : 0 <= (bv_unsigned b + n - 1) / 8 <= bv_unsigned b + n - 1) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (u_small ((bv_unsigned b + n - 1) / 8)) by (unfold two64 in *; lia).
  unfold sh. rewrite (u_small SH_OFF) by (unfold SH_OFF, two64; lia). apply u_small. unfold SH_OFF, two64 in *. lia.
Qed.
End WordsR.
Lemma qrw1_u : forall (b : word), 0 <= bv_unsigned b -> bv_unsigned b + 1 <= 0x800000000000 ->
  bv_unsigned (qw1 (Z_to_bv 64 SH_OFF) b) = 8 * ((SH_OFF + bv_unsigned b / 8) / 8).
Proof.
  intros b Hb0 Hb1. unfold qw1, v_andi. rewrite (qrX_u b 1 Hb0 ltac:(lia) Hb1).
  assert (H0 : 0 <= bv_unsigned b / 8 <= bv_unsigned b) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite land_m8 by (unfold SH_OFF, two64 in *; lia).
  apply u_small. pose proof (hull_bounds (bv_unsigned b) 1 Hb0 ltac:(lia) Hb1). lia.
Qed.
Lemma qrw2_u' : forall (b : word) n, 0 <= bv_unsigned b -> 1 <= n <= 64 -> bv_unsigned b + n <= 0x800000000000 ->
  bv_unsigned (qw2 (Z_to_bv 64 SH_OFF) b n) = 8 * ((SH_OFF + (bv_unsigned b + n - 1) / 8) / 8).
Proof.
  intros b n Hb0 Hn Hbn. unfold qw2, v_andi. rewrite (qrY_u b n Hb0 Hn Hbn).
  assert (H0 : 0 <= (bv_unsigned b + n - 1) / 8 <= bv_unsigned b + n - 1) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite land_m8 by (unfold SH_OFF, two64 in *; lia).
  apply u_small. pose proof (hull_bounds2 (bv_unsigned b) n Hb0 Hn Hbn). lia.
Qed.

(* [comment removed for export] *)
Lemma zero_ov_in_r : forall E fs a n R, Forall (fact_ok E) fs -> zero_ov fs a n R = true -> 0 <= n ->
  uE E (rg_base R) + rsz E R <= two64 ->
  forall w, uE E a <= w < uE E a + n -> uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R.
Proof.
  intros E fs a n R HF H Hn HRw w Hin. unfold zero_ov in H. destruct (rg_kind R); try discriminate.
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Hr. destruct (irange fs (lsub a (rg_base R))) as [lo hi] eqn:Hir.
  cbn [fst snd] in Hr. apply andb_prop in H as [H Hz]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (size_lo_sound E fs R HF) as Hsz. fold (uE E (lsub a (rg_base R))) in Hr.
  pose proof (uE_range E a). pose proof (uE_range E (rg_base R)).
  destruct (small_diff E a (rg_base R) lo hi Hr) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
Qed.

(* [comment removed for export] *)
Lemma qcr_zero_spec : forall E fs rgs b nhi n, Forall (fact_ok E) fs -> qcr_zero fs rgs b nhi = true -> 1 <= n <= nhi -> nhi <= 64 ->
  uE E b + n <= 0x800000000000 ->
  exists sf k R, In R rgs /\ zero_ov fs sf k R = true /\ 0 <= k /\
    uE E sf <= SH_OFF + 8 * (uE E b / 64) /\ SH_OFF + 8 * ((uE E b + n - 1) / 64) + 8 <= uE E sf + k.
Proof.
  intros E fs rgs b nhi n HF Hz Hn Hnhi Hbn. pose proof (uE_range E b) as RB. unfold qcr_zero in Hz.
  destruct (is_const b) as [c|] eqn:Hbc.
  - cbv zeta in Hz. apply existsb_exists in Hz as (R & HRin & HzR). destruct (is_const_sound E b c Hbc) as [Hbv Hc64].
    assert (HBc : uE E b = c) by (unfold uE; rewrite Hbv; apply u_small; exact Hc64).
    exists (lconst (8 * ((SH_OFF + c / 8) / 8))), (8 * ((SH_OFF + (c + nhi - 1) / 8) / 8) + 8 - 8 * ((SH_OFF + c / 8) / 8)), R.
    split; [exact HRin|]. split; [exact HzR|].
    pose proof (hull_bounds c 1 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hl0 Hl1].
    assert (Hsfv : uE E (lconst (8 * ((SH_OFF + c / 8) / 8))) = 8 * ((SH_OFF + c / 8) / 8)) by (unfold uE; rewrite lden_lconst; apply u_small; lia).
    rewrite Hsfv, HBc. rewrite !sh8 by (apply Z.div_pos; lia). rewrite !div64 by lia.
    assert (c / 64 <= (c + n - 1) / 64) by (apply Z.div_le_mono; lia).
    assert ((c + n - 1) / 64 <= (c + nhi - 1) / 64) by (apply Z.div_le_mono; lia). lia.
  - apply existsb_exists in Hz as (R0 & HR0in & Hz1). unfold qcr_z1 in Hz1. set (base := rg_base R0) in *.
    destruct (lal64 base) eqn:Hal; [|discriminate].
    destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr.
    destruct (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool eqn:Hck; [|discriminate].
    apply andb_prop in Hck as [Hck H3]. apply andb_prop in Hck as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2, H3.
    destruct (srl_lin fs 3 base) as [q|] eqn:Hq; [|discriminate].
    apply existsb_exists in Hz1 as (R & HRin & HzR).
    pose proof (srl_lin_sound E fs 3 base q HF ltac:(lia) Hq) as Hqv. rewrite Z.shiftr_div_pow2 in Hqv by lia. change (2 ^ 3) with 8 in Hqv.
    fold (uE E q) (uE E base) in Hqv.
    pose proof (lal64_sound E base Hal) as Hm.
    pose proof (irange_sound E fs base HF) as Rb0. cbn [fst snd] in Rb0. fold (uE E base) in Rb0.
    pose proof (irange_sound E fs (lsub b base) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base)) in Rd.
    pose proof (uE_range E base) as RB0. pose proof (uE_range E q) as RQ.
    destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]]; [|exfalso; unfold two64 in *; lia].
    set (D := uE E (lsub b base)) in *.
    assert (HB : uE E b = uE E base + D) by lia.
    exists (laddc q (SH_OFF + 8 * (dlo / 64))), (8 * ((dhi + nhi - 1) / 64 - dlo / 64 + 1)), R. split; [exact HRin|]. split; [exact HzR|].
    assert (Hd64 : 0 <= dlo / 64 < 2 ^ 40) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hdd : dlo / 64 <= (dhi + nhi - 1) / 64) by (apply Z.div_le_mono; lia).
    assert (Hqb : uE E q < 2 ^ 61) by (rewrite Hqv; apply Z.div_lt_upper_bound; unfold two64 in *; lia).
    assert (Hsfv : uE E (laddc q (SH_OFF + 8 * (dlo / 64))) = uE E q + (SH_OFF + 8 * (dlo / 64))).
    { unfold uE at 1. rewrite lden_laddc. fold (uE E q). apply u_small. unfold SH_OFF, two64 in *. lia. }
    rewrite Hsfv, Hqv, HB. split; [lia|].
    destruct (hull_off (uE E base) D n dlo dhi nhi (proj1 RB0) Hm ltac:(lia) H1 Hn) as [G1 G2]. lia.
Qed.

(* [comment removed for export] *)
Section NodeR.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Himg : img_ok segs img.

#[using="Hwx Himg"] Theorem den_qcr : forall q S M E ms model T,
  qsite_ok segs q -> qcr_chk img q S M = true -> DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (qc_post q S) M ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros q S M E ms model T Hq Hck Hd Hk.
  destruct q as [pc0 rP rA rB rY rZ rW ord bim beq].
  pose proof Hq as Hq0. cbn [qsite_ok] in Hq0.
  destruct Hq0 as (Hnz & Hd1 & Hd2 & I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
  unfold qcr_chk in Hck. cbn [qs_rB qs_rA qs_rP qs_pc0] in Hck.
  set (fs := s_facts S) in *. set (b := rget (s_regs S) (rkey rB)) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (is_const (rget (s_regs S) (rkey rP))) as [P|] eqn:HP; [|discriminate].
  destruct (irange fs (lsub (rget (s_regs S) (rkey rA)) b)) as [nlo nhi] eqn:Hnr.
  destruct (load_at img fs (s_rgs S) (lconst P) SZ8 false) as [[sl|]|] eqn:HlP;
    [|rewrite ?andb_false_r, ?andb_false_l in Hck; discriminate | rewrite ?andb_false_r, ?andb_false_l in Hck; discriminate].
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0.
  match goal with Hx : qcr_zero _ _ _ _ = true |- _ => rename Hx into Hzc end.
  match goal with Hx : lwf (s_next S) b = true |- _ => rename Hx into Hwb end.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  subst sl.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (bw := lden E b).
  assert (HB : getr (ms_regs ms) rB = bw) by exact (HR rB).
  set (n := bv_unsigned (lden E (lsub (rget (s_regs S) (rkey rA)) b))).
  assert (HnE : lden E (lsub (rget (s_regs S) (rkey rA)) b) = Z_to_bv 64 n) by (unfold n; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hn64 : 0 <= n < two64) by (unfold n; apply uE_range).
  pose proof (irange_sound E fs (lsub (rget (s_regs S) (rkey rA)) b) HF) as Rn. rewrite Hnr in Rn. cbn [fst snd] in Rn. fold n in Rn.
  assert (HA : getr (ms_regs ms) rA = v_add bw (Z_to_bv 64 n)) by (rewrite (HR rA); exact (lsub_const_add E _ b n HnE)).
  assert (HPr : getr (ms_regs ms) rP = Z_to_bv 64 P) by (rewrite (HR rP); exact (proj1 (is_const_sound E _ P HP))).
  (* [comment removed for export] *)
  assert (Hb2 : bv_unsigned bw + n <= 0x800000000000).
  { pose proof (irange_sound E fs (rget (s_regs S) (rkey rA)) HF) as RA.
    pose proof (irange_sound E fs b HF) as RBb. fold bw in RBb.
    assert (HvA : bv_unsigned (lden E (rget (s_regs S) (rkey rA))) = bv_unsigned bw + n).
    { rewrite <- (HR rA), HA. unfold v_add. rewrite u_small; [rewrite (u_small n) by (unfold two64 in *; lia); reflexivity|].
      rewrite (u_small n) by (unfold two64 in *; lia). pose proof (bv_unsigned_in_range _ bw) as Rbw. unfold bv_modulus in Rbw.
      change (2 ^ Z.of_N 64) with two64 in Rbw. unfold two64 in *. lia. }
    rewrite HvA in RA. lia. }
  assert (Hbw0 : 0 <= bv_unsigned bw) by (pose proof (bv_unsigned_in_range _ bw) as X; lia).
  assert (Hn1 : 1 <= n <= 64) by lia.
  (* [comment removed for export] *)
  destruct (load_at_sound segs E img fs (s_rgs S) _ SZ8 false _ (ms_mem (restrict H ms)) Himg HG HF HlP) as (bsP & HrP & HvP).
  specialize (HvP _ eq_refl). rewrite ov_rdn in HrP. cbn [nbytes] in HrP.
  assert (HlbP : length bsP = 8%nat) by exact (rdn_length _ _ _ _ _ HrP).
  set (Pw := Z_to_bv 64 P).
  set (sh := Z_to_bv 64 SH_OFF).
  assert (HPv : bytes_le_to_Z bsP = bv_unsigned sh) by (apply ld8_val; [exact HlbP | rewrite <- HvP, lden_lconst; reflexivity]).
  rewrite lden_lconst in HrP. fold Pw in HrP.
  (* [comment removed for export] *)
  assert (Hzero : forall w, (w = qw1 sh bw \/ w = qw2 sh bw n) -> forall i, 0 <= i < 8 ->
            rd1 segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (bv_unsigned w + i)) = Some (Z_to_bv 8 0)).
  { intros w Hw i Hi. set (x := bv_unsigned w + i).
    assert (Hhull : SH_OFF + 8 * (bv_unsigned bw / 64) <= x < SH_OFF + 8 * ((bv_unsigned bw + n - 1) / 64) + 8).
    { apply (hull_pt (bv_unsigned bw) n x Hbw0 (proj1 Hn1)).
      unfold x, sh in *. destruct Hw as [-> | ->]; [left; rewrite (qrw1_u bw Hbw0 ltac:(lia)) | right; rewrite (qrw2_u' bw n Hbw0 Hn1 Hb2)]; lia. }
    destruct (qcr_zero_spec E fs (s_rgs S) b nhi n HF Hzc ltac:(lia) ltac:(lia) Hb2) as (sf & k & R & HRin & HzR & Hk0 & Hsf & Hkk).
    change (uE E b) with (bv_unsigned bw) in Hsf, Hkk.
    pose proof (proj1 (Forall_forall _ _) HG R HRin) as HRok. destruct HRok as (Hrs & Hrw & Hpts & Hcont).
    assert (Hin : uE E sf <= x < uE E sf + k) by lia.
    pose proof (zero_ov_in_r E fs _ _ R HF HzR Hk0 Hrw _ Hin) as HwR.
    destruct (zero_ov_sound E fs _ _ R HF HzR Hk0 Hrw _ HwR Hin) as (HkR & [Ht|Ht]).
    + specialize (Hpts (x - uE E (rg_base R)) ltac:(lia)). rewrite HkR in Hpts. destruct Hpts as (_ & Hz).
      specialize (Hz Ht). unfold uE in Hz. replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in Hz by lia.
      exact Hz.
    + destruct (Hcont _ _ Ht) as (_ & Hv). rewrite okey_pos in Hv by lia. cbn [bden] in Hv.
      unfold uE in Hv. replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in Hv by lia.
      exact Hv. }
  (* [comment removed for export] *)
  assert (HZ1 : rdn segs (mrestrict H (ms_mem ms)) (qw1 sh bw) 8 = Some zeros8)
    by (apply rdn_zeros8; [unfold sh; rewrite (qrw1_u bw Hbw0 ltac:(lia)); exact (proj2 (hull_bounds (bv_unsigned bw) n Hbw0 Hn1 Hb2)) | exact (Hzero _ (or_introl eq_refl))]).
  assert (HZ2 : rdn segs (mrestrict H (ms_mem ms)) (qw2 sh bw n) 8 = Some zeros8)
    by (apply rdn_zeros8; [unfold sh; rewrite (qrw2_u' bw n Hbw0 Hn1 Hb2); exact (proj2 (hull_bounds2 (bv_unsigned bw) n Hbw0 Hn1 Hb2)) | exact (Hzero _ (or_intror eq_refl))]).
  destruct (@qc2_isteps (mkFP (ms_fregs ms) (ms_fcsr ms)) segs pc0 rP rA rB rY rZ rW ord bim beq Hnz Hd1 Hd2
              I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11
              (ms_regs ms) (mrestrict H (ms_mem ms)) (ms_rom ms) bw n Pw sh bsP HB HPr HA HrP HPv HZ1 HZ2)
    as (regs' & Hst & Rp & Ry & Ra & Rz & Rw & Rothers).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pc0 0) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. cbn [qs_pc0] in Hpc. subst pcv.
    unfold restrict, mkst, qpc. cbn [ms_regs ms_fregs ms_fcsr ms_mem ms_rom fp_regs fp_csr ms_pc_val ms_svc_pending ms_resv].
    replace (pc0 + 4 * 0) with pc0 by lia. reflexivity. }
  (* [comment removed for export] *)
  set (x1 := s_next S). set (x2 := Pos.succ (s_next S)).
  set (E1 := upd (upd E x1 (qX sh bw)) x2 (qY sh bw n)).
  assert (Ha1 : agree (s_next S) E E1).
  { intros y Hy. unfold E1, upd. destruct (Pos.eqb_spec y x2); [unfold x2 in *; lia|]. destruct (Pos.eqb_spec y x1); [unfold x1 in *; lia|]. reflexivity. }
  assert (HE1a : E1 x1 = qX sh bw) by (unfold E1, upd; destruct (Pos.eqb_spec x1 x2); [unfold x1, x2 in *; lia|]; rewrite Pos.eqb_refl; reflexivity).
  assert (HE1b : E1 x2 = qY sh bw n) by (unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  set (S1 := bump S (Pos.succ x2)).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump, x2; cbn [s_next]; lia).
  assert (Hx1 : (x1 < s_next S1)%positive) by (unfold S1, bump, x1, x2; cbn [s_next]; lia).
  assert (Hx2 : (x2 < s_next S1)%positive) by (unfold S1, bump, x2; cbn [s_next]; lia).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model) by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | unfold x2; lia]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (qq := QS pc0 rP rA rB rY rZ rW ord bim beq).
  assert (Hpost : sden segs E1 (qc_post qq S) (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (qok2 pc0 bim beq) (mrestrict H (ms_mem ms)) (ms_rom ms))).
  { destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdS1)) as (_ & _ & _ & _ & _ & _ & _ & _).
    pose proof (sden_regs segs E1 S1 (restrict H ms) (s_regs (qc_post qq S)) regs' (qs_ok qq) ltac:(rewrite <- HH1; exact (dn_sden _ _ _ _ _ _ _ _ _ HdS1))) as X.
    assert (Hqk : Z_to_bv 64 (qs_ok qq) = qok2 pc0 bim beq) by (unfold qs_ok; cbn [qs_pc0 qs_bim qs_beq]; apply Z_to_bv_bv_unsigned).
    rewrite Hqk in X. cbn [restrict ms_fregs ms_fcsr ms_resv ms_mem ms_rom] in X. rewrite Hrsv in X.
    unfold qc_post at 1. cbn [qs_ok]. fold qq. unfold mkst. cbn [fp_regs fp_csr]. apply X.
    intros E' Ha' HR'.
    assert (HbE' : lden E' b = bw) by (unfold bw; apply (lden_agree_wf (s_next S) E E' b Hwb); exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' Hnx Ha'))).
    assert (HE'1 : E' x1 = qX sh bw) by (rewrite <- HE1a; symmetry; apply Ha'; exact Hx1).
    assert (HE'2 : E' x2 = qY sh bw n) by (rewrite <- HE1b; symmetry; apply Ha'; exact Hx2).
    destruct Hnz as (NP & NA & NY & NZ & NW).
    destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
    set (r5 := regupd (regupd (regupd (regupd (regupd (ms_regs ms) rP (qX sh bw)) rY (qY sh bw n)) rA (qlast bw n)) rZ (Z_to_bv 64 0)) rW (Z_to_bv 64 0)).
    assert (HR5 : regs_ok E' (s_regs (qc_post qq S)) r5).
    { unfold qc_post, qq. cbn [s_regs qs_rB qs_rP qs_rY qs_rA qs_rZ qs_rW]. fold b.
      unfold r5.
      assert (R0 : forall E0 R regs (rd : reg) l v, rd <> 0%bv -> regs_ok E0 R regs -> lden E0 l = v ->
                     regs_ok E0 (rset R (rkey rd) l) (regupd regs rd v)).
      { intros E0 R regs rd l v Hne HR0 Hv. pose proof (regs_ok_upd E0 R regs rd l v HR0 Hv) as X0.
        rewrite (PropExec.bv_eqb_neq rd 0%bv Hne) in X0. exact X0. }
      apply R0; [exact NW| |]; [apply R0; [exact NZ| |]; [apply R0; [exact NA| |]; [apply R0; [exact NY| |]; [apply R0; [exact NP| |]|]|]|]|].
      - exact HR'.
      - rewrite lden_lvar. exact HE'1.
      - rewrite lden_lvar. exact HE'2.
      - assert (HRA : lden E' (rget (s_regs S) (rkey rA)) = v_add bw (Z_to_bv 64 n)) by (rewrite <- HA; symmetry; exact (HR' rA)).
        rewrite lden_laddc, HRA. unfold qlast, v_addi. reflexivity.
      - rewrite lden_lconst. reflexivity.
      - rewrite lden_lconst. reflexivity. }
    intros r. rewrite <- (HR5 r). unfold r5.
    destruct (decide (r = rW)) as [->|NrW]; [rewrite getr_same by exact NW; exact Rw|]. rewrite getr_other by exact NrW.
    destruct (decide (r = rZ)) as [->|NrZ]; [rewrite getr_same by exact NZ; exact Rz|]. rewrite getr_other by exact NrZ.
    destruct (decide (r = rA)) as [->|NrA]; [rewrite getr_same by exact NA; exact Ra|]. rewrite getr_other by exact NrA.
    destruct (decide (r = rY)) as [->|NrY]; [rewrite getr_same by exact NY; exact Ry|]. rewrite getr_other by exact NrY.
    destruct (decide (r = rP)) as [->|NrP]; [rewrite getr_same by exact NP; exact Rp|]. rewrite getr_other by exact NrP.
    exact (Rothers r NrP NrA NrY NrZ NrW). }
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (qc_post qq S)
           (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (qok2 pc0 bim beq) (mrestrict H (ms_mem ms)) (ms_rom ms)) E1 HdS1).
  - rewrite HH1, Hmsr. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - unfold qc_post, S1, bump, x2. cbn [s_next]. apply Pos.le_refl.
  - intros y _. rewrite HH1. reflexivity.
  - reflexivity.
  - intros E2 ms2 model2 HD2 Ha2. apply (Hk E2 ms2 model2); [|exact HD2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.

End NodeR.
