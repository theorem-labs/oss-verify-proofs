(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChain FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys.

Module FxDropOwn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChSep FxChAdd FxChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Drop.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_drop_own : forall E S M ms model (f : region -> bool),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall p, In p (sm_own M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
     w < two64 /\ forall R, In R (s_rgs S) -> f R = true -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  (forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     in_zr (sm_zr M) w = true -> ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0)) ->
  DEN segs LIMIT model0 mem0 E (drop_post S f) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hno Hf.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  - intros E'' Ha''. cbn [drop_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0, drop_post. cbn [s_pc s_regs s_rgs s_facts s_resv]. repeat split; try assumption.
    + apply Forall_forall. intros R HR. apply filter_In in HR as [HR _]. rewrite Forall_forall in H5. exact (H5 R HR).
    + exact (rgs_disj_filter E'' _ _ H6).
  - unfold bases_wf in *. cbn [drop_post s_rgs s_next]. rewrite forallb_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hbw R HR).
  - intros w Hw Hout Hnow Hnb. cbn [drop_post s_rgs] in Hout.
    destruct (Z_lt_le_dec w 0) as [Hneg|Hnn].
    + pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO in Hs. apply andb_prop in Hs as [Hs _]. apply Z.leb_le in Hs. lia.
    + (* [comment removed for export] *)
      destruct (existsb (fun R => f R && (Z.leb (uE E (rg_base R)) w && Z.ltb w (uE E (rg_base R) + rsz E R)))%bool (s_rgs S)) eqn:He.
      * apply existsb_exists in He as (R & HR & Hc). apply andb_prop in Hc as [HfR Hc]. apply andb_prop in Hc as [C1 C2].
        apply Z.leb_le in C1. apply Z.ltb_lt in C2. exact (Hf R HR HfR w ltac:(lia) Hw).
      * apply (Hzr w Hw); [|exact Hnow|exact Hnb]. unfold outside in *. apply Forall_forall. intros R HR. rewrite Forall_forall in Hout.
        destruct (f R) eqn:HfR.
        -- assert (Hc : (f R && (Z.leb (uE E (rg_base R)) w && Z.ltb w (uE E (rg_base R) + rsz E R)))%bool = false)
             by (apply not_true_iff_false; intros Hc'; rewrite (proj2 (existsb_exists _ _) (ex_intro _ R (conj HR Hc'))) in He; discriminate).
           rewrite HfR in Hc. cbn [andb] in Hc. pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_HI in Hs.
           apply andb_prop in Hs as [_ Hs]. apply Z.ltb_lt in Hs. rewrite fg64 by (unfold two64; lia).
           apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc; left; unfold uE in Hc; exact Hc | apply Z.ltb_ge in Hc; right; unfold uE in Hc; exact Hc].
        -- apply Hout. apply filter_In. split; [exact HR | rewrite HfR; reflexivity].
  - rewrite Forall_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hrl R HR).
  - apply (frz_keep mem0 E E S (drop_post S f) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho. unfold outside in *. cbn [drop_post s_rgs]. apply Forall_forall. intros R HR. apply filter_In in HR as [HR _].
      rewrite Forall_forall in Ho. exact (Ho R HR).
    + intros w _ _. reflexivity.
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho. apply Hm.
    destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG & _ & _ & _).
    destruct (Hno p Hp w Hw) as [Hw64 X].
    pose proof (uE_range E (fst p)) as R1.
    unfold outside in *. rewrite Forall_forall in *. intros R HR.
    destruct (f R) eqn:HfR.
    + destruct (HG R HR) as (Hrs & Hrw & _). specialize (X R HR HfR).
      destruct (Z_lt_le_dec w (uE E (rg_base R))) as [Y|Y].
      * left. rewrite fg64' by (unfold two64 in *; lia). unfold uE in Y. exact Y.
      * destruct (Z_lt_le_dec w (uE E (rg_base R) + rsz E R)) as [Y2|Y2]; [exfalso; apply X; split; assumption|].
        right. rewrite fg64' by (unfold two64 in *; lia). unfold uE in Y2. exact Y2.
    + apply Ho. apply filter_In. split; [exact HR | rewrite HfR; reflexivity].
Qed.

(* [comment removed for export] *)
Definition own_below (fs : list fact) (M : smodel) (p : lin * lin) : bool :=
  match is_const (fst p), is_const (snd p) with
  | Some b, Some n => (Z.leb 0 n && Z.leb (b + n) 0x7fff7f800000)%bool
  | _, Some n => existsb (fun g => (lin_eqb (fst (fst g)) (fst p) && Z.leb 0 n && Z.leb n (gsz_lo fs g))%bool) (sm_maps M)
  | _, None => false
  end.
Definition above_sp (fs : list fact) (M : smodel) (R : region) : bool :=
  let '(lo, hi) := irange fs (lsub (rg_base R) (sm_sp M)) in (Z.leb 0 lo && Z.leb hi (2 ^ 40))%bool.
Definition drop_own_ok (S : sst) (M : smodel) (f : region -> bool) : bool :=
  (forallb (own_below (s_facts S) M) (sm_own M) && forallb (fun R => negb (f R) || above_sp (s_facts S) M R) (s_rgs S))%bool.

#[using="Type"] Theorem drop_own_sound : forall E S M ms model f, DEN segs LIMIT model0 mem0 E S M ms model -> drop_own_ok S M f = true ->
  forall p, In p (sm_own M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
     w < two64 /\ forall R, In R (s_rgs S) -> f R = true -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hok p Hp w Hw. unfold drop_own_ok in Hok. apply andb_prop in Hok as [Ho Hr].
  rewrite forallb_forall in Ho, Hr.
  pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hspo Hsph]. pose proof (alloc_top_lo _ Hspo) as Hatl.
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as HspE.
  assert (Hat : alloc_top (m_vmmaps model) = uE E (sm_sp M) - 8388608) by (unfold alloc_top, stack_max_size, uE; rewrite HspE; reflexivity).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  (* [comment removed for export] *)
  assert (Hlow : w < alloc_top (m_vmmaps model)).
  { pose proof (Ho p Hp) as Hb. unfold own_below in Hb.
    destruct (is_const (fst p)) as [b|] eqn:Hcb; destruct (is_const (snd p)) as [n|] eqn:Hcn; try discriminate.
    - apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
      destruct (is_const_sound E _ b Hcb) as [Vb Rb]. destruct (is_const_sound E _ n Hcn) as [Vn Rn].
      unfold uE in Hw. rewrite Vb, Vn, !fg64' in Hw by assumption. lia.
    - apply existsb_exists in Hb as (g & Hg & Hc). apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2].
      apply lin_eqb_eq in Hc. apply Z.leb_le in H2, H3.
      destruct (is_const_sound E _ n Hcn) as [Vn Rn].
      pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgt. rewrite Forall_forall in Hgt. specialize (Hgt g Hg). rewrite Hc in Hgt.
      pose proof (gsz_bounds E (s_facts S) g HF) as Gb.
      unfold uE in Hw. rewrite Vn, fg64' in Hw by assumption. unfold uE in Hgt. lia. }
  pose proof (uE_range E (sm_sp M)) as Rsp. split; [unfold two64 in *; lia|].
  intros R HR HfR Hin. specialize (Hr R HR). rewrite HfR in Hr. cbn [negb orb] in Hr. unfold above_sp in Hr.
  destruct (irange (s_facts S) (lsub (rg_base R) (sm_sp M))) as [lo hi] eqn:Hir.
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (irange_sound E (s_facts S) (lsub (rg_base R) (sm_sp M)) HF) as Rd. rewrite Hir in Rd. cbn [fst snd] in Rd.
  fold (uE E (lsub (rg_base R) (sm_sp M))) in Rd.
  pose proof (uE_range E (rg_base R)). pose proof (uE_range E (sm_sp M)).
  unfold sp_window_hi in Hsph. rewrite HspE in Hsph. fold (uE E (sm_sp M)) in Hsph.
  destruct (small_diff E (rg_base R) (sm_sp M) lo hi Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
Qed.
End Drop.
(* [comment removed for export] *)
End FxDropOwn.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Instance chw_fx : FPState := fx0.

(* [comment removed for export] *)
Lemma byte_bits_high : forall (b : byte) i, 8 <= i -> Z.testbit (bv_unsigned b) i = false.
Proof.
  intros b i Hi. pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|c r IH]; cbn [bytes_le_to_Z]; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; lia].
Qed.

Lemma Z_to_le_bytes_roundtrip : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b r IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_nonneg r) as Hr0.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec_low by lia. apply orb_false_r.
    + rewrite Z.mod_pow2_bits_high by lia. symmetry. apply byte_bits_high. exact Hi8.
  - replace (Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z r) 8)) 8) with (bytes_le_to_Z r); [exact IH|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    replace (i + 8 - 8) with i by lia. rewrite byte_bits_high by lia. reflexivity.
Qed.

Lemma word_le8_roundtrip : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ (8 * Z.of_nat 8)).
  pose proof (Z_to_le_bytes_roundtrip bs) as R. rewrite Hl in R.
  assert (Hm : bytes_le_to_Z bs mod 2 ^ (8 * Z.of_nat 8) = bytes_le_to_Z bs).
  { rewrite <- (bytes_le_to_Z_of_le_bytes 8 (bytes_le_to_Z bs) (bytes_le_to_Z_nonneg bs)). rewrite R. reflexivity. }
  rewrite Hm. exact R.
Qed.

(* [comment removed for export] *)
Lemma sys_input_pend : forall segs ms x8, ms_rom ms = seg_rom segs ->
  sys_input segs (svc_set ms) x8 = sys_input segs (epend (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (seg_rom segs) x8) x8.
Proof. intros segs ms x8 H. unfold sys_input, ms_read_byte, ms_writable_byte. cbn [svc_set epend ms_mem ms_rom]. rewrite H. reflexivity. Qed.

Lemma ra_le : forall H a n n', (n' <= n)%nat -> range_avoids H a n -> range_avoids H a n'.
Proof. intros H a n n' Hle Hav k Hk. apply Hav. lia. Qed.

(* [comment removed for export] *)
Definition wv_post (L : sst) (len : lin) (n : Z) : sst :=
  post_fresh L (fun x => [FRange x 1 n; FRange (lsub len x) 0 n]).

Section Wv.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma den_ret_fresh : forall model0 E L M ms model (w : word) (fs : lin -> list fact) ci m'',
  DEN segs LIMIT model0 mem0 E L M ms model ->
  (forall E', agree (Pos.succ (s_next L)) (upd E (s_next L) w) E' -> Forall (fact_ok E') (fs (lvar (s_next L)))) ->
  MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
  DEN segs LIMIT model0 mem0 (upd E (s_next L) w) (post_fresh L fs) M
      (advance_past_svc (apply_effect (svc_set ms) (mkEffectU w [] [] [] [] ci))) m''.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model w fs ci m'' Hd Hf Hinv Hsb.
  set (E1 := upd E (s_next L) w).
  assert (Ha : agree (s_next L) E E1) by exact (agree_upd (s_next L) E w).
  pose proof (den_agree segs LIMIT model0 mem0 E E1 L M ms model Hd Ha) as Hd1.
  pose proof (den_bump segs LIMIT model0 mem0 E1 L M ms model (Pos.succ (s_next L)) Hd1 ltac:(lia)) as Hd2.
  assert (HA : AM model0 E1 M = AM model0 E M) by exact (AM_agree (s_next L) model0 E E1 M (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha).
  assert (Hwv : lwf (s_next (bump L (Pos.succ (s_next L)))) (lvar (s_next L)) = true).
  { cbn [bump s_next]. unfold lwf, lvar. cbn. rewrite andb_true_r. apply Pos.ltb_lt. lia. }
  pose proof (den_ret_ci0 segs LIMIT mem0 model0 E1 _ M ms model (lvar (s_next L)) ci m'' Hd2 Hwv ltac:(rewrite HA; exact Hinv) Hsb) as Hd3.
  assert (Hw : lden E1 (lvar (s_next L)) = w) by (rewrite lden_lvar; unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  rewrite Hw in Hd3.
  assert (Hpf : post_fresh L fs = SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (lvar (s_next L))) (s_rgs L)
                                       (fs (lvar (s_next L)) ++ s_facts L) (Pos.succ (s_next L)) (s_resv L)) by reflexivity.
  rewrite Hpf. clear Hpf.
  assert (Hgen : forall fl, (forall E', agree (Pos.succ (s_next L)) E1 E' -> Forall (fact_ok E') fl) ->
            DEN segs LIMIT model0 mem0 E1 (SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (lvar (s_next L))) (s_rgs L)
                                       (fl ++ s_facts L) (Pos.succ (s_next L)) (s_resv L)) M
                 (advance_past_svc (apply_effect (svc_set ms) (mkEffectU w [] [] [] [] ci))) m'').
  { induction fl as [|f fl IH]; intros Hfl.
    - exact Hd3.
    - apply (den_addfact segs LIMIT model0 mem0 E1 _ M _ m'' f (IH (fun E' Ha' => Forall_inv_tail (Hfl E' Ha')))).
      intros E' Ha'. exact (Forall_inv (Hfl E' Ha')). }
  exact (Hgen (fs (lvar (s_next L))) Hf).
Qed.

#[using="Type"] Lemma getr_gpr : forall ms k, (k <= 5)%nat -> getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat k)) = ms_gpr (svc_set ms) k.
Proof. LiaFast.lf_pins LiaFast.u0. intros ms k Hk. unfold getr, ms_gpr. cbn [svc_set ms_regs]. destruct k as [|[|[|[|[|[|k]]]]]]; try lia; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_writev : forall model0 E L M ms model (K : TSet) (ch : Z) (b len : lin) (bs : list byte) (n : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 66 -> arg L 0 = Some ch -> arg L 2 = Some 1 -> (ch = 1 \/ ch = 2) ->
  fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch)) ->
  rdn segs (ms_mem ms) (lden E (argl L 1)) 8 = Some (word_to_le_bytes 8 (lden E b)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 16 - 8)) 8 = Some (word_to_le_bytes 8 (lden E len)) ->
  rdn segs (ms_mem ms) (lden E b) (length bs) = Some bs ->
  bv_unsigned (lden E len) = Z.of_nat (length bs) -> (1 <= length bs)%nat -> Z.of_nat (length bs) <= n -> n <= 2 ^ 30 ->
  bv_unsigned (lden E (argl L 1)) + 16 <= TASK_SIZE -> bv_unsigned (lden E b) + Z.of_nat (length bs) <= TASK_SIZE ->
  range_avoids (Hof E M model) (lden E (argl L 1)) 16 -> range_avoids (Hof E M model) (lden E b) (length bs) ->
  lwf (s_next L) len = true -> K [] ->
  (forall E' ms' m'', DEN segs LIMIT model0 mem0 E' (wv_post L len n) M ms' m'' -> agree (s_next L) E E' ->
     1 <= bv_unsigned (E' (s_next L)) <= Z.of_nat (length bs) ->
     realizes_cfg segs cfg (mkCfg ms' m'') (t_emit (map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (bv_unsigned (E' (s_next L)))) bs)) K)) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) (t_emit (map (WriteEv (Z_to_bv 64 ch)) bs) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model K ch b len bs n Hd H7 H0 H2 Hch Hfd0 Hi0 Hi1 Hbuf Hlen Hnb Hn Hn30 Hiok Hbok Havi Havb Hwl HK0 Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (regs := ms_regs ms).
  set (x8 := ms_reg ms 17).
  assert (Hx8 : x8 = Z_to_bv 64 66) by exact (a7_const segs E L (restrict H ms) ms 66 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 ch) by exact (gpr_const segs E L (restrict H ms) ms 0 ch Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = lden E (argl L 1)) by exact (gpr_lin_k segs E L (restrict H ms) ms 1 Hsd eq_refl ltac:(lia)).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 1) by exact (gpr_const segs E L (restrict H ms) ms 2 1 Hsd eq_refl ltac:(lia) H2).
  assert (R10 : getr regs 10 = Z_to_bv 64 ch).
  { rewrite <- Hg0. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 0))); [reflexivity|]. exact (getr_gpr ms 0 ltac:(lia)). }
  assert (R11 : getr regs 11 = lden E (argl L 1)).
  { rewrite <- Hg1. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 1))); [reflexivity|]. exact (getr_gpr ms 1 ltac:(lia)). }
  assert (R12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length [(lden E b, lden E len)]))).
  { cbn [length]. change (Z.of_nat 1) with 1%Z. rewrite <- Hg2. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 2))); [reflexivity|]. exact (getr_gpr ms 2 ltac:(lia)). }
  assert (R17 : getr regs 17 = Z_to_bv 64 66) by exact Hx8.
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hch32 : fd32 (getr regs 10) = Z_to_bv 64 ch) by (rewrite R10; apply fd32_id; rewrite u_small64 by (unfold two64; lia); lia).
  assert (Hfd : fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel (Z_to_bv 64 ch))) by (rewrite Hch32, Hfm; exact Hfd0).
  assert (Hw0 : w_is0 (Z_to_bv 64 ch) = false) by (unfold w_is0, bv_eqb; destruct Hch as [->| ->]; reflexivity).
  set (iovs := [(lden E b, lden E len)]).
  set (bss := [bs]).
  assert (Harr : iov_array segs (ms_mem ms) (getr regs 11) iovs).
  { unfold iovs. cbn [iov_array]. rewrite R11. split; [exact Hi0|]. split.
    - replace (bv_unsigned (lden E (argl L 1)) + 8) with (bv_unsigned (lden E (argl L 1)) + 16 - 8) by lia. exact Hi1.
    - split; [rewrite Hlen; lia | exact I]. }
  assert (Hbo : iov_bufs_ok iovs) by (unfold iovs; cbn [iov_bufs_ok]; rewrite Hlen; split; [lia | exact I]).
  assert (Hbb : iov_bufs segs (ms_mem ms) iovs bss).
  { unfold iovs, bss. cbn [iov_bufs]. split; [|exact I]. unfold word_to_nat. rewrite Hlen, Nat2Z.id. exact Hbuf. }
  assert (Htot : iovs_total iovs = Z.of_nat (length bs)) by (unfold iovs; cbn; rewrite Hlen; lia).
  assert (Hcb : concat bss = bs) by (unfold bss; cbn; apply app_nil_r).
  assert (Hiok' : bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE) by (rewrite R11; unfold iovs; cbn [length]; lia).
  pose proof (writev_ch_ok_iff segs regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs bss) as Hspec.
  pose proof (writev_ch_no_unmodeled segs regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs bss R17 Hfd Hw0 R12
                ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Hbb ltac:(rewrite Htot; lia) ltac:(rewrite Htot; lia)) as Hnu.
  rewrite <- (sys_input_pend segs ms (getr regs 17) Hrom) in Hnu.
  assert (Hx8' : getr regs 17 = x8) by reflexivity. rewrite Hx8' in Hnu.
  set (CA := import_iovecs_accesses (mrb segs (ms_mem ms)) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs)))).
  set (EF := fun j : wr_index bs => ret_ci (Z_to_bv 64 (Z.of_nat (proj1_sig j))) (CA ++ (iov_prefix_accesses iovs (proj1_sig j) ++ []))).
  assert (Hspr : forall eff m' evs, syscall_spec (sys_input segs ms1 x8) model (Ok eff m' evs) <->
            exists j : wr_index bs, eff = EF j /\ m' = model /\ evs = map (WriteEv (Z_to_bv 64 ch)) (firstn (proj1_sig j) bs)).
  { intros eff m' evs. unfold ms1. rewrite (sys_input_pend segs ms x8 Hrom). fold regs. rewrite <- Hx8'.
    rewrite (Hspec eff m' evs R17 Hfd Hw0 R12 ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Hbb ltac:(rewrite Htot; lia) ltac:(rewrite Htot; lia)).
    rewrite Hcb. split.
    - intros (k & Hk' & -> & -> & ->). exists (exist _ k Hk'). unfold EF. cbn [proj1_sig]. auto.
    - intros ([k Hk'] & -> & -> & ->). exists k. unfold EF. cbn [proj1_sig]. auto. }
  assert (Hacc : forall j : wr_index bs, ranges_avoid H (syscall_effect_accesses (EF j))).
  { intros [k Hk']. unfold EF, ret_ci, syscall_effect_accesses. cbn [eff_copyins eff_writes proj1_sig]. rewrite !app_nil_r.
    apply ranges_avoid_app.
    - unfold CA, import_iovecs_accesses. unfold iovs. cbn [length]. change (Z.of_nat 1) with 1%Z. rewrite bv_eqb_refl.
      destruct (negb (access_okb (getr regs 11) 16)); [apply ranges_avoid_nil|].
      apply ranges_avoid_cons; [rewrite R11; exact Havi | apply ranges_avoid_nil].
    - unfold iovs. cbn [iov_prefix_accesses].
      destruct k as [|k]; [lia|].
      destruct (Nat.eqb (word_to_nat_bounded (lden E len) (Datatypes.S k)) 0) eqn:Ez; [apply ranges_avoid_nil|].
      apply ranges_avoid_cons; [|destruct (Datatypes.S k - word_to_nat_bounded (lden E len) (Datatypes.S k))%nat; apply ranges_avoid_nil].
      apply (ra_le H (lden E b) (length bs)); [|exact Havb].
      unfold word_to_nat_bounded. pose proof (word_to_nat_bounded_eq_min (lden E len) (Datatypes.S k)) as X.
      unfold word_to_nat_bounded in X. rewrite X. unfold word_to_nat. rewrite Hlen, Nat2Z.id. lia. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 (wr_index bs) EF (fun _ => model)
             (fun j => map (WriteEv (Z_to_bv 64 ch)) (firstn (proj1_sig j) bs))
             (fun j => t_emit (map (WriteEv (Z_to_bv 64 ch)) (skipn (proj1_sig j) bs)) K) (wr_full bs Hnb) (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros j. apply Hspr. exists j. auto.
    + intros eff m' evs Hs. apply Hspr in Hs as (j & -> & -> & ->). exists j. auto.
    + exact Hnu.
    + intros eff. apply not_spurious_uninjected. cbn [in_sysno sys_input]. rewrite Hx8. reflexivity.
    + intros _. exact Hh.
    + intros _. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact Hminv.
    + exact Hacc.
    + intros [k Hk'] m'' Hinv'' Hsb''. cbn [proj1_sig].
      set (w := Z_to_bv 64 (Z.of_nat k)).
      assert (Hwu : bv_unsigned w = Z.of_nat k) by (unfold w; apply u_small64; unfold two64; lia).
      pose proof (den_ret_fresh model0 E L M ms model w (fun x => [FRange x 1 n; FRange (lsub len x) 0 n])
                    (CA ++ (iov_prefix_accesses iovs k ++ [])) m'' Hd) as HD'.
      assert (HD2 : DEN segs LIMIT model0 mem0 (upd E (s_next L) w) (wv_post L len n) M
                  (advance_past_svc (apply_effect ms1 (EF (exist _ k Hk')))) m'').
      { apply HD'; [|exact Hinv'' | exact Hsb''].
        intros E' Ha'. assert (He : E' (s_next L) = w) by (rewrite <- (Ha' (s_next L) ltac:(lia)); unfold upd; rewrite Pos.eqb_refl; reflexivity).
        assert (Hle : lden E' len = lden E len).
        { rewrite (lden_agree_wf (s_next L) E E' len Hwl); [reflexivity|].
          intros x Hx. rewrite <- (Ha' x ltac:(lia)). unfold upd. destruct (Pos.eqb x (s_next L)) eqn:Ex; [apply Pos.eqb_eq in Ex; lia | reflexivity]. }
        constructor; [|constructor; [|constructor]].
        - cbn [fact_ok]. rewrite lden_lvar, He, Hwu. lia.
        - cbn [fact_ok]. rewrite lden_lsub, lden_lvar, He, Hle. rewrite bv_sub_unsigned, Hwu, Hlen. unfold bv_wrap.
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
      eapply rzc_conseq; [apply (Hk (upd E (s_next L) w) _ m'' HD2 (agree_upd _ E w))|].
      * unfold upd. rewrite Pos.eqb_refl. rewrite Hwu. lia.
      * unfold upd. rewrite Pos.eqb_refl. rewrite Hwu, Nat2Z.id. apply t_eq_refl.
  - apply (t_alt_wall (Z_to_bv 64 ch) bs K HK0 Hnb).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma rd1_restrict_vis : forall H full w b, H_off_segments segs H -> rd1 segs (mrestrict H full) w = Some b ->
  rd1 segs full w = Some b /\ H w = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros H full w b Hoff Hr. unfold rd1, mrestrict in *. destruct (H w) eqn:Hh.
  - exfalso. apply Hoff in Hh. rewrite (seg_rom_none segs w Hh) in Hr. discriminate.
  - split; [exact Hr | reflexivity].
Qed.

#[using="mem0"] Lemma rdn_restrict_vis : forall H full n a bs, H_off_segments segs H -> rdn segs (mrestrict H full) a n = Some bs ->
  rdn segs full a n = Some bs /\ range_avoids H a n.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros H full n. induction n as [|n IH]; intros a bs Hoff Hr.
  - split; [exact Hr | intros k Hk; lia].
  - cbn [rdn] in Hr |- *.
    destruct (match mrestrict H full a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Hb; [|discriminate].
    destruct (rdn segs (mrestrict H full) (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate].
    injection Hr as <-.
    assert (Hb' : rd1 segs (mrestrict H full) a = Some b) by exact Hb.
    destruct (rd1_restrict_vis H full a b Hoff Hb') as [Hf Hh]. unfold rd1 in Hf. rewrite Hf.
    destruct (IH (a + 1)%bv rest Hoff Hrest) as [Hf2 Hav]. rewrite Hf2. split; [reflexivity|].
    intros [|k] Hk; [rewrite woff_0; exact Hh|]. rewrite <- woff_succ. apply Hav. lia.
Qed.

#[using="Type"] Lemma ld1_byte : forall b : byte, ld_word SZ1 false [b] = Z_to_bv 64 (bv_unsigned b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b. unfold ld_word. rewrite le_word_1, b_extract8_id. unfold zext. apply bv_eq.
  rewrite bv_zero_extend_unsigned, Z_to_bv_unsigned; [|lia]. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

#[using="Type"] Lemma ld8_bytes : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (ld_word SZ8 false bs) = bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs Hl. unfold ld_word.
  assert (He : bv_extract 0 64 (le_bytes_to_word bs) = le_bytes_to_word bs).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite He. exact (word_le8_roundtrip bs Hl).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma t_emit_app : forall a b T, t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)]; [left; exact Hp | right; exists b'; split; [reflexivity | left; exact Hp]].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity | right; exists tr'; split; [reflexivity | exact HT]].
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. split; [rewrite app_assoc; reflexivity | exact HT].
Qed.

End Wv.
