(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YGcfInstDrainCn.v (commit ce1a656b52b7, file sha256 219dc0e75c1e) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the GRANT step of F11 — the drain's cut relation
   across EnsureFreeArraySpace's KMapFreeArray grant, at the intermediate memory the walk exposes at that call's
   return.  rule 24: no function proved (kind: relation-level facts about the walk's own frame).

   F11 = this step ; the no-growth step (YGcfInstDrainCm.cd_step_cf at the grown state, unchanged).  Here the state
   goes from X to YGcfInstDrainCg.cgX (class c's rg_mapped_fa grows by kFreeArrayMapSize and the new map's hole
   goes), the world gains the map and its shadow, the model re-protects the slot, and the memory is the walk's
   intermediate one: equal to the entry's off [cnwin], present on it, with the region record's cells carried by
   value, the new map all zero and its shadow the free-array poison.
   The grant leaves the map LIST untouched (`fixedin_ok_model 3` goes through mmap_fixed_rw_next, whose vm_maps /
   vm_reserved / vm_limit are the argument's), so the ledger's map side transports and only the free-array cut point
   and the eager bound move.  Image-free and event-free. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG03cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstDrainR YGcfInstDrainRL. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YGcfInstDrainCg YGcfInstDrainCl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* The closure now carries YGcfInstBase (through YGcfInstDrainX), which leaves lia's euclidean-division flag
   off; this file's proofs were written with it on. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Local Open Scope am_scope.

Lemma pairwise_nth_n : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Section N.
Variable B : asyms.
Variable ly : alayout.
Variable X : astate.
Variables (c sp0 : Z).
Variables (W W3 : world im_segs) (mem mem1 : word -> option byte) (md md2 : Model) (Hp : list Z).
Local Notation rd := (aview im_segs (w_H W) mem).
Local Notation rd1 := (aview im_segs (w_H W3) mem1).
Local Notation T := (ly_T ly).
Local Notation mf := (rg_mapped_fa (reg X c)).
Local Notation fadr := (fa_base ly c + rg_mapped_fa (reg X c)).
Local Notation shf := (shadow_addr (fa_base ly c + rg_mapped_fa (reg X c))).
Local Notation RG := (ly_space ly + kRegionInfoOff + 128 * c).

Hypothesis MR : ARcfR im_segs B ly X Hp W mem md.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hgrow : mf + kFreeArrayMapSize <= kFreeArrayMax.
Hypothesis Hsp : ly_stk_lo ly + 320 <= sp0 <= ly_stk_hi ly.

(* EnsureFreeArraySpace's frame at its return: H3's WING1 (DMcdR.v:137-191 @ ea2f3f773b0) — its stack scratch, the
   region's mapped-free-array word, the record's NON-cell junk bytes, the two thread-stats windows, the new map and
   its shadow.  Every other region cell is the entry's, by the frame. *)
Variable stklo : Z.
Hypothesis Hstk : ly_stk_lo ly <= stklo /\ stklo <= sp0 <= ly_stk_hi ly.
Definition cnwin (a : Z) : Prop :=
(stklo <= a < sp0) \/ (RG + 24 <= a < RG + 32) \/ (RG + 64 <= a < RG + 68) \/ (RG + 69 <= a < RG + 128) \/
(T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) \/
(fadr <= a < fadr + kUserMapSize) \/ (shf <= a < shf + 32768).
Definition okn (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ cnwin a.

Hypothesis MEQ1 : forall x : word, ~ cnwin (bv_unsigned x) -> mem1 x = mem x.
Hypothesis PRES1 : forall a, cnwin a -> apresent (w_H W3) mem1 a.
Hypothesis HWH : forall a : word, ~ (fadr <= bv_unsigned a < fadr + kUserMapSize) ->
  ~ (shf <= bv_unsigned a < shf + 32768) -> w_H W3 a = w_H W a.

Lemma cnM : ARmcfR B ly X Hp rd. Proof. exact (proj1 MR). Qed.
Lemma cnLO : layout_ok ly. Proof. exact (amr_layout _ _ _ _ _ cnM). Qed.
Lemma cnWF : WfR_cf (as_universe B) 0 0 0 X. Proof. exact (amr_wfr _ _ _ _ _ cnM). Qed.
Lemma cnSY : asyms_ok B. Proof. exact (amr_syms _ _ _ _ _ cnM). Qed.
Lemma cnLED : ALedger_cf im_segs ly X md. Proof. exact (proj1 (proj2 MR)). Qed.

Lemma cnSX : forall i j x y, (i < j)%nat -> nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y ->
zdisjoint x y.
Proof. intros i j x y Hij Hi Hj. exact (pairwise_nth_n zdisjoint _ i j x y (lo_disj _ cnLO) Hij Hi Hj). Qed.
Ltac sx i j := let D := fresh "DJ" in pose proof (cnSX i j _ _ ltac:(lia) eq_refl eq_refl) as D; unfold zdisjoint in D; cbn [fst snd] in D.

(* the reads off the window *)
Lemma AGn : forall a, okn a -> rd1 a = rd a.
Proof.
intros a [H1 H2]. unfold aview, mbyte, mrestrict.
rewrite (MEQ1 (Z_to_bv 64 a)); [|rewrite unsigned_lit_small by exact H1; exact H2].
rewrite (HWH (Z_to_bv 64 a)); [reflexivity| |];
rewrite unsigned_lit_small by exact H1; intros HD; apply H2; unfold cnwin; tauto.
Qed.

Lemma VISn : forall a, rd a <> None -> rd1 a <> None.
Proof.
intros a Hv. unfold aview, mbyte, mrestrict in Hv |- *.
assert (EX : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a)) = Z_to_bv 64 a) by apply Z_to_bv_bv_unsigned.
assert (DEC : cnwin (bv_unsigned (Z_to_bv 64 a)) \/ ~ cnwin (bv_unsigned (Z_to_bv 64 a))) by (unfold cnwin; lia).
destruct DEC as [Hw|Hw].
- destruct (PRES1 _ Hw) as [Hh [bb Hb]]. rewrite EX in Hh, Hb. rewrite Hh, Hb. discriminate.
- rewrite (MEQ1 (Z_to_bv 64 a) Hw).
  rewrite (HWH (Z_to_bv 64 a)); [exact Hv| |]; intros HD; apply Hw; unfold cnwin; tauto.
Qed.


(* The walk's written values at EnsureFreeArraySpace's return (DMcdR.v:137-191): the region's mapped-free-array word
   takes the grown size, the new map is zeroed and its shadow is the free-array poison. *)
Hypothesis V_RG24 : forall k, (k < 8)%nat -> rd1 (RG + 24 + Z.of_nat k) = Some (le_byte (mf + kFreeArrayMapSize) 8 k).
Hypothesis V_MAP : forall a, fadr <= a < fadr + kUserMapSize -> rd1 a = Some (le_byte 0 1 0).
Hypothesis V_SH : forall a, shf <= a < shf + 32768 -> rd1 a = Some (le_byte 250 1 0).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The zones apart from EnsureFreeArraySpace's frame.                                                               *)
Lemma cn_prim_hi : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL.
Proof. pose proof (lo_high _ cnLO) as IP. unfold in_high in IP. cbn [fst snd] in IP. lia. Qed.
Lemma cn_Tapp : in_app T kThreadObjSize.
Proof. exact (proj1 (Forall_forall _ _) (lo_app _ cnLO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)). Qed.
Lemma cn_space : ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize.
Proof. pose proof (lo_space_in _ cnLO) as [S1 S2]. lia. Qed.
Lemma cn_stk : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top _ cnLO) as (_ & _ & _ & T4 & _ & _ & T7). lia. Qed.
Lemma cn_ro : region_off c = c * 2 ^ 32. Proof. exact (region_off_eq c ltac:(lia)). Qed.
Lemma cn_fa : 0 <= mf <= kFreeArrayMax /\ 4 * fa_len (rg_free (reg X c)) <= mf.
Proof.
pose proof (wfr_classes _ _ _ _ _ cnWF c ltac:(lia)) as CL.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F3.
pose proof (wrc_runs _ _ _ _ _ _ CL) as RU. pose proof (fa_len_nonneg _ RU) as F0.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as F4. lia.
Qed.

Lemma cn_slot : ly_prim ly <= fadr /\ fadr + kUserMapSize <= ly_prim ly + kPrimResvSize /\ kHighMemBeg <= fadr /\
ly_space ly + c * 2 ^ 32 + kFreeArrayOffset <= fadr /\ fadr + kUserMapSize < ly_space ly + kRegionInfoOff.
Proof.
pose proof cn_prim_hi as [H1 H2]. pose proof cn_space as [H4 H5]. pose proof cn_fa as [[M1 M1'] M2].
pose proof cn_ro as RO. pose proof (region_in_prim ly c cnLO ltac:(lia)) as (R1 & R2 & _ & R4 & _).
unfold fa_base, region_base in *. rewrite RO in *.
unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kFreeArrayMapSize, kRegionInfoOff in *.
repeat split; try lia; try nia.
Qed.

Lemma cn_news_band : forall a, shf <= a < shf + 32768 -> kLowShadowBeg <= a < kHighMemBeg.
Proof.
intros a Ha. pose proof cn_slot as (S1 & S2 & S3 & _). pose proof cn_prim_hi as [P1 P2].
assert (APP : in_app fadr kUserMapSize) by (unfold in_app; split; [unfold kHighMemBeg in *; lia | right; lia]).
assert (IB : forall i, 0 <= i < kUserMapSize -> in_band_rw (shadow_addr (fadr + i)))
  by (intros i Hi; exact (shadow_addr_in_band _ kUserMapSize i APP Hi)).
pose proof (IB 0 ltac:(unfold kUserMapSize; lia)) as I0. rewrite Z.add_0_r in I0.
pose proof (IB (kUserMapSize - 8) ltac:(unfold kUserMapSize; lia)) as I1.
unfold shadow_addr in *.
assert (D1 : (fadr + (kUserMapSize - 8)) / 8 = fadr / 8 + 32767)
  by (unfold kUserMapSize; replace (262144 - 8) with (32767 * 8) by lia; apply Z.div_add; lia).
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.

Lemma okn_T : forall a, T <= a < T + kThreadObjSize ->
~ (T + 2768 <= a < T + 2800) -> ~ (T + 2872 <= a < T + 2888) -> okn a.
Proof.
intros a Ha N1 N2. pose proof cn_prim_hi as [H1 H2]. pose proof cn_Tapp as H3. pose proof cn_space as [H4 H5].
pose proof cn_stk as [H6 H7]. pose proof cn_slot as (S1 & S2 & S3 & _).
pose proof (lo_space_in _ cnLO) as [SP1 SP2]. ceil.
split; [destruct H3 as [HT0 [HTL|[HTH HTC]]]; unfold in_app, kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|].
intros [Hs|[Hr|[Hj1|[Hj2|[Hq|[Hq2|[Hm|Hsh]]]]]]].
- sx 2%nat 8%nat. unfold kThreadObjSize in *. destruct Hstk as [K1 K2]. lia.
- sx 0%nat 2%nat. unfold kRegionInfoOff, kSpaceSize, kThreadObjSize in *. lia.
- sx 0%nat 2%nat. unfold kRegionInfoOff, kSpaceSize, kThreadObjSize in *. lia.
- sx 0%nat 2%nat. unfold kRegionInfoOff, kSpaceSize, kThreadObjSize in *. lia.
- exact (N1 Hq).
- exact (N2 Hq2).
- sx 0%nat 2%nat. unfold kThreadObjSize in *. lia.
- pose proof (cn_news_band a Hsh) as HB.
  destruct H3 as [HT0 [HTL|[HTH HTC]]]; unfold in_app, kThreadObjSize, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma okn_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
~ (RG + 24 <= a < RG + 32) -> ~ (RG + 64 <= a < RG + 68) -> ~ (RG + 69 <= a < RG + 128) ->
~ (fadr <= a < fadr + kUserMapSize) -> okn a.
Proof.
intros a Ha NR1 NR2 NR3 NM. pose proof cn_prim_hi as [H1 H2]. pose proof cn_Tapp as H3. pose proof cn_space as [H4 H5].
pose proof cn_stk as [H6 H7]. ceil.
split; [unfold ASAN_CEIL, kHighMemBeg in *; lia|].
intros [Hs|[Hr|[Hj1|[Hj2|[Hq|[Hq2|[Hm|Hsh]]]]]]].
- sx 0%nat 8%nat. destruct Hstk as [K1 K2]. lia.
- exact (NR1 Hr).
- exact (NR2 Hj1).
- exact (NR3 Hj2).
- sx 0%nat 2%nat. unfold kThreadObjSize in *. lia.
- sx 0%nat 2%nat. unfold kThreadObjSize in *. lia.
- exact (NM Hm).
- pose proof (cn_news_band a Hsh) as HB. unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The window, coarsened to five zones. *)
Lemma cnwin_zones : forall a, cnwin a ->
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (RG + 24 <= a < RG + 128) \/ (T + 2768 <= a < T + 2888) \/
(fadr <= a < fadr + kUserMapSize) \/ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros a [Hs|[Hr|[Hj1|[Hj2|[Hq|[Hq2|[Hm|Hsh]]]]]]]; destruct Hstk as [K1 K2].
- left. lia.
- right; left. lia.
- right; left. lia.
- right; left. lia.
- right; right; left. lia.
- right; right; left. lia.
- right; right; right; left. exact Hm.
- right; right; right; right. exact (cn_news_band a Hsh).
Qed.

Lemma cn_RG_prim : ly_prim ly <= RG /\ RG + 128 <= ly_prim ly + kPrimResvSize /\ fadr + kUserMapSize < RG.
Proof.
pose proof cn_space as [S1 S2]. pose proof cn_slot as (_ & _ & _ & _ & S5).
unfold kRegionInfoOff, kSpaceSize in *. lia.
Qed.

Lemma okn_static : forall j e a, (3 <= j <= 7)%nat \/ j = 1%nat -> nth_error (static_extents ly) j = Some e ->
fst e <= a < fst e + snd e -> okn a.
Proof.
intros j e a Hj He Ha.
pose proof (proj1 (Forall_forall _ _) (lo_app _ cnLO) e ltac:(unfold static_extents in He; rewrite nth_error_app1 in He by (cbn; lia);
  eapply nth_error_In; exact He)) as HE. cbn [fst snd] in HE.
pose proof cn_RG_prim as (R1 & R2 & R3). pose proof cn_slot as (S1 & S2 & S3 & _). pose proof cn_Tapp as HT.
split; [destruct HE as [E0 [EL|[EH EC]]]; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|]. intros HD.
destruct (cnwin_zones a HD) as [Y|[Y|[Y|[Y|Y]]]].
- pose proof (cnSX j 8%nat _ _ ltac:(lia) He eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- pose proof (cnSX 0%nat j _ _ ltac:(lia) eq_refl He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- assert (j <> 2)%nat by lia. destruct (Nat.lt_ge_cases j 2).
  + pose proof (cnSX j 2%nat _ _ ltac:(lia) He eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kThreadObjSize in *. lia.
  + pose proof (cnSX 2%nat j _ _ ltac:(lia) eq_refl He) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kThreadObjSize in *. lia.
- pose proof (cnSX 0%nat j _ _ ltac:(lia) eq_refl He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- destruct HE as [E0 [EL|[EH EC]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma okn_img : forall a, in_zr a (ly_img ly) -> okn a.
Proof.
intros a Ha. pose proof (lo_img _ cnLO) as (I1 & I2 & I3 & _). unfold in_zr in Ha. rewrite I1 in Ha.
pose proof cn_RG_prim as (R1 & R2 & R3). pose proof cn_slot as (S1 & S2 & S3 & _).
split; [unfold kImgLo, kImgEnd in *; lia|]. intros HD.
destruct (cnwin_zones a HD) as [Y|[Y|[Y|[Y|Y]]]].
- sx 8%nat 9%nat. unfold in_zr, kImgLo, kImgEnd in *. lia.
- sx 0%nat 9%nat. unfold in_zr, kImgLo, kImgEnd in *. lia.
- sx 2%nat 9%nat. unfold in_zr, kImgLo, kImgEnd, kThreadObjSize in *. lia.
- sx 0%nat 9%nat. unfold in_zr, kImgLo, kImgEnd in *. lia.
- unfold kImgLo, kImgEnd, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma okn_sec : forall e a, In e (sec_extents ly X) -> fst e <= a < fst e + snd e -> okn a.
Proof.
intros e a He Ha.
assert (D : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint e y).
{ intros j y Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ cnM)) He).
  eapply nth_error_In. exact Hj. }
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ cnM)) e He) as (_ & IA & _).
pose proof cn_RG_prim as (R1 & R2 & R3). pose proof cn_slot as (S1 & S2 & S3 & _).
split; [destruct IA as [E0 [EL|[EH EC]]]; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|]. intros HD.
destruct (cnwin_zones a HD) as [Y|[Y|[Y|[Y|Y]]]].
- pose proof (D 8%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
- pose proof (D 0%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
- pose proof (D 2%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold kThreadObjSize in *. lia.
- pose proof (D 0%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
- destruct IA as [E0 [EL|[EH EC]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
Qed.

(* the shadow band, off the new map's shadow *)
Lemma okn_band : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ (shf <= a < shf + 32768) -> okn a.
Proof.
intros a Ha NS. pose proof cn_RG_prim as (R1 & R2 & R3). pose proof cn_slot as (S1 & S2 & S3 & _).
pose proof cn_prim_hi as [H1 H2]. pose proof cn_Tapp as HT. pose proof cn_stk as [K1 K2].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
intros [Hs|[Hr|[Hj1|[Hj2|[Hq|[Hq2|[Hm|Hsh]]]]]]]; destruct Hstk as [Q1 Q2];
try (exact (NS Hsh));
destruct HT as [T0 [TL|[TH TC]]]; unfold kLowShadowBeg, kHighMemBeg, kThreadObjSize in *; lia.
Qed.

(* The primary-reserve zones apart from the region record and the new map. *)
Lemma okn_rinfo : forall c' a, 1 <= c' <= 31 -> ly_space ly + kRegionInfoOff + 128 * c' <= a < ly_space ly + kRegionInfoOff + 128 * c' + 128 ->
(c' = c -> a < RG + 24 \/ (RG + 32 <= a < RG + 64) \/ a = RG + 68) -> okn a.
Proof.
intros c' a Hc' Ha NW. pose proof cn_space as [S1 S2]. pose proof cn_RG_prim as (R1 & R2 & R3).
assert (SEP : c' <> c -> a < RG \/ RG + 128 <= a).
{ intros NE. destruct (Z.lt_trichotomy c' c) as [L|[E|L]]; [lia | exfalso; exact (NE E) | lia]. }
pose proof cn_slot as (_ & _ & _ & _ & S5).
assert (NREC : ~ (RG + 24 <= a < RG + 32) /\ ~ (RG + 64 <= a < RG + 68) /\ ~ (RG + 69 <= a < RG + 128)).
{ destruct (Z.eq_dec c' c) as [->|NE].
  - destruct (NW eq_refl) as [Y|[Y|Y]]; lia.
  - pose proof (SEP NE). lia. }
destruct NREC as (N1 & N2 & N3).
apply okn_prim; [unfold kRegionInfoOff, kSpaceSize in *; lia | exact N1 | exact N2 | exact N3 | lia].
Qed.

Definition okrn (lo len : Z) : Prop := forall a, lo <= a < lo + len -> okn a.

Lemma okn_fa : forall c' i, 1 <= c' <= 31 -> 0 <= i -> 4 * i + 4 <= rg_mapped_fa (reg X c') -> okrn (fa_base ly c' + 4 * i) 4.
Proof.
intros c' i Hc' Hi Hi2 a Ha. pose proof cn_space as [S1 S2]. pose proof cn_RG_prim as (R1 & R2 & R3).
pose proof (region_off_eq c' ltac:(lia)) as RO'. pose proof cn_ro as RO.
pose proof (wrc_fa_bound _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cnWF c' ltac:(lia))) as FBx.
pose proof (region_in_prim ly c' cnLO ltac:(lia)) as (P1 & P2 & _). unfold region_base in P1, P2.
unfold fa_base in Ha.
assert (BELOW : a < RG) by (unfold kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kSpaceSize in *; rewrite RO' in Ha; nia).
apply okn_prim; [unfold kFreeArrayOffset, kFreeArrayMax in *; lia | lia | lia | lia |].
- intros Hm. pose proof cn_fa as [[M0 M1] M2]. destruct (Z.eq_dec c' c) as [->|NE].
  + unfold fa_base in Hm. unfold kUserMapSize in *. lia.
  + unfold fa_base, region_base in Hm. rewrite RO in Hm. rewrite RO' in Ha.
    unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kFreeArrayMapSize in *. destruct (Z.lt_trichotomy c' c) as [L|[E|L]]; [nia | lia | nia].
Qed.

Lemma okn_chunk : forall k a, In k (st_chunks X) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> okn a.
Proof.
intros k a Hk Ha. pose proof cn_RG_prim as (R1 & R2 & R3). pose proof cn_ro as RO.
destruct (RL.extent_zone_cf B ly X Hp _ k cnM Hk) as [[P1 P2]|(m & len & Hin & E1 & E2)].
- pose proof (RL.chunk_facts_cf B ly X Hp _ k cnM Hk) as CF. unfold RL.cfacts_cf in CF.
  destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k) as [|o|r o|cc pp] eqn:Eb; try solve [destruct GG].
  + cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
    set (c2 := prim_class o) in *.
    pose proof (region_off_eq c2 ltac:(lia)) as RO2.
    pose proof (wrc_mapped_bound _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cnWF c2 ltac:(lia))) as MBx.
    pose proof (wrc_alloc _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cnWF c2 ltac:(lia))) as ALx.
    pose proof cn_space as [S1 S2].
    unfold region_base in Gbase. rewrite RO2 in Gbase.
    assert (BELOW : a < RG) by (unfold kRegionInfoOff, kSpaceSize, kFreeArrayOffset in *; nia).
    apply okn_prim; [lia | lia | lia | lia |].
    * intros Hm. pose proof cn_fa as [[M0 M1] M2]. unfold fa_base, region_base in Hm. rewrite RO in Hm.
      unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kFreeArrayMapSize in *.
      destruct (Z.lt_trichotomy c2 c) as [L|[E|L]]; [nia | | nia].
      clearbody c2. subst c2. unfold ck_base in *. nia.
  + destruct GG as (-> & _ & Gbase & Gext & Gin & _). exact (okn_sec _ a Gin ltac:(unfold kPage in *; cbn [fst snd]; lia)).
- exact (okn_sec (m, len) a Hin ltac:(cbn [fst snd]; unfold kPage in *; lia)).
Qed.


Lemma okn_batch : forall b a, In b (all_batches X) -> ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> okn a.
Proof.
intros b a Hb Ha.
pose proof (wfr_classes _ _ _ _ _ cnWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (xb := b_self b - region_off kBatchClass).
assert (INB : In xb (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) xb ltac:(rewrite !in_app_iff; tauto)) as [Z1 Z2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in Z2, AA.
assert (XB : xb + 8192 <= rg_alloc_user (reg X kBatchClass))
  by (apply Z.mod_divide in Z2 as [q Hq]; [|lia]; apply Z.mod_divide in AA as [q' Hq']; [|lia]; nia).
pose proof (region_in_prim ly kBatchClass cnLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (region_off_eq kBatchClass ltac:(unfold kBatchClass; lia)) as RO24.
pose proof cn_ro as RO. pose proof cn_space as [S1 S2]. pose proof cn_fa as [[M0 M1] M2].
unfold region_base in R1, R2. unfold kBatchBytes in *.
assert (BELOW : a < RG) by (unfold xb in *; rewrite RO24 in *; unfold kRegionInfoOff, kSpaceSize, kFreeArrayOffset, kBatchClass in *; lia).
apply okn_prim; [unfold xb in *; rewrite RO24 in *; unfold kFreeArrayOffset, kBatchClass in *; lia | lia | lia | lia |].
intros Hm. unfold fa_base, region_base in Hm. rewrite RO in Hm. unfold xb in *. rewrite RO24 in *.
unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kFreeArrayMapSize, kBatchClass in *.
destruct (Z.lt_trichotomy 24 c) as [L|[E|L]]; [nia | lia | nia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells at the grown state over the intermediate memory.                                                       *)
Lemma cnOLD : forall ce, In ce (acells_cf B ly X) -> cell_holds B ly rd ce.
Proof. intros ce Hce. exact (proj1 (Forall_forall _ _) (amr_cells _ _ _ _ _ cnM) ce Hce). Qed.

Lemma cn_cell_xfer : forall ce, cell_holds B ly rd ce ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> okn (aeval B ly (c_at ce) + j)) -> cell_holds B ly rd1 ce.
Proof. intros ce Hce Hok. eapply (cell_holds_agree B ly rd rd1 ce Hce). intros j Hj. apply AGn, Hok, Hj. Qed.

Lemma cn_cells_ok_xfer : forall L, Forall (fun ce => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> okn (aeval B ly (c_at ce) + j)) L ->
Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd1) L.
Proof.
intros L OK O. apply Forall_forall. intros ce Hce. apply cn_cell_xfer;
[exact (proj1 (Forall_forall _ _) O ce Hce) | exact (proj1 (Forall_forall _ _) OK ce Hce)].
Qed.

Lemma cn_cells_rng : forall L lo len, okrn lo len -> Forall (fun ce => lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len) L ->
Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd1) L.
Proof.
intros L lo len OK IN OLD. apply cn_cells_ok_xfer; [|exact OLD].
eapply Forall_impl; [|exact IN]. intros ce [I1 I2] j Hj. apply OK. lia.
Qed.

Lemma cn_img_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ cnSY) r Hr) as E.
apply Exists_exists in E as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ cnM) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr. lia.
Qed.
Lemma cn_area_ok : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> okn a.
Proof. intros r a Hr Ha. exact (okn_img a (cn_img_area r a Hr Ha)). Qed.
Lemma cn_inst_ok : forall a, as_inst B <= a < as_inst B + 3632 -> okn a.
Proof. intros a Ha. apply (cn_area_ok (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia]. Qed.

Lemma okn_Tlow : forall a, T <= a < T + 2768 -> okn a.
Proof. intros a Ha. apply okn_T; [unfold kThreadObjSize; lia | lia | lia]. Qed.

Lemma cn_cache : forall c', 1 <= c' <= 31 -> Forall (cell_holds B ly rd) (cache_cells X c') -> Forall (cell_holds B ly rd1) (cache_cells X c').
Proof.
intros c' Hc' O. apply (cn_cells_rng _ (T + t_cache + 80 * c') 80); [| |exact O].
- intros a Ha. apply okn_Tlow. unfold t_cache in *. lia.
- pose proof (wrc_cache _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cnWF c' ltac:(lia))) as WC.
  pose proof (class_ok c' ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6).
  unfold cache_cells, t_cache. destruct (st_cache_inited X).
  + destruct WC as [PM PL]. repeat (apply Forall_cons; [cbn; lia|]).
    apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
    apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

Lemma cn_region_other : forall c', 1 <= c' <= 31 -> c' <> c -> Forall (cell_holds B ly rd) (region_cells_cf X c') ->
Forall (cell_holds B ly rd1) (region_cells_cf X c').
Proof.
intros c' Hc' Hne O. apply (cn_cells_rng _ (ly_space ly + kRegionInfoOff + 128 * c') 128); [| |exact O].
- intros a Ha. apply (okn_rinfo c'); [lia | lia | intros E; exfalso; exact (Hne E)].
- unfold region_cells_cf, region_cells. cbv zeta. cbn [removelast].
  repeat (apply Forall_cons; [cbn [c_at c_w z8 z1 c8 c1 aeval aoff]; cbn; lia|]). apply Forall_nil.
Qed.

Lemma cn_region_c : (Z.to_nat c < length (st_regions X))%nat -> Forall (cell_holds B ly rd) (region_cells_cf X c) ->
Forall (cell_holds B ly rd1) (region_cells_cf (cgX X c) c).
Proof.
intros Hlenr OLDR.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RG + d) by (intros d; cbn; lia).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RG) by (cbn; lia).
unfold region_cells_cf, region_cells in OLDR |- *. cbv zeta in OLDR |- *. cbn [removelast] in OLDR |- *.
rewrite (cg_reg_c X c Hc Hlenr). unfold cgr. cbn [rg_free rg_mapped_fa rg_alloc_user rg_mapped_user].
apply Forall_cons_iff in OLDR as [O0 OLDR]. apply Forall_cons_iff in OLDR as [O8 OLDR].
apply Forall_cons_iff in OLDR as [O16 OLDR]. apply Forall_cons_iff in OLDR as [O24 OLDR].
apply Forall_cons_iff in OLDR as [O32 OLDR]. apply Forall_cons_iff in OLDR as [O40 OLDR].
apply Forall_cons_iff in OLDR as [O48 OLDR]. apply Forall_cons_iff in OLDR as [O56 _].
assert (OKR : forall d, 0 <= d < 128 -> d < 24 \/ (32 <= d < 64) \/ d = 68 -> okn (RG + d)).
{ intros d Hd Hd2. apply (okn_rinfo c); [lia | lia | intros _; lia]. }
Ltac gcell O ER ER0 OKR := apply (cn_cell_xfer _ O); intros j Hj; cbn [c_at c_w z8 z1 c8 c1] in Hj |- *; rewrite ?ER, ?ER0;
  match goal with |- okn ?a => replace a with (RG + (a - RG)) by lia end; apply OKR; lia.
apply Forall_cons. { gcell O0 ER ER0 OKR. }
apply Forall_cons. { gcell O8 ER ER0 OKR. }
apply Forall_cons. { gcell O16 ER ER0 OKR. }
apply Forall_cons.
{ cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. rewrite ER. cbn [aeval]. exact (V_RG24 kk Hkk). }
apply Forall_cons. { gcell O32 ER ER0 OKR. }
apply Forall_cons. { gcell O40 ER ER0 OKR. }
apply Forall_cons. { gcell O48 ER ER0 OKR. }
apply Forall_cons; [|apply Forall_nil]. { gcell O56 ER ER0 OKR. }
Qed.

Lemma cn_chunks : Forall (cell_holds B ly rd1) (flat_map chunk_cells (st_chunks X)).
Proof.
apply Forall_flat_map'. intros k Hk.
pose proof (RL.chunk_facts_cf B ly X Hp _ k cnM Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d)
  by (intros d; unfold ck_base, sptr_addr; destruct (ck_beg k) as [|o|r o|cc pp]; try solve [destruct GG]; cbn; lia).
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d')
  by (intros d d'; unfold ck_base, sptr_addr; destruct (ck_beg k) as [|o|r o|cc pp]; try solve [destruct GG]; cbn; lia).
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & _).
apply (cn_cells_rng _ (ck_base B ly k) (ck_rz k)).
- intros a Ha. exact (okn_chunk k a Hk ltac:(lia)).
- unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
    assert (32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|lia]; lia).
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- apply Forall_forall. intros ce Hce. apply cnOLD. unfold acells_cf. rewrite !in_app_iff.
  right; right; left. apply in_flat_map. exists k. split; [exact Hk | exact Hce].
Qed.

Lemma cm_img_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ cnSY) r Hr) as E.
apply Exists_exists in E as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ cnM) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr. lia.
Qed.

Lemma cn_sec : Forall (cell_holds B ly rd) (sec_cells X) -> Forall (cell_holds B ly rd1) (sec_cells X).
Proof.
intros O. pose proof (wfr_secondary _ _ _ _ _ cnWF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
apply cn_cells_ok_xfer; [|exact O]. unfold sec_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply cn_inst_ok; unfold o_sec_reserved; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply cn_inst_ok; unfold o_sec_n; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply cn_inst_ok; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  intros j Hj. cbn [c_at c_w aeval fst snd c8] in *.
  apply (okn_static 1%nat (ly_Q ly, kPtrArrayResv)); [right; reflexivity | reflexivity |
    cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia].
- apply Forall_forall. intros ce Hce. apply in_flat_map in Hce as (k0 & Hk0 & Hce).
  pose proof (RL.chunk_facts_cf B ly X Hp _ k0 cnM Hk0) as CF. unfold RL.cfacts_cf in CF.
  destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k0) as [|o|r o|cc pp] eqn:Eb; try solve [destruct Hce].
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  assert (SM : 4096 + 17 <= sec_map_size (ck_req k0))
    by (pose proof (req_size_bounds (ck_req k0) ltac:(lia)) as (_ & Q1 & _); unfold kPage in *; lia).
  destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
    apply (okn_sec _ _ Gin); cbn [fst snd]; lia.
Qed.

Lemma cn_batch_cells_ok : forall l, incl l (all_batches X) ->
Forall (fun ce => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> okn (aeval B ly (c_at ce) + j)) (batch_cells l).
Proof.
intros l. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfr_quarantine _ _ _ _ _ cnWF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OKB : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> okn a)
  by (intros a Ha; exact (okn_batch b a (Hincl b (or_introl eq_refl)) Ha)).
unfold kBatchBytes in OKB.
apply Forall_cons; [intros j Hj; cbn [c_at c_w c8 z8 batch_exp aeval aoff] in *; apply OKB; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w c8 z8 batch_exp aeval aoff] in *; apply OKB; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w c8 z8 batch_exp aeval aoff] in *; apply OKB; lia|].
apply Forall_app. split.
- apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
  intros j Hj. cbn [fst snd c_at c_w c8 batch_exp aeval aoff] in *. apply OKB. lia.
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.

Lemma cn_quar : Forall (cell_holds B ly rd) (quar_cells X) -> Forall (cell_holds B ly rd1) (quar_cells X).
Proof.
intros O.
assert (OKT : forall a, T + t_qc <= a < T + t_qc + 32 -> okn a).
{ intros a Ha. apply okn_Tlow. unfold t_qc in *. lia. }
apply cn_cells_ok_xfer; [|exact O]. unfold quar_cells, qc_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply cn_inst_ok; unfold o_q_cmutex, o_quar; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply cn_inst_ok; unfold o_q_rmutex, o_quar; lia|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8 aoff] in *; apply OKT; unfold t_qc in *; lia|]).
  apply cn_batch_cells_ok. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb.
- do 4 (apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8 aoff] in *;
    apply cn_inst_ok; unfold o_q_size, o_quar; lia|]).
  apply cn_batch_cells_ok. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb.
Qed.

Lemma cn_fs : Forall (cell_holds B ly rd) (fs_cells X) -> Forall (cell_holds B ly rd1) (fs_cells X).
Proof.
intros O. apply (cn_cells_rng _ (ly_F ly) kFakeFramesOff); [| |exact O].
- intros a Ha. apply (okn_static 3%nat (ly_F ly, kFakeStackSize)); [left; lia | reflexivity |
    cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia].
- unfold fs_cells, kFakeFramesOff. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|].
  apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.

Lemma cn_depot : Forall (cell_holds B ly rd) (depot_cells ly X) -> Forall (cell_holds B ly rd1) (depot_cells ly X).
Proof.
intros O. apply cn_cells_ok_xfer; [|exact O]. unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c4 z4] in *;
  apply (cn_area_ok (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cn_area_ok (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cn_area_ok (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cn_area_ok (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]|]. apply Forall_nil.
Qed.

Lemma cn_ialloc : Forall (cell_holds B ly rd) (ialloc_cells B X) -> Forall (cell_holds B ly rd1) (ialloc_cells B X).
Proof.
intros O. pose proof (aso_ialloc _ cnSY) as [I1 I2].
apply cn_cells_ok_xfer; [|exact O]. unfold ialloc_cells. cbv zeta.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *;
  apply (cn_area_ok (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *;
  apply (cn_area_ok (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cn_area_ok (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cn_area_ok (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia]|]. apply Forall_nil.
Qed.

Lemma cn_thread : Forall (cell_holds B ly rd) thread_cells -> Forall (cell_holds B ly rd1) thread_cells.
Proof.
intros O.
apply cn_cells_ok_xfer; [|exact O]. unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
intros j Hj. cbn [c_at c_w aeval c1 z1] in *. apply okn_T; unfold t_unwinding, kThreadObjSize in *; lia.
Qed.


Lemma cn_FMI {A0 : Type} : forall (f : Z -> list A0) (P : A0 -> Prop) c', 1 <= c' <= 31 ->
Forall P (flat_map f (zseq 1 31)) -> Forall P (f c').
Proof.
intros f P c' Hc' H. apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) H). apply in_flat_map.
exists c'. split; [apply In_zseq; lia | exact Hy].
Qed.

Lemma cn_cells : (Z.to_nat c < length (st_regions X))%nat -> Forall (cell_holds B ly rd1) (acells_cf B ly (cgX X c)).
Proof.
intros Hlenr.
pose proof (amr_cells _ _ _ _ _ cnM) as C. unfold acells_cf in C. rewrite !Forall_app in C.
destruct C as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
unfold acells_cf. rewrite !Forall_app.
split.
{ apply Forall_flat_map'. intros c' Hc0. apply zseq_In in Hc0.
  destruct (Z.eq_dec c' c) as [->|NE].
  - exact (cn_region_c Hlenr (cn_FMI _ _ c ltac:(lia) O1)).
  - assert (E : region_cells_cf (cgX X c) c' = region_cells_cf X c')
      by (unfold region_cells_cf, region_cells; rewrite (cg_reg_other X c Hc Hlenr c' ltac:(lia) NE); reflexivity).
    rewrite E. exact (cn_region_other c' ltac:(lia) NE (cn_FMI _ _ c' ltac:(lia) O1)). }
split.
{ apply Forall_flat_map'. intros c' Hc0. apply zseq_In in Hc0.
  change (cache_cells (cgX X c) c') with (cache_cells X c'). exact (cn_cache c' ltac:(lia) (cn_FMI _ _ c' ltac:(lia) O2)). }
split. { change (st_chunks (cgX X c)) with (st_chunks X). exact cn_chunks. }
split. { change (sec_cells (cgX X c)) with (sec_cells X). exact (cn_sec O4). }
split. { change (quar_cells (cgX X c)) with (quar_cells X). exact (cn_quar O5). }
split. { change (fs_cells (cgX X c)) with (fs_cells X). exact (cn_fs O6). }
split. { change (depot_cells ly (cgX X c)) with (depot_cells ly X). exact (cn_depot O7). }
split. { change (ialloc_cells B (cgX X c)) with (ialloc_cells B X). exact (cn_ialloc O8). }
exact (cn_thread O9).
Qed.

Lemma cn_al8_slot : exists q, fadr = 8 * q.
Proof.
pose proof (lo_space_al _ cnLO) as SA. pose proof cn_fa as [[M0 M1] M2].
pose proof (wrc_fa _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cnWF c ltac:(lia))) as [_ Fal].
apply Z.mod_divide in SA as [s Hs]; [|lia]. apply Z.mod_divide in Fal as [m Hm]; [|unfold kFreeArrayMapSize; lia].
unfold fa_base, region_base. rewrite cn_ro. rewrite Hs, Hm.
unfold kFreeArrayOffset, kFreeArrayMapSize. exists (8192 * s + c * 536870912 + 469762048 + 32768 * m). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The shadow at the grown state: the new map's granules read the free-array poison; every other granule is X's.   *)
Lemma cn_inr_app : forall g l1 l2, in_rangesb g (l1 ++ l2) = in_rangesb g l1 || in_rangesb g l2.
Proof. intros g l1 l2. induction l1 as [|[lo len] t IH]; cbn; [reflexivity|]. rewrite IH. apply orb_assoc. Qed.
Lemma cn_inr_flat : forall {A0} g (f : A0 -> list (Z * Z)) l, in_rangesb g (flat_map f l) = existsb (fun x => in_rangesb g (f x)) l.
Proof. intros A0 g f l. induction l as [|x t IH]; cbn; [reflexivity|]. rewrite cn_inr_app, IH. reflexivity. Qed.

Lemma cn_existsb_ext {A0 : Type} : forall (f g : A0 -> bool) l, (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof. intros f g l. induction l as [|x t IH]; intros H; cbn; [reflexivity|]. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

Lemma cn_newmap_dec : forall g, (fadr <= g < fadr + kUserMapSize) \/ ~ (fadr <= g < fadr + kUserMapSize).
Proof. intros g. lia. Qed.

Lemma cn_poison_eq : (Z.to_nat c < length (st_regions X))%nat -> forall g, ~ (fadr <= g < fadr + kUserMapSize) ->
in_rangesb g (fa_poison_ranges ly (cgX X c)) = in_rangesb g (fa_poison_ranges ly X).
Proof.
intros Hlenr g Hg. unfold fa_poison_ranges. rewrite !cn_inr_app, !cn_inr_flat.
f_equal. apply cn_existsb_ext. intros c' Hc'. apply zseq_In in Hc'.
destruct (Z.eq_dec c' c) as [->|NE].
- rewrite (cg_reg_c X c Hc Hlenr). unfold cgr. cbn [rg_mapped_user rg_mapped_fa in_rangesb].
  f_equal. f_equal. unfold fa_base in Hg |- *. unfold kUserMapSize, kFreeArrayMapSize in *.
  destruct (Z.leb_spec (region_base ly c + kFreeArrayOffset) g); destruct (Z.ltb_spec g (region_base ly c + kFreeArrayOffset + (rg_mapped_fa (reg X c) + 262144)));
  destruct (Z.ltb_spec g (region_base ly c + kFreeArrayOffset + rg_mapped_fa (reg X c))); cbn; try reflexivity; lia.
- rewrite (cg_reg_other X c Hc Hlenr c' ltac:(lia) NE). reflexivity.
Qed.

Lemma cn_poison_new : (Z.to_nat c < length (st_regions X))%nat -> forall g, fadr <= g < fadr + kUserMapSize ->
in_rangesb g (fa_poison_ranges ly (cgX X c)) = true.
Proof.
intros Hlenr g Hg. unfold fa_poison_ranges. rewrite cn_inr_app, cn_inr_flat. apply orb_true_intro. left.
apply existsb_exists. exists c. split; [apply In_zseq; lia|].
rewrite (cg_reg_c X c Hc Hlenr). unfold cgr. cbn [rg_mapped_user rg_mapped_fa in_rangesb].
apply orb_true_intro. right. apply orb_true_intro. left. apply andb_true_intro.
pose proof cn_fa as [[M0 M1] M2]. unfold fa_base, region_base in Hg |- *. unfold kUserMapSize, kFreeArrayMapSize in *. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* a byte of a live chunk's extent is off the window, so it is never in the new map *)
Lemma cn_chunk_not_new : forall k g, In k (st_chunks X) -> ck_base B ly k <= g < ck_base B ly k + ck_extent k ->
~ (fadr <= g < fadr + kUserMapSize).
Proof. intros k g Hk Hg Hn. destruct (okn_chunk k g Hk Hg) as [_ HW]. apply HW. unfold cnwin. tauto. Qed.

Lemma cn_find_none : forall g, fadr <= g < fadr + kUserMapSize -> find_chunk_at B ly (st_chunks X) g = None.
Proof.
intros g Hg. destruct (find_chunk_at B ly (st_chunks X) g) as [k|] eqn:E; [|reflexivity].
destruct (find_chunk_at_In B ly _ g k E) as [Hk Hr]. exfalso. exact (cn_chunk_not_new k g Hk Hr Hg).
Qed.

Lemma cn_head_false : forall g, fadr <= g < fadr + kUserMapSize -> in_head Hp g = false.
Proof.
intros g Hg. unfold in_head. apply not_true_is_false. intros E. apply existsb_exists in E as (p & Hp' & Hpg).
apply andb_true_iff in Hpg as [P1 P2]. apply Z.leb_le in P1. apply Z.ltb_lt in P2.
pose proof (proj1 (Forall_forall _ _) (amr_hp_live _ _ _ _ _ cnM) p Hp') as (k & Hk & Hst & Ep & Hn).
pose proof (RL.chunk_facts_cf B ly X Hp _ k cnM Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (HPk : match ck_beg k with PPrim _ | PSec _ _ => True | _ => False end)
  by (destruct (ck_beg k); first [exact I | destruct GG]).
assert (UB : sptr_addr B ly (ck_user k) = ck_base B ly k + ck_rz k)
  by (unfold ck_user; rewrite (YG0s.sptr_addr_padd B ly _ _ HPk); unfold ck_base; lia).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & _).
apply (cn_chunk_not_new k g Hk); [|exact Hg]. rewrite Ep, UB in *. unfold ck_n in *. lia.
Qed.

(* The grant changes no chunk and no queue, so the exemption set is the cut's: the new map's granules take their
   value from the grant's poison (the left disjunct), the others transport. *)
Lemma cn_shadow : (Z.to_nat c < length (st_regions X))%nat -> shadow_ok_weak_cf B ly Hp rd1 (cgX X c).
Proof.
intros Hlenr g v Hg Hv. pose proof cn_slot as (S1 & S2 & S3 & _).
destruct (cn_newmap_dec g) as [HN|HN].
- unfold ashadow in Hv. change (st_chunks (cgX X c)) with (st_chunks X) in Hv.
  rewrite (cn_find_none g HN), (cn_poison_new Hlenr g HN) in Hv. injection Hv as <-.
  rewrite (cn_head_false g HN). unfold shHeapLeftRz.
  left. rewrite (V_SH (shadow_addr g)); [reflexivity|].
  destruct cn_al8_slot as [q Hq].
  assert (Gq : g = 8 * (g / 8)) by (pose proof (Z.div_mod g 8 ltac:(lia)) as DM; rewrite Hg, Z.add_0_r in DM; exact DM).
  unfold shadow_addr. rewrite Hq. rewrite (Z.mul_comm 8 q), Z_div_mult by lia. rewrite Hq in HN. unfold kUserMapSize in HN. lia.
- assert (EQ : ashadow B ly (cgX X c) g = ashadow B ly X g).
  { unfold ashadow. change (st_chunks (cgX X c)) with (st_chunks X). rewrite (cn_poison_eq Hlenr g HN). reflexivity. }
  rewrite EQ in Hv. pose proof (amr_shadow _ _ _ _ _ cnM g v Hg Hv) as HX.
  pose proof (RL.ashadow_low_cf B ly X Hp _ g v cnM Hv) as SL.
  assert (AG1 : rd1 (shadow_addr g) = rd (shadow_addr g)).
  { apply AGn. apply okn_band; [unfold SHADOW_OFF, kLowShadowBeg in *; lia|].
  intros Hs. apply HN. destruct cn_al8_slot as [q Hq]. unfold shadow_addr in Hs. rewrite Hq in Hs.
  rewrite Z.mul_comm, Z_div_mult in Hs by lia.
  pose proof (Z.div_mod g 8 ltac:(lia)) as DM. rewrite Hg, Z.add_0_r in DM. rewrite Hq. unfold kUserMapSize. lia. }
  rewrite AG1. destruct HX as [HL|[(k & (Hk & Hst & Hni) & HR) HP]]; [left; exact HL|].
  right. split; [|exact HP]. exists k. split; [|exact HR].
  split; [change (st_chunks (cgX X c)) with (st_chunks X); exact Hk|]. split; [exact Hst|]. exact Hni.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The remaining fields of the record at the grown state.                                                           *)
Lemma cn_zone_apart : forall lo len i, lo mod 8 = 0 -> 0 <= lo -> zdisjoint (lo, len) (fadr, kUserMapSize) ->
0 <= i < len / 8 -> ~ (shf <= shadow_addr lo + i < shf + 32768).
Proof.
intros lo len i Hm H0 DJ Hi Hs. destruct cn_al8_slot as [q Hq].
apply Z.mod_divide in Hm as [p Ep]; [|lia]. subst lo.
unfold shadow_addr in Hs. rewrite Hq in Hs. rewrite (Z.mul_comm p 8), (Z.mul_comm 8 q), !Z_div_mult in Hs by lia.
rewrite (Z.mul_comm p 8) in DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite Hq in DJ. unfold kUserMapSize in DJ.
pose proof (Z.mul_div_le len 8 ltac:(lia)). lia.
Qed.

Lemma cn_zshadow : zshadow_ok B ly rd1.
Proof.
pose proof (amr_zshadow _ _ _ _ _ cnM) as Z0. unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi.
unfold shadow_of_addr. fold (shadow_addr (fst r)). change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (RL.zshadow_low_cf B ly X Hp _ r i cnM Hr Hi) as ZL.
pose proof (RL.zshadow_range_facts_cf B ly X Hp _ r cnM Hr) as (A1 & A2 & A3 & A4 & _).
assert (DJ : zdisjoint r (fadr, kUserMapSize)).
{ pose proof cn_slot as (S1 & S2 & S3 & _). unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
  - sx 0%nat 8%nat. unfold zdisjoint. cbn [fst snd]. lia.
  - pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ cnM) r ltac:(apply in_app_iff; right; exact Hr)) as [I1 I2].
    sx 0%nat 9%nat. unfold zdisjoint, zr_sub, in_zr in *. destruct r as [lo len]. cbn [fst snd] in *. lia. }
rewrite AGn; [exact (proj1 (Forall_forall _ _) Z0 r Hr i Hi)|].
apply okn_band; [unfold SHADOW_OFF, kLowShadowBeg in *; lia|].
exact (cn_zone_apart (fst r) (snd r) i A1 A2 ltac:(destruct r; exact DJ) Hi).
Qed.

Lemma cn_flags : fs_flags_ok ly rd1 (cgX X c).
Proof.
intros cid pos Hc' Hpos. change (frames (cgX X c)) with (frames X). pose proof (flag_off_bounds cid pos Hc' Hpos) as FB.
change (fs_flags_ok ly rd1 (cgX X c)) with (fs_flags_ok ly rd1 X).
rewrite AGn; [exact (amr_flags _ _ _ _ _ cnM cid pos Hc' Hpos)|].
apply (okn_static 3%nat (ly_F ly, kFakeStackSize)); [left; lia | reflexivity |].
cbn [fst snd]. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.

Lemma cn_depot_ok : depot_ok B ly rd1 (cgX X c).
Proof.
change (depot_ok B ly rd1 (cgX X c)) with (depot_ok B ly rd1 X).
pose proof (amr_depot _ _ _ _ _ cnM) as (heads & links & D1 & D2 & D3).
unfold depot_ok. exists heads, links. split; [|split; [|exact D3]].
- intros b Hb. destruct (D1 b Hb) as [E1 E2]. split; [exact E1|]. intros k Hk.
  rewrite AGn; [exact (E2 k Hk)|]. apply (cn_area_ok (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; unfold d_tab_words in Hb; lia].
- intros id Hid. destruct (D2 id Hid) as (E1 & E2 & E3). split; [exact E1|].
  assert (NB : Z.of_nat (length (st_depot X)) <= 4097).
  { pose proof (depot_len_bound _ _ (amr_universe _ _ _ _ _ cnM) (wfr_depot _ _ _ _ _ cnWF)) as DL. unfold DEPOT_MAX in DL. lia. }
  assert (OR : forall x, ly_NB ly + 16 * id <= x < ly_NB ly + 16 * id + 16 -> rd1 x = rd x).
  { intros x Hx. apply AGn. apply (okn_static 4%nat (ly_NB ly, kNodesBlockSize)); [left; lia | reflexivity |].
    cbn [fst snd]. unfold depot_ids in Hid. unfold kNodesBlockSize. lia. }
  split; intros k Hk; rewrite OR by lia; [exact (E2 k Hk) | exact (E3 k Hk)].
Qed.

Lemma cn_zero : Forall (range_zero B ly rd1) (ialloc_zero B).
Proof.
pose proof (amr_zero _ _ _ _ _ cnM) as Z0. pose proof (aso_ialloc _ cnSY) as [I1 I2].
apply Forall_forall. intros r Hr i Hi.
assert (Ha : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
{ unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
rewrite AGn; [exact (proj1 (Forall_forall _ _) Z0 r Hr i Hi)|].
apply (cn_area_ok (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | exact Ha].
Qed.

Lemma cn_fa_ok : (Z.to_nat c < length (st_regions X))%nat -> fa_entries_ok ly rd1 (cgX X c).
Proof.
intros Hlenr c' i v Hc' Hi Hv. pose proof (amr_fa _ _ _ _ _ cnM) as XF.
assert (ER : rg_free (reg (cgX X c) c') = rg_free (reg X c') /\ rg_mapped_fa (reg X c') <= rg_mapped_fa (reg (cgX X c) c')).
{ destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite (cg_reg_c X c Hc Hlenr). unfold cgr. cbn [rg_free rg_mapped_fa]. split; [reflexivity|]. unfold kFreeArrayMapSize. lia.
  - rewrite (cg_reg_other X c Hc Hlenr c' ltac:(lia) NE). split; [reflexivity | lia]. }
destruct ER as [EF EM]. rewrite EF in Hi, Hv.
pose proof (wfr_classes _ _ _ _ _ cnWF c' Hc') as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
intros k Hk. rewrite AGn; [exact (XF c' i v Hc' Hi Hv k Hk)|].
apply (okn_fa c' i Hc' ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cn_junk : Forall (range_vis B ly rd1) (ajunk_cf B ly (cgX X c)).
Proof.
change (ajunk_cf B ly (cgX X c)) with (ajunk_cf B ly X).
eapply Forall_impl; [|exact (amr_junk _ _ _ _ _ cnM)]. intros r Hr i Hi. exact (VISn _ (Hr i Hi)).
Qed.

Lemma cn_client : Forall (range_vis B ly rd1) (aclient (cgX X c)).
Proof.
change (aclient (cgX X c)) with (aclient X).
eapply Forall_impl; [|exact (amr_client _ _ _ _ _ cnM)]. intros r Hr i Hi. exact (VISn _ (Hr i Hi)).
Qed.

Lemma cn_areas : (Z.to_nat c < length (st_regions X))%nat -> Forall (range_vis B ly rd1) (aareas (cgX X c)).
Proof.
intros Hlenr. pose proof (amr_areas _ _ _ _ _ cnM) as AR. unfold aareas in AR |- *. rewrite !Forall_app in AR |- *.
destruct AR as (A1 & A2 & A3 & A4). split; [|split; [|split]].
- apply Forall_flat_map'. intros c' Hc0. apply zseq_In in Hc0.
  assert (OLD : Forall (range_vis B ly rd) [(ASp (region_off c'), rg_mapped_user (reg X c')); (ASp (region_off c' + kFreeArrayOffset), rg_mapped_fa (reg X c'))])
    by (exact (cn_FMI _ _ c' ltac:(lia) A1)).
  apply Forall_cons_iff in OLD as [O1 OLD]. apply Forall_cons_iff in OLD as [O2 _].
  destruct (Z.eq_dec c' c) as [->|NE].
  + rewrite (cg_reg_c X c Hc Hlenr). unfold cgr. cbn [rg_mapped_user rg_mapped_fa].
    apply Forall_cons; [intros i Hi; exact (VISn _ (O1 i Hi))|]. apply Forall_cons; [|apply Forall_nil].
    intros i Hi. cbn [fst snd aeval] in Hi |- *.
    destruct (Z_lt_le_dec i (rg_mapped_fa (reg X c))) as [L|L]; [exact (VISn _ (O2 i ltac:(cbn [snd]; lia)))|].
    assert (HW : cnwin (ly_space ly + (region_off c + kFreeArrayOffset) + i)).
    { right; right; right; right; right; right; left. unfold fa_base, region_base. unfold kUserMapSize, kFreeArrayMapSize in *. lia. }
    destruct (PRES1 _ HW) as [Hh [bb Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
  + rewrite (cg_reg_other X c Hc Hlenr c' ltac:(lia) NE).
    apply Forall_cons; [intros i Hi; exact (VISn _ (O1 i Hi))|]. apply Forall_cons; [|apply Forall_nil].
    intros i Hi. exact (VISn _ (O2 i Hi)).
- eapply Forall_impl; [|exact A2]. intros r Hr i Hi. exact (VISn _ (Hr i Hi)).
- eapply Forall_impl; [|exact A3]. intros r Hr i Hi. exact (VISn _ (Hr i Hi)).
- eapply Forall_impl; [|exact A4]. intros r Hr i Hi. exact (VISn _ (Hr i Hi)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The record and the relation at the grown state.                                                                  *)
Section G2.
Hypothesis Hlenr : (Z.to_nat c < length (st_regions X))%nat.
(* the cut invariant at the grown state: YGcfInstDrainCg.cg_WfR, discharged where cd_model's growth facts are in
   scope (the F11 assembly) *)
Hypothesis HWFG : WfR_cf (as_universe B) 0 0 0 (cgX X c).
(* the image's constant cells at the intermediate memory (the walk discharges them, as for F12's CONST') *)
Hypothesis CONST1 : Forall (cell_holds B ly rd1) (as_const B ly).
(* the grant's world, model and budget, as the walk's EnsureFreeArraySpace leaf gives them *)
Hypothesis HWA : w_A W3 = (shf, shf + 32768) :: (fadr, fadr + kUserMapSize) :: w_A W.
Hypothesis HVM : vm_maps (m_vmmaps md2) = vm_maps (m_vmmaps md).
Hypothesis HVR : vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps md).
Hypothesis HVL : vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps md).
Hypothesis HVT : alloc_top (m_vmmaps md2) = alloc_top (m_vmmaps md).
Hypothesis HVNA : forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md2)) lo n = true.
Hypothesis HCOV : forall x, ~ (fadr <= x < fadr + kUserMapSize) ->
  YK0g.covered (vm_noaccess (m_vmmaps md2) ++ m_vm_lazy md2) x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Hypothesis HEAG : eager_used md2 <= eager_used md + kUserMapSize.
Hypothesis HAMWF : amwf md2.
(* The free side's ledger at the grant's post, DERIVED (it was a named premise until the layer's abudget_cf carried
   prim_committed / 8, ae2fa80b0325): the grant adds the map and its shadow to the world, 8 * 32768 + 32768 bytes
   (HWA), and raises the committed primary by the map (cg_prim_committed), so YGcfAbudget.ledger_grant_prim_cf at
   q = 32768 carries the pre-state's ledger over. *)
Lemma cn_free_ledger : A_bytes (w_A W3) <= abudget_cf (cgX X c).
Proof.
pose proof (proj1 (proj1 (proj2 (proj2 MR)))) as BU0.
apply (YGcfAbudget.ledger_grant_prim_cf im_segs W W3 X (cgX X c) 32768 BU0).
- rewrite HWA. cbn [A_bytes fst snd]. unfold kUserMapSize. lia.
- rewrite (cg_prim_committed X c Hc Hlenr). reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

(* The relation's two machine cells across the grant (field round 2).  The grant removes one hole, at
   kFreeArrayOffset + mf >= 0, so the exhausted mark (the hole at EXH_HOLE = -1) of every class is unchanged; the
   exhausted byte RG' + cf_exh_off is off the window (okn_rinfo admits RG + 68 for the grown class), and the buffer's
   object is in the image, off the window too (okn_img). *)
Lemma cn_exh_eq : forall c', exh_mem_cf (cgX X c) c' = exh_mem_cf X c'.
Proof.
assert (H : forall c'', 0 <= c'' -> exh_mem_cf (cgX X c) c'' = exh_mem_cf X c'').
{ intros c'' H0. unfold exh_mem_cf. destruct (Z.eq_dec c'' c) as [->|NE].
  - rewrite (cg_reg_c X c Hc Hlenr). unfold cgr. cbn [rg_holes]. unfold del_hole.
    induction (rg_holes (reg X c)) as [|h hs IH]; [reflexivity|]. cbn [filter existsb].
    destruct (fst h =? kFreeArrayOffset + rg_mapped_fa (reg X c)) eqn:E1; cbn [negb orb].
    + apply Z.eqb_eq in E1. pose proof (wrc_fa _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cnWF c ltac:(lia))) as [F0 _].
      replace (fst h =? EXH_HOLE) with false by (symmetry; apply Z.eqb_neq; unfold EXH_HOLE, kFreeArrayOffset in *; lia).
      exact IH.
    + cbn [existsb]. rewrite IH. reflexivity.
  - rewrite (cg_reg_other X c Hc Hlenr c'' H0 NE). reflexivity. }
intros c'. destruct (Z_lt_le_dec c' 0) as [N|N]; [|exact (H c' N)].
assert (E : forall s : astate, reg s c' = reg s 0).
{ intros s. unfold reg, znth. replace (Z.to_nat c') with (Z.to_nat 0) by lia. reflexivity. }
unfold exh_mem_cf. rewrite !E. exact (H 0 ltac:(lia)).
Qed.

Lemma cn_exh : YGcfImgRows.EXH_OFF_t -> exh_cell_cf B ly X rd -> exh_cell_cf B ly (cgX X c) rd1.
Proof.
intros EXO HE. apply (YGcfInstBase.exh_cell_cf_frame B ly ly X (cgX X c) rd rd1 HE cn_exh_eq).
intros c' Hc'. unfold YGcfImgRows.EXH_OFF_t in EXO.
replace (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c')) cf_exh_off))
  with (ly_space ly + kRegionInfoOff + 128 * c' + cf_exh_off) by (cbn; lia).
apply AGn. apply (okn_rinfo c'); [exact Hc' | rewrite EXO; lia |].
intros ->. right; right. rewrite EXO. lia.
Qed.

Lemma cn_errb : errb_obj_owned_t B -> errb_cells_cf B ly X rd -> errb_cells_cf B ly (cgX X c) rd1.
Proof.
intros EOO HEB. apply (YGcfInstBase.errb_cells_cf_frame B ly ly X (cgX X c) rd rd1 HEB); try reflexivity.
- intros a Ha. apply AGn. apply okn_img.
  pose proof (EOO a Ha) as OS. pose proof (amr_static_img _ _ _ _ _ cnM) as SI. apply Exists_exists in OS as (r & Hr & Ha').
  pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_app_iff; left; exact Hr)) as SUB.
  unfold zr_sub, in_zr in *. lia.
- exact VISn.
Qed.

(* Printf's two cells across the step (field round 3): owned static, inside the image. *)
Lemma cn_pf : pf_cells_owned_t B -> pf_cells_cf B ly rd -> pf_cells_cf B ly rd1.
Proof.
intros PO HP. apply (pf_cells_frame_cf B ly rd rd1); [|exact HP].
intros a Ha. apply AGn. apply okn_img.
pose proof (proj1 (proj1 PO a Ha)) as OS. pose proof (amr_static_img _ _ _ _ _ cnM) as SI. apply Exists_exists in OS as (r & Hr & Ha').
pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_app_iff; left; exact Hr)) as SUB.
unfold zr_sub, in_zr in *. lia.
Qed.

Lemma cn_ARmcfR : ARmcfR B ly (cgX X c) Hp rd1.
Proof.
pose proof cnM as M0.
destruct M0 as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor.
- exact HWFG.
- exact Xuni.
- exact Xsyms.
- exact Xlay.
- change (sec_placed ly (cgX X c)) with (sec_placed ly X). exact Xplaced.
- exact CONST1.
- exact Xcowned.
- exact (cn_cells Hlenr).
- exact (cn_fa_ok Hlenr).
- exact cn_flags.
- exact cn_depot_ok.
- exact (cn_shadow Hlenr).
- exact cn_zshadow.
- exact cn_junk.
- exact (cn_areas Hlenr).
- exact cn_client.
- exact cn_zero.
- exact Xtsd.
- exact Ximg.
- change (st_chunks (cgX X c)) with (st_chunks X). exact Xhp.
- change (xs_placed_cf ly (cgX X c)) with (xs_placed_cf ly X). exact Xxs.
- exact (cn_exh (proj1 Xown) Xexh).
- exact (cn_errb (proj1 (proj2 Xown)) Xerrb).
- exact Xown.
- exact (cn_pf Xpfo Xpf).
- exact Xpfo.
Qed.

Lemma cn_ahs : ahs B ly (cgX X c) (w_H W3) mem1.
Proof.
pose proof (proj2 (proj2 (proj2 (proj2 MR)))) as [HP HZ]. unfold ahs_pres, ahz in *. split.
- intros a Hb NC HH. unfold YG0n.w64, YG0d.w64 in *.
  assert (DEC : (shf <= a < shf + 32768) \/ ~ (shf <= a < shf + 32768)) by lia.
  destruct DEC as [IN|OUT].
  + destruct (PRES1 a ltac:(unfold cnwin; tauto)) as [_ [bb Hbb]]. rewrite Hbb. discriminate.
  + assert (OK : okn a) by (apply okn_band; [unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia | exact OUT]).
    destruct OK as [OR NW]. rewrite (MEQ1 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact OR; exact NW).
    apply HP; [exact Hb | exact NC|].
    rewrite <- (HWH (Z_to_bv 64 a)); [exact HH| |]; rewrite unsigned_lit_small by exact OR; [|exact OUT].
    pose proof cn_slot as (S1 & S2 & S3 & _). unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia.
- intros g Hg Ha Hf. unfold YG0n.w64, YG0d.w64 in *. change (hfree ly (cgX X c) g) with (hfree ly X g) in Hf.
  pose proof (HZ g Hg Ha Hf) as Z0.
  assert (NOTNEW : ~ (fadr <= g < fadr + kUserMapSize)).
  { intros Hn. unfold hfree in Hf. rewrite Forall_app in Hf. destruct Hf as [Hf _].
    pose proof (proj1 (Forall_forall _ _) Hf (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
    pose proof cn_slot as (S1 & S2 & _). cbn [fst snd] in D. unfold kUserMapSize in *. lia. }
  assert (BAND : kLowShadowBeg <= shadow_addr g < kHighMemBeg).
  { pose proof (shadow_addr_in_band g 8 0 Ha ltac:(lia)) as IB. rewrite Z.add_0_r in IB.
    unfold in_band_rw in IB. destruct IB as [IB|IB]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia. }
  assert (NS : ~ (shf <= shadow_addr g < shf + 32768)).
  { intros Hs. apply NOTNEW. destruct cn_al8_slot as [q Hq]. unfold shadow_addr in Hs. rewrite Hq in Hs.
    rewrite (Z.mul_comm 8 q), Z_div_mult in Hs by lia.
    pose proof (Z.div_mod g 8 ltac:(lia)) as DM. rewrite Hg, Z.add_0_r in DM. rewrite Hq. unfold kUserMapSize. lia. }
  assert (OK : okn (shadow_addr g)) by (apply okn_band; [exact BAND | exact NS]).
  destruct OK as [OR NW]. rewrite (MEQ1 (Z_to_bv 64 (shadow_addr g))) by (rewrite unsigned_lit_small by exact OR; exact NW).
  exact Z0.
Qed.

Lemma cn_budget : abudget_ok_cf im_segs ly (cgX X c) W3.
Proof.
pose proof (proj1 (proj2 (proj2 MR))) as (BU & SA & BV). split; [exact cn_free_ledger|]. split.
- intros e He. change (sec_extents ly (cgX X c)) with (sec_extents ly X) in He. destruct (SA e He) as [A1 A2].
  rewrite HWA. split; right; right; assumption.
- intros a Ha. unfold YG0n.w64, YG0d.w64 in *. pose proof cn_slot as (S1 & S2 & S3 & _).
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R.
  assert (DEC : (shf <= bv_unsigned (Z_to_bv 64 a) < shf + 32768) \/ ~ (shf <= bv_unsigned (Z_to_bv 64 a) < shf + 32768)) by lia.
  destruct DEC as [IN|OUT].
  + assert (W1 : cnwin (bv_unsigned (Z_to_bv 64 a))) by (unfold cnwin; tauto).
    destruct (PRES1 _ W1) as [Hh _].  rewrite Z_to_bv_bv_unsigned in Hh. exact Hh.
  + rewrite (HWH (Z_to_bv 64 a)); [exact (BV a Ha) | | exact OUT].
    intros Hm.
    pose proof (region_in_prim ly 1 cnLO ltac:(lia)) as (P1 & P2 & _). unfold region_base in P1, P2.
    pose proof cn_prim_hi as [H1 H2].
    assert (APP1 : in_app (region_base ly 1) (kFreeArrayOffset + 8))
      by (unfold in_app, region_base, kFreeArrayOffset, kHighMemBeg in *; split; [lia | right; lia]).
    pose proof (shadow_addr_in_band (region_base ly 1) (kFreeArrayOffset + 8) kFreeArrayOffset APP1 ltac:(unfold kFreeArrayOffset; lia)) as IB.
    pose proof (shadow_addr_in_band (region_base ly 1) (kFreeArrayOffset + 8) 0 APP1 ltac:(unfold kFreeArrayOffset; lia)) as IB0.
    rewrite Z.add_0_r in IB0.
    assert (A0 : 0 <= a < 2 ^ 64)
      by (unfold in_band_rw in IB0, IB; destruct IB0 as [I0|I0]; destruct IB as [I1|I1];
          unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
    rewrite unsigned_lit_small in Hm by exact A0.
    unfold in_band_rw in IB. destruct IB as [I1|I1]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia.
Qed.

Theorem cn_grant_ARcfR : ARcfR im_segs B ly (cgX X c) Hp W3 mem1 md2.
Proof.
split; [exact cn_ARmcfR|]. split.
- exact (ALedger_cf_grant B ly X c md md2 cnLO cnWF Hc Hgrow Hlenr cnLED HVM HVR HVL HVT HVNA
    (amr_placed _ _ _ _ _ cnM) (amr_xs_placed _ _ _ _ _ cnM) HCOV HEAG).
- split; [exact cn_budget|]. split; [exact HAMWF | exact cn_ahs].
Qed.
End G2.

End N.
End U.
