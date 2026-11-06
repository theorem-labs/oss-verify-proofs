(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstHitPost.v (a working branch 3295f3a9fd5f, file sha256 428dd92691d2), lane M's field round 3 on the cf layer of record d0377850faab (round6f), as A11's 3b8046b1e79 / c1f4f4bb81cb; module paths changed only: 62 modules to this unit's lib/Reusable. No other edit; no image numeral is stated here. *)
(* Theorem Labs, 2026-10 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The hit AR link over the cf relation: ARcf at the state a hit leaves (ImgBaseAG.st_final: the popped cache, the
   depot after the put, the new chunk), at the memory the hit walk returns.  The cf twin of
   cgif/cgif_file_fuzzer lib/AGj1.v (file sha256 28e323163a35; donor not released) (AR_transport, the g path) and cgif/cgif_file_fuzzer lib/AGjf.v (file sha256 03c747e676d4; donor not released) (the k path), as ONE transport over the chunk's redzone rz_size n
   and size req_size n: the g path (49 <= n <= 64512, AGif0n.at_RETw) and the k path (0 <= n <= 48,
   AGif0n.at_RETkw) are its two instances (YGcfInstHit.v).
   rule 24: no function proved (interface-instance discharge at a model relation; no machine walk is written).
   Image facts are premises over the class fields only (HIMG, HDZO, HDZX, HFP, HCW below); no numeral of any image;
   no event term. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG ImgBase ImgBaseAG AGif0n YGcfInstHitCore.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot YGcfDIface YGcfInstBase.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2.
Set Default Proof Using "All".

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ================================================================================================================ *)
(* 0. The hit's memory geometry: the new block's shadow (SU), its partial granule (PB), the walk's window (AGif0n's  *)
(*    WIN at redzone rz and size nn) and the set a hit changes (XC).                                                *)
Definition hSU (ly : alayout) (cl v rz : Z) : Z := shadow_addr (ImgBaseAG.Kv ly cl v + rz).
Definition hPB (ly : alayout) (cl v rz nn : Z) : Z := shadow_addr (ImgBaseAG.Kv ly cl v + rz + nn / 8 * 8).
Definition hWIN (ly : alayout) (cl v rz nn sp0 : Z) (odd : bool) (a : Z) : Prop :=
  (sp0 - AFSTACK <= a < sp0) \/ ImgBaseAG.WINT ly cl a \/
  ((ImgBaseAG.Kv ly cl v <= a < ImgBaseAG.Kv ly cl v + 16) \/ (ImgBaseAG.Kv ly cl v + rz - 16 <= a < ImgBaseAG.Kv ly cl v + rz)) \/
  (odd = true /\ hPB ly cl v rz nn <= a < hPB ly cl v rz nn + 1).
Definition hSHX (ly : alayout) (cl v rz nn : Z) (odd : bool) (a : Z) : Prop :=
  (hSU ly cl v rz <= a < hSU ly cl v rz + nn / 8 * 8 / 8) \/ (odd = true /\ hPB ly cl v rz nn <= a < hPB ly cl v rz nn + 1).
Definition hXC (ly : alayout) (cl v rz nn : Z) (odd : bool) (a : Z) : Prop :=
  ImgBaseAG.WINT ly cl a \/ (ImgBaseAG.Kv ly cl v <= a < ImgBaseAG.Kv ly cl v + rz + nn) \/ hSHX ly cl v rz nn odd a \/ ag_dzone ly a.

(* ================================================================================================================ *)
(* 1. Generic helpers.                                                                                              *)
Lemma pairwise_nth_h {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hi Hj Lt; [destruct i; discriminate|].
cbn [pairwise] in P. destruct P as [F P]. destruct i as [|i].
- cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj.
  exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- destruct j as [|j]; [lia|]. cbn in Hi, Hj. exact (IH i j x y P Hi Hj ltac:(lia)).
Qed.

Lemma static_disj_h : forall ly, layout_ok ly -> forall i j x y, nth_error (static_extents ly) i = Some x ->
  nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof.
intros ly LO i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j) as [L|L].
- exact (pairwise_nth_h zdisjoint _ i j x y (lo_disj _ LO) Hi Hj L).
- assert (L' : (j < i)%nat) by lia. pose proof (pairwise_nth_h zdisjoint _ j i y x (lo_disj _ LO) Hj Hi L') as D.
  unfold zdisjoint in *. lia.
Qed.

Lemma unsigned8_h : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.

Lemma val_mem_cell_h : forall B ly H mem e (w : nat) e',
  val_mem im_segs (mrestrict H mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview im_segs H mem) (ACell e w (AV e')).
Proof.
intros B ly H mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite unsigned8_h; [reflexivity|]. first [unfold YO0f.le_byte | unfold YG0f.le_byte]. apply Z.mod_pos_bound. lia.
Qed.

Lemma val_mem_aview_h : forall H mem a v, 0 <= v < 256 -> val_mem im_segs (mrestrict H mem) a 1 v -> aview im_segs H mem a = Some v.
Proof.
intros H mem a v Hv V. unfold aview. pose proof (V 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. rewrite X.
cbn [option_map]. f_equal. rewrite unsigned8_h; [|first [unfold YO0f.le_byte | unfold YG0f.le_byte]; apply Z.mod_pos_bound; lia].
first [unfold YO0f.le_byte | unfold YG0f.le_byte]. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.

(* A cell whose every byte reads as in one of two readers where it holds, holds (decided on the cell's value). *)
Lemma cell_holds_mix_h : forall B ly (rd1 rd2 rd' : reader) c, cell_holds B ly rd1 c -> cell_holds B ly rd2 c ->
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
   ~ ~ (rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k))) ->
  cell_holds B ly rd' c.
Proof.
intros B ly rd1 rd2 rd' c H1 H2 Hm. unfold cell_holds in *. cbv zeta in *. destruct (c_val c) as [e|m vv].
- intros k Hk. specialize (H1 k Hk). specialize (H2 k Hk).
  destruct (rd' (aeval B ly (c_at c) + Z.of_nat k)) as [x|] eqn:E.
  + destruct (Z.eq_dec x (YG0f.le_byte (aeval B ly e) (c_w c) k)) as [->|Ne]; [reflexivity|].
    exfalso. apply (Hm (Z.of_nat k) ltac:(lia)). rewrite E. intros [E1|E2]; [rewrite H1 in E1 | rewrite H2 in E2]; congruence.
  + exfalso. apply (Hm (Z.of_nat k) ltac:(lia)). rewrite E. intros [E1|E2]; [rewrite H1 in E1 | rewrite H2 in E2]; congruence.
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
  pose proof (Hm 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (rd' (aeval B ly (c_at c))) as [x|] eqn:E.
  + destruct (Z.eq_dec (Z.land x m) vv) as [Ex|Ne]; [exists x; split; [reflexivity | exact Ex]|].
    exfalso. apply H0. intros [E1|E2]; [rewrite Hb1 in E1 | rewrite Hb2 in E2]; injection E1 || injection E2; intros; subst; contradiction.
  + exfalso. apply H0. intros [E1|E2]; [rewrite Hb1 in E1 | rewrite Hb2 in E2]; discriminate.
Qed.

Lemma apresent_word_h : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; exact H. Qed.

Lemma apresent_vis_h : forall H mem a, apresent H mem a -> aview im_segs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma zrange_dec_h : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof.
intros lo hi a. destruct (Z_le_dec lo a) as [H1|H1]; [destruct (Z_lt_dec a hi) as [H2|H2]; [left; exact (conj H1 H2) | right; intros [_ H]; exact (H2 H)] | right; intros [H _]; exact (H1 H)].
Qed.

Lemma Forall_flat_map_h {X Y : Type} (P : Y -> Prop) : forall (f : X -> list Y) l,
  (forall x, In x l -> Forall P (f x)) -> Forall P (flat_map f l).
Proof.
intros f l H. apply Forall_forall. intros y Hy. apply in_flat_map in Hy as (x & Hx & Hy). exact (proj1 (Forall_forall _ _) (H x Hx) y Hy).
Qed.

Lemma In_combine_seq_app_h : forall (l0 : list Z) (x : Z) s p, In p (combine (seq s (length l0)) l0) -> In p (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
induction l0 as [|y t IH]; intros x s p H; [destruct H|]. cbn [length combine seq app Nat.add] in *.
destruct H as [H|H]; [left; exact H | right]. apply IH. exact H.
Qed.

Lemma find_chunk_at_app1_h : forall B ly l1 l2 g k, find_chunk_at B ly l1 g = Some k -> find_chunk_at B ly (l1 ++ l2) g = Some k.
Proof.
intros B ly. induction l1 as [|k' t IH]; intros l2 g k H; [discriminate|]. cbn [find_chunk_at app] in *.
destruct (andb _ _); [exact H | exact (IH l2 g k H)].
Qed.
Lemma find_chunk_at_app2_h : forall B ly l1 l2 g, find_chunk_at B ly l1 g = None -> find_chunk_at B ly (l1 ++ l2) g = find_chunk_at B ly l2 g.
Proof.
intros B ly. induction l1 as [|k' t IH]; intros l2 g H; [reflexivity|]. cbn [find_chunk_at app] in *.
destruct (andb _ _); [discriminate | exact (IH l2 g H)].
Qed.

(* The depot's memory facts transfer between two readers that agree on the depot's footprint. *)
Lemma depot_mem_ok_agree_h : forall B ly S' (rd rd' : reader), depot_ids S' <= 4098 ->
  (forall a, CLdepot.depot_footprint B ly a -> rd' a = rd a) -> CLdepot.depot_mem_ok B ly S' rd -> CLdepot.depot_mem_ok B ly S' rd'.
Proof.
intros B ly S' rd rd' HID He (D1' & D2 & D3).
assert (EZ : forall a, (as_depot B <= a < as_depot B + d_map1 + 8) \/ (as_store B <= a < as_store B + 32) \/
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. apply He. unfold CLdepot.depot_footprint, d_map1 in *. lia. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (YG0q.cell_holds_agree B ly rd rd' c); [exact (proj1 (Forall_forall _ _) D1' c Hc)|].
  intros k Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk; unfold d_nuniq, d_map1, s_total, s_block0 in *; lia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
  + intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|]. unfold d_tab_words, d_map1 in *. lia.
  + intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
    * intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. unfold kNodesBlockSize. lia.
    * intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. unfold kNodesBlockSize. lia.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
  cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; unfold d_nuniq, d_map1 in *; lia.
Qed.

(* The depot's memory facts read the model only through its depot. *)
Lemma depot_mem_ok_ext_h : forall B ly S1 S2 (rd : reader), st_depot S1 = st_depot S2 ->
  CLdepot.depot_mem_ok B ly S1 rd -> CLdepot.depot_mem_ok B ly S2 rd.
Proof.
intros B ly S1 S2 rd E (D1 & D2 & D3). split; [|split; [|exact D3]].
- replace (depot_cells ly S2) with (depot_cells ly S1) by (unfold depot_cells, depot_ids, depot_frames; rewrite E; reflexivity). exact D1.
- revert D2. unfold depot_ok, depot_ids, depot_traces. rewrite E. exact (fun H => H).
Qed.

Lemma sh_band_h : forall g, 0 <= g < ASAN_CEIL -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof.
intros g Hg. ceil. unfold shadow_addr. pose proof (Z.div_mod g 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as M1.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ================================================================================================================ *)
(* 2. The transport.                                                                                                *)
Section t.
Variables (B : asyms) (ly : alayout) (S : astate) (Hp : list Z) (W : world im_segs) (mem0 : word -> option byte) (md0 : Model).
Variables (n cl cnt v : Z) (l : list Z) (off : Z).
Hypothesis HAR : ARcf im_segs B ly S Hp W mem0 md0.
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Local Abbreviation vM := (YGcfInstHitCore.vM B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation vL := (YGcfInstHitCore.vL B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation vLY := (YGcfInstHitCore.vLY B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation vWF := (YGcfInstHitCore.vWF B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cl_range := (YGcfInstHitCore.cl_range B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cls_geom := (YGcfInstHitCore.cls_geom B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation off_facts := (YGcfInstHitCore.off_facts B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_base := (YGcfInstHitCore.Kv_base B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_geom := (YGcfInstHitCore.Kv_geom B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hcnt' := (YGcfInstHitCore.Hcnt' B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (YGcfInstHitCore.cached_vs_chunk B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation not_in_head := (YGcfInstHitCore.not_in_head B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow250 := (YGcfInstHitCore.shadow250 B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SK_range := (YGcfInstHitCore.SK_range B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation sh_granule := (YGcfInstHitCore.sh_granule B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow_present := (YGcfInstHitCore.shadow_present B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_present := (YGcfInstHitCore.chunk_present B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_acells_cache := (YGcfInstHitCore.In_acells_cache B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).

Local Notation Kv := (ImgBaseAG.Kv ly cl v).
Local Notation rd0 := (aview im_segs (w_H W) mem0).
Local Notation Kc := (ImgBaseAG.new_chunk cl off n).

(* The unit's image facts, over the class fields and the symbol table. *)
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HDZO : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Hypothesis HDZX : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Hypothesis HFP : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  CLdepot.depot_footprint B ly' a -> ag_dzone ly' a.
Hypothesis HCW : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).

(* The hit's post: the walk's memory at its return, and the model's state after the pop. *)
Variables (tr : list Z) (sp0 : Z) (odd : bool) (z : Z) (mem' memD : word -> option byte) (mat : list word).
Local Notation SF := (ImgBaseAG.st_final S cl l off n tr z).
Local Notation rd' := (aview im_segs (w_H W) mem').
Local Notation rdD := (aview im_segs (w_H W) memD).
Local Notation m' := (mrestrict (w_H W) mem').
Local Notation RZv := (rz_size n).
Local Notation NN := (req_size n).
Local Notation SUv := (hSU ly cl v (rz_size n)).
Local Notation PBv := (hPB ly cl v (rz_size n) (req_size n)).
Local Notation XC := (hXC ly cl v (rz_size n) (req_size n) odd).
Local Notation SHX := (hSHX ly cl v (rz_size n) (req_size n) odd).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis Hodd : odd = true <-> req_size n mod 8 <> 0.
Hypothesis MPwf : Wf_cf (as_universe B) SF.
Hypothesis DEPD : CLdepot.depot_mem_ok B ly (CLdepot.depot_after z tr S) rdD.
Hypothesis CSTD : Forall (cell_holds B ly rdD) (as_const B ly).
Hypothesis PRD : forall a, ag_dzone ly a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a.
Hypothesis EQD : forall x : word, ag_dzone ly (bv_unsigned x) -> mem' x = memD x.
Hypothesis MEQF : forall x : word, ~ hWIN ly cl v RZv NN sp0 odd (bv_unsigned x) -> ~ ag_dzone ly (bv_unsigned x) ->
  ~ (Kv + RZv <= bv_unsigned x < Kv + RZv + NN) -> ~ (SUv <= bv_unsigned x < SUv + NN / 8 * 8 / 8) -> mem' x = mem0 x.
Hypothesis PRS : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a.
Hypothesis PRW : forall a, ImgBaseAG.WINT ly cl a \/ (Kv <= a < Kv + RZv + NN) \/ (odd = true /\ PBv <= a < PBv + 1) -> apresent (w_H W) mem' a.
Hypothesis HVMG : RZv <> 16 -> val_mem im_segs m' Kv 8 0xCC6E96B9CC6E96B9 /\ val_mem im_segs m' (Kv + 8) 8 (Kv + RZv - 16).
Hypothesis HV3 : val_mem im_segs m' (Kv + RZv - 16) 1 2.
Hypothesis HV4 : exists b, val_mem im_segs m' (Kv + RZv - 15) 1 b /\ 0 <= b < 256 /\ Z.land b 127 = 17.
Hypothesis HV5 : val_mem im_segs m' (Kv + RZv - 14) 2 0.
Hypothesis HV6 : val_mem im_segs m' (Kv + RZv - 12) 4 NN.
Hypothesis HV7 : val_mem im_segs m' (ImgBaseAG.Pv ly cl) 4 (cnt - 1).
Hypothesis HV8 : val_mem im_segs m' (ly_T ly + t_unwinding) 1 0.
Hypothesis HV9 : forall x : word, SUv <= bv_unsigned x < SUv + NN / 8 * 8 / 8 -> mem' x = Some (Z_to_bv 8 0).
Hypothesis HV10 : odd = true -> val_mem im_segs m' PBv 1 (NN mod 8).

(* ---- geometry ---- *)
Lemma t_geom : 16 <= RZv <= 2048 /\ RZv mod 16 = 0 /\ 1 <= NN /\ n <= NN /\ RZv + NN <= class_size cl.
Proof.
pose proof (rz_size_bounds n) as [R1 R2]. pose proof (req_size_bounds n Hn0) as (Q1 & Q2 & Q3).
pose proof (primary_geometry n Hn0 FP) as (_ & [G1 G2] & _). rewrite <- Hcl_class in G2. lia.
Qed.

Lemma t_div : RZv = 8 * (RZv / 8) /\ 8 * (NN / 8) <= NN < 8 * (NN / 8) + 8 /\ class_size cl = 8 * (class_size cl / 8) /\
  NN / 8 * 8 = 8 * (NN / 8) /\ NN / 8 * 8 / 8 = NN / 8 /\ (NN mod 8 <> 0 -> 8 * (NN / 8) < NN).
Proof.
pose proof t_geom as (T1 & T2 & T3 & T4 & T5). pose proof cls_geom as (K1 & K2 & _).
pose proof (Z.div_mod RZv 8 ltac:(lia)) as D1. pose proof (Z.div_mod NN 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound NN 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (class_size cl) 8 ltac:(lia)) as D3.
assert (E1 : RZv mod 8 = 0) by (apply Z.mod_divide in T2 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z_mod_mult).
assert (E3 : class_size cl mod 8 = 0) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; rewrite Hq; replace (q * 32) with ((4 * q) * 8) by lia; apply Z_mod_mult).
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply Z.div_mul; lia|]. intros H. lia.
Qed.

Lemma SU_eq : SUv = shadow_addr Kv + RZv / 8.
Proof. pose proof t_div as (D1 & _). unfold hSU. rewrite D1 at 1. rewrite sh_granule. reflexivity. Qed.

Lemma PB_eq : PBv = shadow_addr Kv + RZv / 8 + NN / 8.
Proof.
pose proof t_div as (D1 & D2 & D3 & D4 & _). unfold hPB.
replace (Kv + RZv + NN / 8 * 8) with (Kv + 8 * (RZv / 8 + NN / 8)) by lia. rewrite sh_granule. lia.
Qed.

Lemma SHX_where : forall a, SHX a -> shadow_addr Kv + RZv / 8 <= a < shadow_addr Kv + class_size cl / 8 /\ 2 <= RZv / 8.
Proof.
intros a Hs. pose proof t_geom as (T1 & T2 & T3 & T4 & T5). pose proof t_div as (D1 & D2 & D3 & D4 & D5 & D6).
unfold hSHX in Hs. rewrite SU_eq, PB_eq, D5 in Hs. destruct Hs as [Hs|[Ho Hs]]; [lia|].
apply Hodd in Ho. pose proof (D6 Ho). lia.
Qed.

(* A granule's shadow is in the cached chunk's shadow only for a granule of the chunk. *)
Lemma sh_in_chunk : forall g, g mod 8 = 0 -> shadow_addr Kv <= shadow_addr g < shadow_addr Kv + class_size cl / 8 -> Kv <= g < Kv + class_size cl.
Proof.
intros g Hg Hs. pose proof Kv_geom as (V1 & V2 & V3 & _). pose proof t_div as (_ & _ & D3 & _).
unfold shadow_addr in Hs. pose proof (Z.div_mod g 8 ltac:(lia)) as DG. pose proof (Z.div_mod Kv 8 ltac:(lia)) as DK.
assert (K8 : Kv mod 8 = 0) by (apply Z.mod_divide in V3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z_mod_mult).
lia.
Qed.

Lemma Kc_facts : ck_base B ly Kc = Kv /\ ck_rz Kc = RZv /\ ck_n Kc = NN /\ ck_extent Kc = class_size cl /\
  ck_state Kc = CAllocated /\ ck_beg Kc = PPrim (region_off cl + off) /\ aeval B ly (sptr_exp (ck_beg Kc)) = Kv.
Proof.
pose proof cl_range as CR.
assert (EK : aeval B ly (sptr_exp (PPrim (region_off cl + off))) = Kv) by (cbn; unfold ImgBaseAG.Kv; rewrite region_off_eq by lia; lia).
unfold ImgBaseAG.new_chunk, ck_base, ck_rz, ck_n, ck_extent, sptr_addr. cbn [ck_beg ck_req ck_state]. rewrite FP, <- Hcl_class, EK.
repeat split; reflexivity.
Qed.

Lemma Kc_user : sptr_addr B ly (ck_user Kc) = Kv + RZv /\ aeval B ly (sptr_exp (ck_user Kc)) = Kv + RZv.
Proof.
pose proof Kc_facts as (_ & KR & _ & _ & _ & KB & KA).
unfold ck_user, sptr_addr. rewrite KR, KB. rewrite KB in KA. cbn [padd sptr_exp aeval]. cbn [sptr_exp aeval] in KA. split; lia.
Qed.

(* ---- the state after the hit ---- *)
Lemma Kc_fresh : forall k, In k (st_chunks S) -> sptr_eqb (ck_beg k) (ck_beg Kc) = false.
Proof.
intros k Hk. pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & _). pose proof cl_range as CR. pose proof cls_geom as (K1 & _).
destruct (sptr_eqb (ck_beg k) (ck_beg Kc)) eqn:E; [|reflexivity]. exfalso.
unfold ImgBaseAG.new_chunk in E. cbn [ck_beg] in E. destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; cbn in E; try discriminate.
apply Z.eqb_eq in E. apply NI. apply in_or_app. right. apply in_or_app. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. rewrite E in IN.
replace (prim_class (region_off cl + off)) with cl in IN.
2:{ unfold prim_class. rewrite region_off_eq by lia. rewrite Z.shiftr_div_pow2 by lia. unfold kFreeArrayOffset in O5.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
rewrite region_off_eq in IN by lia. replace (cl * 2 ^ 32 + off - cl * 2 ^ 32) with off in IN by lia. exact IN.
Qed.

Lemma upd_chunk_fresh_h : forall lst, (forall k, In k lst -> sptr_eqb (ck_beg k) (ck_beg Kc) = false) -> upd_chunk lst Kc = lst ++ [Kc].
Proof.
induction lst as [|k t IH]; intros H; [reflexivity|]. cbn [upd_chunk app]. rewrite (H k (or_introl eq_refl)). f_equal. apply IH.
intros k' Hk'. apply H. right. exact Hk'.
Qed.

Lemma SF_chunks : st_chunks SF = st_chunks S ++ [Kc].
Proof.
unfold ImgBaseAG.st_final. cbn [st_chunks set_chunks].
replace (st_chunks (ImgBaseAG.depot_after z tr (ImgBaseAG.st_popped S cl l))) with (st_chunks S).
- apply upd_chunk_fresh_h. exact Kc_fresh.
- unfold ImgBaseAG.depot_after, ImgBaseAG.st_popped. destruct (z =? 0); reflexivity.
Qed.

Lemma SF_same :
st_regions SF = st_regions S /\ st_cache_inited SF = st_cache_inited S /\ st_secs SF = st_secs S /\
st_sec_arr SF = st_sec_arr S /\ st_sec_reserved SF = st_sec_reserved S /\ st_qthread SF = st_qthread S /\
st_qglobal SF = st_qglobal S /\ st_fs SF = st_fs S /\ st_internal_inited SF = st_internal_inited S /\
st_cache SF = zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S) /\
st_depot SF = st_depot (CLdepot.depot_after z tr S).
Proof. unfold ImgBaseAG.st_final, ImgBaseAG.depot_after, CLdepot.depot_after, ImgBaseAG.st_popped. destruct (z =? 0); cbn; repeat split; reflexivity. Qed.

Lemma SF_parts :
(forall c, reg SF c = reg S c) /\ (forall c, 0 <= c -> c <> cl -> cache SF c = cache S c) /\
cache SF cl = mkPC (pc_max (cache S cl)) l /\ frames SF = frames S /\
sec_extents ly SF = sec_extents ly S /\ xs_cf ly SF = xs_cf ly S.
Proof.
pose proof SF_same as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rcache & Rdep). pose proof cl_range as CR.
split; [intros c; unfold reg; rewrite Rregs; reflexivity|].
split; [intros c Hc Hne; unfold cache; rewrite Rcache; apply znth_zupd_other; [lia | exact Hc | congruence]|].
split; [unfold cache at 1; rewrite Rcache; apply znth_zupd_same; [lia|]; rewrite (wfc_len_cache _ _ _ _ _ vWF); lia|].
split; [unfold frames; rewrite Rfs; reflexivity|].
split; [unfold sec_extents; rewrite SF_chunks, flat_map_app; cbn [flat_map ck_beg ImgBaseAG.new_chunk]; rewrite app_nil_r; reflexivity|].
unfold xs_cf, errb_cap_cf, errb_e. rewrite Rsecs. reflexivity.
Qed.

(* ---- the layout's separation facts ---- *)
Lemma sx : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. exact (static_disj_h ly vLY). Qed.

Lemma ext_apart : forall i e a, nth_error (static_extents ly) i = Some e -> in_zr a e ->
  forall j e', nth_error (static_extents ly) j = Some e' -> i <> j -> ~ in_zr a e'.
Proof. intros i e a Hi Ha j e' Hj Hne Ha'. pose proof (sx i j e e' Hi Hj Hne) as D. unfold zdisjoint, in_zr in *. lia. Qed.

Lemma oapp : forall e, In e (owned_extents ly) -> in_app (fst e) (snd e).
Proof. exact (proj1 (Forall_forall _ _) (lo_app _ vLY)). Qed.

Lemma app_not_band : forall lo len a, in_app lo len -> lo <= a < lo + len -> ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof. intros lo len a [H0 H1] Ha Hb. unfold kLowShadowBeg, kHighMemBeg in *. lia. Qed.

Lemma WINT_T : forall a, ImgBaseAG.WINT ly cl a -> ly_T ly <= a < ly_T ly + kThreadObjSize.
Proof. intros a Hw. pose proof cl_range. unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold kThreadObjSize, t_cache, t_stats, t_unwinding in *. lia. Qed.

Lemma DZ_loc : forall a, ag_dzone ly a -> in_zr a (ly_img ly) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros a Hd. destruct (HDZO ly a Hd) as [Hs|[Hs|Hs]]; [left | right; left; exact Hs | right; right; exact Hs].
apply Exists_exists in Hs as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ vM) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
unfold in_zr. lia.
Qed.

Lemma area_img : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ vM)) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [S1 S2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ vM) r' ltac:(apply in_app_iff; left; exact Hr')) as [Z1 Z2].
unfold in_zr. lia.
Qed.

Lemma img_low : forall a, in_zr a (ly_img ly) -> kImgLo <= a < kImgEnd.
Proof. intros a Ha. pose proof (lo_img _ vLY) as (I1 & I2 & I3 & _). unfold in_zr in Ha. lia. Qed.

(* ---- what the hit changes, and where it lies ---- *)
Lemma not_XC : forall a, ~ ImgBaseAG.WINT ly cl a -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) ->
  ~ (kLowShadowBeg <= a < kHighMemBeg) -> ~ ag_dzone ly a -> ~ XC a.
Proof.
intros a NW NP NB ND Hx. unfold hXC in Hx. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & V6). pose proof t_geom as (T1 & T2 & T3 & T4 & T5).
destruct Hx as [Hw|[Hb|[Hs|Hd]]]; [exact (NW Hw) | apply NP; lia | | exact (ND Hd)].
apply SHX_where in Hs. pose proof SK_range as (SK1 & SK2 & SK3). apply NB. unfold kHighShadowBeg, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma DZ_apart : forall a, ~ in_zr a (ly_img ly) -> ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) ->
  ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> ~ ag_dzone ly a.
Proof. intros a N1 N2 N3 Hd. destruct (DZ_loc a Hd) as [H|[H|H]]; auto. Qed.

(* An owned extent other than the primary, the thread object and the depot blocks (index i of static_extents). *)
Lemma Z_ext : forall (i : nat) e a, nth_error (static_extents ly) i = Some e -> In e (owned_extents ly) ->
  (i = 1 \/ i = 3 \/ i = 6 \/ i = 7)%nat -> in_zr a e -> ~ XC a.
Proof.
intros i e a Hi Hin Hix Ha. apply not_XC.
- intros Hw. apply (ext_apart i e a Hi Ha 2 (ly_T ly, kThreadObjSize) eq_refl ltac:(lia)). exact (WINT_T a Hw).
- exact (ext_apart i e a Hi Ha 0 (ly_prim ly, kPrimResvSize) eq_refl ltac:(lia)).
- exact (app_not_band (fst e) (snd e) a (oapp e Hin) Ha).
- apply DZ_apart; [exact (ext_apart i e a Hi Ha 9 (ly_img ly) eq_refl ltac:(lia)) | exact (ext_apart i e a Hi Ha 4 (ly_NB ly, kNodesBlockSize) eq_refl ltac:(lia)) | exact (ext_apart i e a Hi Ha 5 (ly_SB ly, kStoreBlockSize) eq_refl ltac:(lia))].
Qed.

Lemma Z_Q : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> ~ XC a.
Proof. intros a Ha. apply (Z_ext 1 (ly_Q ly, kPtrArrayResv) a eq_refl ltac:(unfold owned_extents; cbn; tauto) ltac:(lia) Ha). Qed.
Lemma Z_F : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> ~ XC a.
Proof. intros a Ha. apply (Z_ext 3 (ly_F ly, kFakeStackSize) a eq_refl ltac:(unfold owned_extents; cbn; tauto) ltac:(lia) Ha). Qed.
Lemma Z_C : forall a, ly_C ly <= a < ly_C ly + 256 -> ~ XC a.
Proof. intros a Ha. apply (Z_ext 6 (ly_C ly, 256) a eq_refl ltac:(unfold owned_extents; cbn; tauto) ltac:(lia) Ha). Qed.
Lemma Z_D : forall a, ly_D ly <= a < ly_D ly + 4096 -> ~ XC a.
Proof. intros a Ha. apply (Z_ext 7 (ly_D ly, 4096) a eq_refl ltac:(unfold owned_extents; cbn; tauto) ltac:(lia) Ha). Qed.

Lemma Z_T : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> ~ ImgBaseAG.WINT ly cl a -> ~ XC a.
Proof.
intros a Ha NW. apply not_XC; [exact NW | | |].
- exact (ext_apart 2 (ly_T ly, kThreadObjSize) a eq_refl Ha 0 (ly_prim ly, kPrimResvSize) eq_refl ltac:(lia)).
- exact (app_not_band (ly_T ly) kThreadObjSize a (oapp (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) Ha).
- apply DZ_apart; [exact (ext_apart 2 (ly_T ly, kThreadObjSize) a eq_refl Ha 9 (ly_img ly) eq_refl ltac:(lia)) |
  exact (ext_apart 2 (ly_T ly, kThreadObjSize) a eq_refl Ha 4 (ly_NB ly, kNodesBlockSize) eq_refl ltac:(lia)) |
  exact (ext_apart 2 (ly_T ly, kThreadObjSize) a eq_refl Ha 5 (ly_SB ly, kStoreBlockSize) eq_refl ltac:(lia))].
Qed.

Lemma Z_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> ~ ag_dzone ly a -> ~ XC a.
Proof.
intros a Ha ND. apply not_XC; [| | |exact ND].
- intros Hw. apply (ext_apart 4 (ly_NB ly, kNodesBlockSize) a eq_refl Ha 2 (ly_T ly, kThreadObjSize) eq_refl ltac:(lia)). exact (WINT_T a Hw).
- exact (ext_apart 4 (ly_NB ly, kNodesBlockSize) a eq_refl Ha 0 (ly_prim ly, kPrimResvSize) eq_refl ltac:(lia)).
- exact (app_not_band (ly_NB ly) kNodesBlockSize a (oapp (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) Ha).
Qed.
Lemma Z_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> ~ ag_dzone ly a -> ~ XC a.
Proof.
intros a Ha ND. apply not_XC; [| | |exact ND].
- intros Hw. apply (ext_apart 5 (ly_SB ly, kStoreBlockSize) a eq_refl Ha 2 (ly_T ly, kThreadObjSize) eq_refl ltac:(lia)). exact (WINT_T a Hw).
- exact (ext_apart 5 (ly_SB ly, kStoreBlockSize) a eq_refl Ha 0 (ly_prim ly, kPrimResvSize) eq_refl ltac:(lia)).
- exact (app_not_band (ly_SB ly) kStoreBlockSize a (oapp (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) Ha).
Qed.

Lemma Z_img : forall a, in_zr a (ly_img ly) -> ~ ag_dzone ly a -> ~ XC a.
Proof.
intros a Ha ND. pose proof (img_low a Ha) as IL. apply not_XC; [| | |exact ND].
- intros Hw. apply (ext_apart 9 (ly_img ly) a eq_refl Ha 2 (ly_T ly, kThreadObjSize) eq_refl ltac:(lia)). exact (WINT_T a Hw).
- exact (ext_apart 9 (ly_img ly) a eq_refl Ha 0 (ly_prim ly, kPrimResvSize) eq_refl ltac:(lia)).
- unfold kImgLo, kImgEnd, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (Kv <= a < Kv + class_size cl) -> ~ XC a.
Proof.
intros a Ha NK Hx. unfold hXC in Hx. pose proof t_geom as (T1 & T2 & T3 & T4 & T5).
destruct Hx as [Hw|[Hb|[Hs|Hd]]].
- apply (ext_apart 0 (ly_prim ly, kPrimResvSize) a eq_refl Ha 2 (ly_T ly, kThreadObjSize) eq_refl ltac:(lia)). exact (WINT_T a Hw).
- apply NK. lia.
- apply SHX_where in Hs. pose proof SK_range as (SK1 & SK2 & SK3). pose proof (lo_high _ vLY) as [H1 _].
  unfold kHighMemBeg in *. lia.
- destruct (DZ_loc a Hd) as [H|[H|H]].
  + exact (ext_apart 0 (ly_prim ly, kPrimResvSize) a eq_refl Ha 9 (ly_img ly) eq_refl ltac:(lia) H).
  + exact (ext_apart 0 (ly_prim ly, kPrimResvSize) a eq_refl Ha 4 (ly_NB ly, kNodesBlockSize) eq_refl ltac:(lia) H).
  + exact (ext_apart 0 (ly_prim ly, kPrimResvSize) a eq_refl Ha 5 (ly_SB ly, kStoreBlockSize) eq_refl ltac:(lia) H).
Qed.

Lemma Z_sec : forall e a, In e (sec_extents ly S) -> in_zr a e -> ~ XC a.
Proof.
intros e a He Ha. pose proof (amc_placed _ _ _ _ _ vM) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (static_extents ly) -> ~ in_zr a e').
{ intros e' He' Ha'. pose proof (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He He') as X.
  unfold zdisjoint, in_zr in *. lia. }
apply not_XC.
- intros Hw. apply (D (ly_T ly, kThreadObjSize)); [unfold static_extents, owned_extents; cbn; tauto | exact (WINT_T a Hw)].
- exact (D (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)).
- exact (app_not_band (fst e) (snd e) a HIA Ha).
- apply DZ_apart; [exact (D (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) |
  exact (D (ly_NB ly, kNodesBlockSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) |
  exact (D (ly_SB ly, kStoreBlockSize) ltac:(unfold static_extents, owned_extents; cbn; tauto))].
Qed.

Lemma Z_band : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ SHX a -> ~ XC a.
Proof.
intros a Ha NS Hx. unfold hXC in Hx. pose proof Kv_geom as (V1 & _).
destruct Hx as [Hw|[Hb|[Hs|Hd]]].
- exact (app_not_band (ly_T ly) kThreadObjSize a (oapp (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) (WINT_T a Hw) Ha).
- unfold kHighMemBeg in *. lia.
- exact (NS Hs).
- destruct (DZ_loc a Hd) as [H|[H|H]].
  + pose proof (img_low a H). unfold kImgEnd, kLowShadowBeg in *. lia.
  + exact (app_not_band (ly_NB ly) kNodesBlockSize a (oapp (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) H Ha).
  + exact (app_not_band (ly_SB ly) kStoreBlockSize a (oapp (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) H Ha).
Qed.

(* ---- the memory frame ---- *)
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR Ho) as Ra.
pose proof (AR_stack_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR) as NS.
assert (R64 : 0 <= a < 2 ^ 64) by (ceil; lia).
unfold hXC, hSHX in Hx. pose proof t_geom as TG.
apply aview_same_h. apply MEQF; rewrite unsigned_lit_small by exact R64.
- intros Hw. unfold hWIN in Hw. destruct Hw as [Hs|[Hw|[Hk|Ho']]].
  + apply NS; [destruct Hsp as [S1 S2]; unfold AFSTACK in *; lia | exact Ho].
  + apply Hx. left. exact Hw.
  + apply Hx. right; left. lia.
  + apply Hx. right; right; left. right. exact Ho'.
- intros Hd. apply Hx. right; right; right. exact Hd.
- intros Hk. apply Hx. right; left. lia.
- intros Hs. apply Hx. right; right; left. left. exact Hs.
Qed.

Lemma PRES_MONO : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem' a.
Proof.
assert (G : forall u, 0 <= u < 2 ^ 64 -> apresent (w_H W) mem0 u -> apresent (w_H W) mem' u).
{ intros u Ru Hp0. destruct Hp0 as [Hh [b Hb]]. split; [exact Hh|].
  destruct (mem' (Z_to_bv 64 u)) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  assert (NP : ~ apresent (w_H W) mem' u) by (intros [_ [b'' Hb'']]; rewrite E in Hb''; discriminate).
  destruct (zrange_dec_h (sp0 - AFSTACK) sp0 u) as [D1|D1]; [exact (NP (PRS u D1))|].
  destruct (zrange_dec_h SUv (SUv + NN / 8 * 8 / 8) u) as [D2|D2].
  { rewrite (HV9 (Z_to_bv 64 u)) in E; [discriminate | rewrite unsigned_lit_small by exact Ru; exact D2]. }
  assert (NW : ~ ImgBaseAG.WINT ly cl u) by (intros Hw; exact (NP (PRW u (or_introl Hw)))).
  assert (NK : ~ (Kv <= u < Kv + RZv + NN)) by (intros Hk; exact (NP (PRW u (or_intror (or_introl Hk))))).
  assert (NPB : ~ (odd = true /\ PBv <= u < PBv + 1)) by (intros Ho; exact (NP (PRW u (or_intror (or_intror Ho))))).
  assert (ND : ~ ag_dzone ly u).
  { intros Hd. destruct (PRD u Hd (conj Hh (ex_intro _ b Hb))) as [_ [bD HbD]].
    rewrite EQD in E by (rewrite unsigned_lit_small by exact Ru; exact Hd). rewrite HbD in E. discriminate. }
  pose proof t_geom as TG.
  assert (EM : mem' (Z_to_bv 64 u) = mem0 (Z_to_bv 64 u)).
  { apply MEQF; rewrite unsigned_lit_small by exact Ru.
    - unfold hWIN. intros [Hs|[Hw|[Hk|Ho]]]; [exact (D1 Hs) | exact (NW Hw) | apply NK; lia | exact (NPB Ho)].
    - exact ND.
    - intros Hk. apply NK. lia.
    - exact D2. }
  rewrite E, Hb in EM. discriminate. }
intros a Hp0. apply (proj2 (apresent_word_h _ _ a)).
apply G; [pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R|].
apply (proj1 (apresent_word_h _ _ a)). exact Hp0.
Qed.

Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a HV. unfold aview, mbyte in *.
destruct (seg_rom im_segs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H W) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp0 : apresent (w_H W) mem0 a).
  { unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [exfalso; apply HV; reflexivity|].
    split; [reflexivity|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply HV; reflexivity]. }
  destruct (PRES_MONO a Hp0) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

Lemma Kext_vis : forall a, Kv <= a < Kv + class_size cl -> rd' a <> None.
Proof. intros a Ha. apply VIS_MONO. apply apresent_vis_h. exact (chunk_present a Ha). Qed.

Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.

Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells_cf B ly S) ->
  Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) lst ->
  Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) RNG c Hc) as [R1 R2]. cbv beta in R1, R2.
apply (YG0q.cell_holds_agree B ly rd0 rd' c); [exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ vM) c (INC c Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned_cf B ly S Hp _ vM) c (INC c Hc) k Hk).
- apply LOC. lia.
Qed.

Lemma keep_cell : forall c lo len, loc_ok lo len -> In c (acells_cf B ly S) ->
  lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_holds B ly rd' c.
Proof.
intros c lo len LOC Hc R1 R2.
exact (proj1 (Forall_forall _ _) (keep_cells [c] lo len LOC ltac:(intros x [<-|[]]; exact Hc) ltac:(constructor; [split; assumption | constructor])) c (or_introl eq_refl)).
Qed.

(* The instance object and the internal allocator's cells are in the image and off the depot zone. *)
Lemma LOC_inst : loc_ok (as_inst B) 3632.
Proof.
intros a Ha. apply Z_img; [apply (area_img (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | exact Ha] |].
intros Hd. exact (proj1 (HDZX ly a vLY (HIMG ly S md0 vL) Hd) Ha).
Qed.
Lemma LOC_ial : loc_ok (as_ialloc_lo B) (as_ialloc_hi B - as_ialloc_lo B).
Proof.
intros a Ha. apply Z_img; [apply (area_img (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia] |].
intros Hd. apply (proj1 (proj2 (HDZX ly a vLY (HIMG ly S md0 vL) Hd))). lia.
Qed.
Lemma LOC_flag : loc_ok (as_ialloc_flag B) 2.
Proof.
intros a Ha. apply Z_img; [apply (area_img (as_ialloc_flag B, 2)); [unfold asyms_areas; cbn; tauto | exact Ha] |].
intros Hd. exact (proj2 (proj2 (HDZX ly a vLY (HIMG ly S md0 vL) Hd)) Ha).
Qed.

Local Abbreviation Hcl' := (YGcfInstHitCore.Hcl' B ly S Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def).

Lemma val_mem_eq_h : forall m a a' (w : nat) x x', a = a' -> x = x' -> val_mem im_segs m a' w x' -> val_mem im_segs m a w x.
Proof. intros m a a' w x x' -> -> H. exact H. Qed.

Lemma cell_vis : forall c k, In c (acells_cf B ly S) -> (exists e, c_val c = AV e) -> (k < c_w c)%nat -> rd0 (aeval B ly (c_at c) + Z.of_nat k) <> None.
Proof.
intros c k Hc [e He] Hk. pose proof (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ vM) c Hc) as CH. unfold cell_holds in CH. cbv zeta in CH. rewrite He in CH.
rewrite (CH k Hk). discriminate.
Qed.

(* ---- the cells ---- *)
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf SF) (zseq 1 31)).
Proof.
pose proof SF_parts as (Rreg & _). apply Forall_flat_map_h. intros c Hc. apply YG0q.zseq_In in Hc.
replace (region_cells_cf SF c) with (region_cells_cf S c) by (unfold region_cells_cf, region_cells; rewrite Rreg; reflexivity).
pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & V6). pose proof cl_range as CR. pose proof (lo_space_in _ vLY) as [SP1 SP2].
apply (keep_cells _ (ly_space ly + kRegionInfoOff) 4096).
- intros a Ha. apply Z_prim; [unfold kRegionInfoOff, kSpaceSize in *; lia|].
  unfold region_base in V6. rewrite region_off_eq in V6 by lia. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
- intros x Hx. unfold acells_cf. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply YG0s.In_zseq; lia | exact Hx].
- unfold region_cells_cf, region_cells, kRegionInfoOff. cbn [removelast].
  repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SF) (zseq 1 31)).
Proof.
pose proof SF_parts as (_ & Rother & Rcl & _). pose proof SF_same as (_ & Rinit & _). pose proof cl_range as CR.
apply Forall_flat_map_h. intros c Hc. apply YG0q.zseq_In in Hc.
destruct (Z.eq_dec c cl) as [->|Hne].
- unfold cache_cells. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks pc_max].
  assert (INC : forall x, In x (cache_cells S cl) -> In x (acells_cf B ly S)) by exact In_acells_cache.
  unfold cache_cells in INC. rewrite Hinited, Hcache in INC.
  assert (LOC : loc_ok (ImgBaseAG.Pv ly cl + 4) 76).
  { intros a Ha. apply Z_T; [unfold ImgBaseAG.Pv in *; unfold t_cache, kThreadObjSize in *; lia|].
    intros Hw. unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in *. unfold t_cache, t_stats, t_unwinding in *. lia. }
  pose proof off_facts as (_ & _ & _ & _ & _ & _ & CNt & CN & _).
  constructor.
  { apply val_mem_cell_h. apply (val_mem_eq_h _ _ (ImgBaseAG.Pv ly cl) _ _ (cnt - 1)); [cbn; unfold ImgBaseAG.Pv; lia | cbn; lia | exact HV7]. }
  constructor. { apply (keep_cell _ (ImgBaseAG.Pv ly cl + 4) 76 LOC); [apply INC; right; left; reflexivity | cbn; unfold ImgBaseAG.Pv; lia | cbn; unfold ImgBaseAG.Pv; lia]. }
  constructor. { apply (keep_cell _ (ImgBaseAG.Pv ly cl + 4) 76 LOC); [apply INC; right; right; left; reflexivity | cbn; unfold ImgBaseAG.Pv; lia | cbn; unfold ImgBaseAG.Pv; lia]. }
  apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
  pose proof Hiv as Hi. apply in_combine_l in Hi. apply in_seq in Hi.
  apply (keep_cell _ (ImgBaseAG.Pv ly cl + 4) 76 LOC).
  + apply INC. right; right; right. apply in_map_iff. exists (i, vv). split; [reflexivity|].
    rewrite length_app. cbn [length]. apply In_combine_seq_app_h. exact Hiv.
  + cbn. unfold ImgBaseAG.Pv. lia.
  + cbn. unfold ImgBaseAG.Pv. lia.
- replace (cache_cells SF c) with (cache_cells S c) by (unfold cache_cells; rewrite Rinit, (Rother c) by lia; reflexivity).
  apply (keep_cells _ (ly_T ly + t_cache + 80 * c) 80).
  + intros a Ha. apply Z_T; [unfold t_cache, kThreadObjSize in *; lia|].
    intros Hw. unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in *. unfold t_cache, t_stats, t_unwinding in *. lia.
  + intros x Hx. unfold acells_cf. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply YG0s.In_zseq; lia | exact Hx].
  + unfold cache_cells. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ vWF c ltac:(lia))) as WC.
    pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
    destruct (st_cache_inited S).
    * destruct WC as [PM PL]. unfold t_cache. repeat (apply Forall_cons; [cbn; lia|]).
      apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv). apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
    * unfold t_cache. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks SF)).
Proof.
rewrite SF_chunks, flat_map_app. apply Forall_app. split.
- apply Forall_flat_map_h. intros k Hk.
  pose proof (chunk_facts_cf B ly S Hp _ k vM Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
  apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
  + intros a Ha. destruct (extent_zone_cf B ly S Hp _ k vM Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
    * apply Z_prim; [lia|]. intros HK. pose proof (cached_vs_chunk k Hk) as D. lia.
    * apply (Z_sec (m, len)); [exact Hin | unfold in_zr; cbn [fst snd]; unfold kPage in *; lia].
  + intros x Hx. unfold acells_cf. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. split; [exact Hk | exact Hx].
  + assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
    { intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
    assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
    { intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
    assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
    clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
    * repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
    * destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
      assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
      repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- cbn [flat_map]. rewrite app_nil_r. pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). pose proof t_geom as (T1 & T2 & T3 & T4 & T5).
  rewrite KBEG in KA. cbn [sptr_exp aeval] in KA.
  unfold chunk_cells, hdr_state. rewrite KR, KN, KS, KBEG. unfold kChunkHeaderSize.
  apply Forall_app. split.
  + constructor. { apply val_mem_cell_h. apply (val_mem_eq_h _ _ (Kv + RZv - 16) _ _ 2); [cbn [aeval aoff sptr_exp]; lia | reflexivity | exact HV3]. }
    constructor.
    { cbn [cell_holds c_at c_val c_w]. destruct HV4 as (b & Vb & Hb & Hm). exists b. split; [|exact Hm].
      replace (aeval B ly (aoff (aoff (sptr_exp (PPrim (region_off cl + off))) (rz_size n - 16)) 1)) with (Kv + RZv - 15) by (cbn [aeval aoff sptr_exp]; lia).
      exact (val_mem_aview_h _ _ _ _ Hb Vb). }
    constructor. { apply val_mem_cell_h. apply (val_mem_eq_h _ _ (Kv + RZv - 14) _ _ 0); [cbn [aeval aoff sptr_exp]; lia | reflexivity | exact HV5]. }
    constructor. { apply val_mem_cell_h. apply (val_mem_eq_h _ _ (Kv + RZv - 12) _ _ NN); [cbn [aeval aoff sptr_exp]; lia | reflexivity | exact HV6]. }
    apply Forall_nil.
  + destruct (Z.eqb_spec (rz_size n) 16) as [E16|N16]; [apply Forall_nil|].
    destruct (HVMG N16) as [M1 M2].
    constructor. { apply val_mem_cell_h. apply (val_mem_eq_h _ _ Kv _ _ 0xCC6E96B9CC6E96B9); [cbn [aeval aoff sptr_exp]; lia | reflexivity | exact M1]. }
    constructor. { apply val_mem_cell_h. apply (val_mem_eq_h _ _ (Kv + 8) _ _ (Kv + RZv - 16)); [cbn [aeval aoff sptr_exp]; lia | cbn [aeval aoff sptr_exp]; lia | exact M2]. }
    apply Forall_nil.
Qed.

Lemma batch_loc : forall b, In b (all_batches S) -> loc_ok (ly_space ly + b_self b) kBatchBytes.
Proof.
intros b Hb a Ha.
pose proof (wfc_classes _ _ _ _ _ vWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
assert (INB : In (b_self b - region_off kBatchClass) (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | exact Hb]).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) (b_self b - region_off kBatchClass) ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (region_in_prim ly kBatchClass vLY ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
assert (XB : b_self b - region_off kBatchClass + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
pose proof off_facts as (O1 & O2 & O3 & _ & O5 & NI & _). pose proof Kv_base as KB. pose proof cls_geom as (K1 & _). pose proof cl_range as CR.
unfold region_base in *. rewrite region_off_eq in * by (unfold kBatchClass; lia).
apply Z_prim.
- unfold kBatchBytes, kFreeArrayOffset, kBatchClass in *. lia.
- intros HK. destruct (Z.eq_dec cl kBatchClass) as [Ec|Nc].
  + assert (Nx : off <> b_self b - kBatchClass * 2 ^ 32).
    { intros E. apply NI. apply in_app_iff; right. apply in_app_iff; right. rewrite Ec. rewrite <- E in INB. exact INB. }
    rewrite Ec, CS in *. apply Z.mod_divide in X2 as [qx Hqx]; [|lia]. apply Z.mod_divide in O3 as [qo Hqo]; [|lia].
    unfold kBatchBytes in *. assert (qx <> qo) by (intros ->; apply Nx; lia). nia.
  + unfold kBatchBytes, kBatchClass, kFreeArrayOffset in *. lia.
Qed.

Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells_cf B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfc_quarantine _ _ _ _ _ vWF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
pose proof (batch_loc b (Hincl b (or_introl eq_refl))) as LOC.
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; left; reflexivity | cbn; lia | cbn; unfold kBatchBytes; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; left; reflexivity | cbn; lia | cbn; unfold kBatchBytes; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; right; left; reflexivity | cbn; lia | cbn; unfold kBatchBytes; lia]|].
apply Forall_app. split.
- apply (keep_cells _ _ _ LOC).
  + intros y Hy. apply INC. do 3 right. apply in_app_iff. left. exact Hy.
  + apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
    cbn. unfold kBatchBytes. lia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.

Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells SF).
Proof.
pose proof SF_same as (_ & _ & _ & Rarr & Rres & _).
replace (sec_cells SF) with (sec_cells S).
2:{ unfold sec_cells. rewrite Rres, Rarr, SF_chunks, flat_map_app. cbn [flat_map ck_beg ImgBaseAG.new_chunk]. rewrite app_nil_r. reflexivity. }
assert (INC : forall x, In x (sec_cells S) -> In x (acells_cf B ly S)) by (intros x Hx; unfold acells_cf; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (wfc_secondary _ _ _ _ _ vWF) as X. destruct X as [Snd Sac Sal Sres Sral Slen].
unfold sec_cells in *.
apply Forall_cons; [apply (keep_cell _ _ _ LOC_inst); [apply INC; left; reflexivity | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC_inst); [apply INC; right; left; reflexivity | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC_inst); [apply INC; right; right; left; reflexivity | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
  + intros a Ha. exact (Z_Q a Ha).
  + intros x Hx. apply INC. do 3 right. apply in_app_iff. left. exact Hx.
  + apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
    cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_flat_map_h. intros k Hk.
  pose proof (chunk_facts_cf B ly S Hp _ k vM Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
  destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try apply Forall_nil.
  destruct GG as (_ & _ & Gbase & Gext & Gin & _).
  apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
  + intros a Ha. apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Gin | unfold in_zr; cbn [fst snd]; exact Ha].
  + intros x Hx. apply INC. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. split; [exact Hk | exact Hx].
  + unfold kPage in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells SF).
Proof.
pose proof SF_same as (_ & _ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SF) with (quar_cells S) by (unfold quar_cells; rewrite Rqt, Rqg; reflexivity).
assert (INC : forall x, In x (quar_cells S) -> In x (acells_cf B ly S)) by (intros x Hx; unfold acells_cf; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof cl_range as CR.
assert (LOCT : loc_ok (ly_T ly + t_qc) 32).
{ intros a Ha. apply Z_T; [unfold t_qc, kThreadObjSize in *; lia|]. intros Hw. unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in *. unfold t_qc, t_cache, t_stats, t_unwinding in *. lia. }
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
apply Forall_cons; [apply (keep_cell _ _ _ LOC_inst); [apply INC; left; reflexivity | cbn; lia | cbn; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC_inst); [apply INC; right; left; reflexivity | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCT); [apply INC; right; right; apply in_app_iff; left; cbn; tauto | cbn; lia | cbn; lia]|]).
  apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
  intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOC_inst); [apply INC; right; right; apply in_app_iff; right; cbn; tauto | cbn; lia | cbn; lia]|]).
  apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
  intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.

Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells SF).
Proof.
pose proof SF_same as (_ & _ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SF) with (fs_cells S) by (unfold fs_cells; rewrite Rfs; reflexivity).
apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. exact (Z_F a Ha).
- intros x Hx. unfold acells_cf. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold fs_cells, kFakeStackSize. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
  apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.

Lemma depot_ids_after : depot_ids (CLdepot.depot_after z tr S) <= 4098.
Proof.
pose proof (depot_len_bound _ _ (amc_universe _ _ _ _ _ vM) (wfc_depot _ _ _ _ _ vWF)) as LEN.
unfold CLdepot.depot_after, depot_ids. unfold DEPOT_MAX in LEN.
destruct (z =? 0); cbn; [lia|]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma fp_range : forall a, CLdepot.depot_footprint B ly a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof (aso_cells _ (amc_syms _ _ _ _ _ vM)) as AC. ceil.
pose proof (oapp (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as ANB.
pose proof (oapp (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as ASB.
unfold CLdepot.depot_footprint, in_app, d_map1, kLowMemEnd, kNodesBlockSize, kStoreBlockSize, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *. lia.
Qed.

Lemma depot_final : CLdepot.depot_mem_ok B ly (CLdepot.depot_after z tr S) rd'.
Proof.
apply (depot_mem_ok_agree_h B ly _ rdD rd' depot_ids_after); [|exact DEPD].
intros a Ha. apply aview_same_h. apply EQD. rewrite unsigned_lit_small by exact (fp_range a Ha).
exact (HFP ly a vLY (HIMG ly S md0 vL) (amc_tsd _ _ _ _ _ vM) Ha).
Qed.

Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SF).
Proof.
pose proof SF_same as (_ & _ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SF) with (ialloc_cells B S) by (unfold ialloc_cells; rewrite Rii; reflexivity).
pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ vM)) as [I1 I2].
assert (INC : forall x, In x (ialloc_cells B S) -> In x (acells_cf B ly S)) by (intros x Hx; unfold acells_cf; do 7 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
unfold ialloc_cells in *.
apply Forall_cons; [apply (keep_cell _ _ _ LOC_flag); [apply INC; left; reflexivity | cbn; lia | cbn; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC_flag); [apply INC; right; left; reflexivity | cbn; lia | cbn; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC_ial); [apply INC; right; right; left; reflexivity | cbn; lia | cbn; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC_ial); [apply INC; right; right; right; left; reflexivity | cbn; lia | cbn; lia]|].
apply Forall_nil.
Qed.

Lemma cells_final : Forall (cell_holds B ly rd') (acells_cf B ly SF).
Proof.
unfold acells_cf.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [|apply Forall_app; split; [exact cells_ialloc|]].
- replace (depot_cells ly SF) with (depot_cells ly (CLdepot.depot_after z tr S))
    by (pose proof SF_same as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep); unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; reflexivity).
  exact (proj1 depot_final).
- unfold thread_cells. constructor; [|apply Forall_nil]. apply val_mem_cell_h. apply (val_mem_eq_h _ _ (ly_T ly + t_unwinding) _ _ 0); [reflexivity | reflexivity | exact HV8].
Qed.

(* The constant cells: on the depot zone from the depot's post, elsewhere kept. *)
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros c Hc.
apply (cell_holds_mix_h B ly rd0 rdD rd' c (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ vM) c Hc) (proj1 (Forall_forall _ _) CSTD c Hc)).
intros k Hk Hno.
pose proof (proj1 (Forall_forall _ _) (const_cells_owned_cf B ly S Hp _ vM) c Hc k Hk) as Ox.
pose proof (AR_owned_low_law_ok_cf im_segs B ly S Hp W mem0 md0 _ HAR Ox) as Rx.
assert (R64 : 0 <= aeval B ly (c_at c) + k < 2 ^ 64) by (ceil; lia).
assert (ND : ~ ag_dzone ly (aeval B ly (c_at c) + k)).
{ intros Hd. apply Hno. right. apply aview_same_h. apply EQD. rewrite unsigned_lit_small by exact R64. exact Hd. }
apply Hno. left. apply AGX; [exact Ox|].
pose proof (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ vM) c Hc k Hk) as OC.
destruct OC as [O|[O|O]].
- apply Exists_exists in O as (r & Hr & Hx). apply Z_img; [|exact ND].
  pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ vM) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
  unfold in_zr in *. lia.
- apply Exists_exists in O as (e & He & Hx). unfold core_extents in He. cbn in He.
  destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold in_zr in Hx; cbn [fst snd] in Hx.
  + exact (Z_Q _ Hx).
  + exact (Z_T _ Hx (HCW ly c k cl vLY (HIMG ly S md0 vL) (amc_tsd _ _ _ _ _ vM) Hc Hk Hcl')).
  + exact (Z_NB _ Hx ND).
  + exact (Z_SB _ Hx ND).
  + exact (Z_C _ Hx).
  + exact (Z_D _ Hx).
- apply Exists_exists in O as (r & Hr & Hx).
  pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ vM)) r Hr) as (T1 & T2 & T3).
  pose proof SK_range as (SK1 & SK2 & SK3). unfold in_zr in Hx. cbn [fst snd] in Hx. unfold shadow_addr in *.
  pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as DA. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MA.
  pose proof (Z.div_mod (snd r + 7) 8 ltac:(lia)) as DB. pose proof (Z.mod_pos_bound (snd r + 7) 8 ltac:(lia)) as MB.
  apply Z_band.
  + unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kImgEnd in *. lia.
  + intros Hs. apply SHX_where in Hs. unfold shadow_addr in Hs. unfold SHADOW_OFF, kHighShadowBeg, kImgEnd in *. lia.
Qed.

Lemma fa_final : fa_entries_ok ly rd' SF.
Proof.
pose proof SF_parts as (Rreg & _). intros c i vv Hc Hi HV k Hk. rewrite Rreg in Hi, HV.
pose proof (wfc_classes _ _ _ _ _ vWF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
rewrite AGX; [exact (amc_fa _ _ _ _ _ vM c i vv Hc Hi HV k Hk) | eapply own_fa_cf; [exact vM | exact Hc | lia] |].
pose proof (region_in_prim ly c vLY Hc) as (R1 & R2 & _). pose proof Kv_base as KB. pose proof off_facts as (O1 & O2 & _ & _ & O5 & _).
pose proof cls_geom as (K1 & _). pose proof cl_range as CR.
apply Z_prim.
- unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
- unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. rewrite !region_off_eq in * by lia. lia.
Qed.

Lemma flags_final : fs_flags_ok ly rd' SF.
Proof.
pose proof SF_parts as (_ & _ & _ & Rfr & _). intros cid pos Hc Hpos. rewrite Rfr.
pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
rewrite AGX; [exact (amc_flags _ _ _ _ _ vM cid pos Hc Hpos) | unfold flag_addr; eapply own_F_low_cf; [exact vM | unfold kFakeFlagsOff, kFakeFramesOff in *; lia] |].
apply Z_F. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.

(* ---- the shadow ---- *)
Lemma poison_range : forall g, in_rangesb g (fa_poison_ranges ly S) = true -> 0 <= g < ASAN_CEIL.
Proof.
intros g IR. apply in_rangesb_true in IR as (lo & len & Hin & Hg).
unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply YG0q.zseq_In in Hc.
  pose proof (region_in_prim ly c vLY ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof (wfc_classes _ _ _ _ _ vWF c ltac:(lia)) as CL. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
  pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
  unfold fa_base, kFreeArrayOffset, kFreeArrayMax, region_base in *. ceil.
  destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold kHighMemBeg in *; lia.
- apply in_flat_map in Hin as (k & Hk & Hin). destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try (destruct Hin; fail). destruct Hin as [E|[]]. injection E as <- <-.
  pose proof (amc_placed _ _ _ _ _ vM) as [PL _].
  pose proof (proj1 (Forall_forall _ _) PL (ly_sec ly r, sec_map_size (ck_req k)) ltac:(unfold sec_extents; apply in_flat_map; exists k; rewrite Eb; split; [exact Hk | left; reflexivity])) as (_ & [H1 _] & H2).
  cbn [fst snd] in H1, H2. unfold YG0f.ASAN_CEIL. lia.
Qed.

Lemma shadow_final : shadow_ok_cf B ly Hp rd' SF.
Proof.
pose proof SF_same as (Rregs & _). pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA).
pose proof cls_geom as (K1 & K2 & K3 & K4). pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5 & G6). pose proof t_geom as (T1 & T2 & T3 & T4 & T5).
pose proof t_div as (D1 & D2 & D3 & D4 & D5 & D6). pose proof SK_range as (SK1 & SK2 & SK3).
assert (FPR : fa_poison_ranges ly SF = fa_poison_ranges ly S).
{ unfold fa_poison_ranges, reg. rewrite Rregs, SF_chunks, flat_map_app. cbn [flat_map ck_beg ImgBaseAG.new_chunk]. rewrite app_nil_r. reflexivity. }
intros g vv Hg8 HV. unfold ashadow in HV. rewrite SF_chunks in HV.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- rewrite (find_chunk_at_app1_h _ _ _ _ _ _ F0) in HV.
  assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
  rewrite AGX; [exact (amc_shadow _ _ _ _ _ vM g vv Hg8 A0) | exact (ashadow_owned_cf B ly S Hp _ g vv vM A0) |].
  apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts_cf B ly S Hp _ k0 vM Hk0) as (C1 & C2 & _).
  apply Z_band; [apply sh_band_h; destruct C1 as [C1 _]; lia|].
  intros HS. apply SHX_where in HS. pose proof (sh_in_chunk g Hg8 ltac:(lia)) as HG. pose proof (cached_vs_chunk k0 Hk0) as D. lia.
- rewrite (find_chunk_at_app2_h _ _ _ _ _ F0) in HV. cbn [find_chunk_at] in HV. rewrite KB, KE in HV.
  destruct (andb (Kv <=? g) (g <? Kv + class_size cl)) eqn:CK.
  + apply andb_prop in CK as [CK1 CK2]. apply Z.leb_le in CK1. apply Z.ltb_lt in CK2.
    rewrite (not_in_head g (conj CK1 CK2)).
    injection HV as HV'. rewrite KB in HV'. unfold chunk_granule in HV'. rewrite KR, KN, KS in HV'. cbv zeta in HV'.
    assert (Hgj : g = Kv + 8 * ((g - Kv) / 8)).
    { pose proof (Z.div_mod (g - Kv) 8 ltac:(lia)) as DG.
      assert (E8 : (g - Kv) mod 8 = 0).
      { apply Z.mod_divide in Hg8 as [s Hs]; [|lia]. apply Z.mod_divide in G3 as [q Hq]; [|lia]. rewrite Hs, Hq.
        replace (s * 8 - q * 16) with ((s - 2 * q) * 8) by lia. apply Z_mod_mult. }
      lia. }
    set (j := (g - Kv) / 8) in *.
    pose proof (sh_granule j) as SA. rewrite <- Hgj in SA.
    assert (Gp : ly_prim ly <= g < ly_prim ly + kPrimResvSize) by lia.
    assert (Gb : kLowShadowBeg <= shadow_addr g < kHighMemBeg) by (apply sh_band_h; unfold kHighMemBeg in *; lia).
    assert (Gs : shadow_addr Kv <= shadow_addr g < shadow_addr Kv + class_size cl / 8) by lia.
    enough (E : rd' (shadow_addr g) = Some vv) by (rewrite E; reflexivity).
    destruct (Z.ltb_spec j (RZv / 8)) as [J1|J1].
    * subst vv. rewrite AGX; [rewrite (shadow250 g Hg8 (conj CK1 CK2)); reflexivity | exact (own_shadow_prim_cf B ly S Hp _ g vM Gp) |].
      apply Z_band; [exact Gb|]. intros HS. apply SHX_where in HS. lia.
    * destruct (Z.ltb_spec j (RZv / 8 + NN / 8)) as [J2|J2].
      -- subst vv. destruct (shadow_present (shadow_addr g) Gs) as [_ [Hh _]].
         unfold aview, mbyte, mrestrict. rewrite Hh. rewrite (HV9 (Z_to_bv 64 (shadow_addr g))).
         ++ cbn [option_map]. rewrite unsigned8_h by lia. reflexivity.
         ++ rewrite unsigned_lit_small by (unfold kLowShadowBeg, kHighMemBeg in *; lia). rewrite SU_eq, D5. lia.
      -- destruct (andb (j =? RZv / 8 + NN / 8) (negb (NN mod 8 =? 0))) eqn:PJ.
         ++ apply andb_prop in PJ as [PJ1 PJ2]. apply Z.eqb_eq in PJ1. apply Bool.negb_true_iff in PJ2. apply Z.eqb_neq in PJ2. subst vv.
            assert (Ho : odd = true) by (apply Hodd; exact PJ2).
            assert (EP : PBv = shadow_addr g) by (rewrite PB_eq; lia).
            rewrite <- EP. apply val_mem_aview_h; [pose proof (Z.mod_pos_bound NN 8 ltac:(lia)); lia | exact (HV10 Ho)].
         ++ subst vv. rewrite AGX; [rewrite (shadow250 g Hg8 (conj CK1 CK2)); reflexivity | exact (own_shadow_prim_cf B ly S Hp _ g vM Gp) |].
            apply Z_band; [exact Gb|]. intros HS. unfold hSHX in HS. rewrite SU_eq, PB_eq, D5 in HS.
            apply Bool.andb_false_iff in PJ. destruct HS as [HS|[Ho HS]]; [lia|].
            apply Hodd in Ho. destruct PJ as [PJ|PJ]; [apply Z.eqb_neq in PJ; lia | apply Bool.negb_false_iff in PJ; apply Z.eqb_eq in PJ; exact (Ho PJ)].
  + rewrite FPR in HV. assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
    rewrite AGX; [exact (amc_shadow _ _ _ _ _ vM g vv Hg8 A0) | exact (ashadow_owned_cf B ly S Hp _ g vv vM A0) |].
    destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|discriminate].
    pose proof (poison_range g IR) as GB.
    apply Z_band; [apply sh_band_h; exact GB|]. intros HS. apply SHX_where in HS. pose proof (sh_in_chunk g Hg8 ltac:(lia)) as HG.
    apply Bool.andb_false_iff in CK. destruct CK as [CK|CK]; [apply Z.leb_gt in CK | apply Z.ltb_ge in CK]; lia.
Qed.

Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (amc_zshadow _ _ _ _ _ vM) r Hr i Hi) | eapply own_shadow_zero_cf; [exact vM | exact Hr | exact Hi] |].
pose proof (lo_top ly vLY) as (TP1 & TP2 & TP3 & TP4 & TP5 & TP6 & TP7). pose proof (lo_stk_ceil ly vLY) as SC.
pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5 & G6). pose proof SK_range as (SK1 & SK2 & SK3). pose proof t_div as (_ & _ & D3 & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst snd] in *. unfold page_aligned in TP5.
  assert (SL : shadow_addr (ly_stk_lo ly) = SHADOW_OFF + ly_stk_lo ly / 8) by reflexivity.
  pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as DS1.
  assert (MS : ly_stk_lo ly mod 8 = 0) by (apply Z.mod_divide in TP5 as [q Hq]; [|lia]; rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_mod_mult).
  pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as DS2. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as MS2.
  assert (KS : shadow_addr Kv + class_size cl / 8 = SHADOW_OFF + (Kv + class_size cl) / 8).
  { rewrite D3 at 2. rewrite <- sh_granule. reflexivity. }
  pose proof (Z.div_le_mono (Kv + class_size cl) (ly_stk_lo ly) 8 ltac:(lia) ltac:(ceil; lia)) as DM.
  apply Z_band.
  + unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *. lia.
  + intros Hs. apply SHX_where in Hs. lia.
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ vM)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as DA. pose proof (Z.div_mod (snd r) 8 ltac:(lia)) as DB.
  unfold shadow_addr in *. apply Z_band.
  + unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia.
  + intros Hs. apply SHX_where in Hs. unfold shadow_addr in Hs. unfold SHADOW_OFF, kHighShadowBeg, kLowMemEnd in *. lia.
Qed.

(* ---- visibility ---- *)
Lemma vis_keep : forall lst, incl lst (ajunk_cf B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]); [exact (amc_junk _ _ _ _ _ vM) | exact (amc_areas _ _ _ _ _ vM) | exact (amc_client _ _ _ _ _ vM)].
Qed.

Lemma junk_final : Forall (range_vis B ly rd') (ajunk_cf B ly SF).
Proof.
pose proof SF_same as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rcache & Rdep).
pose proof SF_parts as (Rreg & Rother & Rcl & _). pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA).
pose proof cls_geom as (K1 & K2 & K3 & K4). pose proof cl_range as CR. pose proof off_facts as (_ & _ & _ & _ & _ & _ & CNt & CN & _).
pose proof t_geom as (T1 & T2 & T3 & T4 & T5).
unfold ajunk_cf. rewrite SF_chunks.
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk_cf. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk_cf. right; left. reflexivity. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk_cf; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply Forall_flat_map_h. intros c Hc. apply YG0q.zseq_In in Hc. destruct (Z.eq_dec c cl) as [->|Hne].
  - unfold cache_junk. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks].
    constructor; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in *.
    destruct (Z_lt_le_dec i 4) as [I4|I4].
    + replace (ly_T ly + (t_cache + 80 * cl + 16 + 4 * Z.of_nat (length l)) + i)
        with (aeval B ly (c_at (z4 (aoff (AT (t_cache + 80 * cl)) (16 + 4 * Z.of_nat (length l))) (off / 16))) + Z.of_nat (Z.to_nat i)) by (cbn; lia).
      apply VIS_MONO. apply cell_vis; [| eexists; reflexivity | cbn; lia].
      apply In_acells_cache. unfold cache_cells. rewrite Hinited, Hcache. do 3 right. apply in_map_iff. exists (length l, off). split; [reflexivity|].
      rewrite length_app. cbn [length]. replace (length l) with (0 + length l)%nat at 1 by lia. apply In_combine_seq_last_h.
    + pose proof (proj1 (Forall_forall _ _) (amc_junk _ _ _ _ _ vM) (AT (t_cache + 80 * cl + 16 + 4 * cnt), 64 - 4 * cnt)
        ltac:(unfold ajunk_cf; do 2 right; apply in_app_iff; right; apply in_app_iff; left; apply in_flat_map; exists cl; split; [apply YG0s.In_zseq; lia|];
              unfold cache_junk; rewrite Hinited, Hcache, length_app; cbn [length]; left; f_equal; [f_equal; lia | lia])) as RV.
      specialize (RV (i - 4) ltac:(cbn [snd]; lia)). cbn [fst snd aeval] in RV. apply VIS_MONO.
      replace (ly_T ly + (t_cache + 80 * cl + 16 + 4 * Z.of_nat (length l)) + i) with (ly_T ly + (t_cache + 80 * cl + 16 + 4 * cnt) + (i - 4)) by lia. exact RV.
  - apply vis_keep. left. intros x Hx. unfold ajunk_cf. do 2 right. apply in_app_iff; right. apply in_app_iff; left. apply in_flat_map. exists c. split; [apply YG0s.In_zseq; lia|].
    unfold cache_junk in *. rewrite Rinit, (Rother c) in Hx by lia. exact Hx. }
apply Forall_app; split.
{ rewrite flat_map_app. apply Forall_app; split.
  - apply vis_keep. left. intros x Hx. unfold ajunk_cf. do 2 right. do 2 (apply in_app_iff; right). apply in_app_iff; left. exact Hx.
  - cbn [flat_map]. rewrite app_nil_r. rewrite KBEG in KA. cbn [sptr_exp aeval] in KA.
    apply Forall_forall. intros [e len] Hel i Hi. cbn [fst snd] in Hi |- *. apply Kext_vis.
    unfold chunk_junk in Hel. rewrite KR, KN, KS, KE, KBEG in Hel. unfold kChunkHeaderSize in Hel.
    destruct (Z.eqb_spec (rz_size n) 16) as [E16|N16]; cbn [app In] in Hel.
    + destruct Hel as [E|[E|[]]]; injection E as <- <-; cbn [aeval aoff sptr_exp]; lia.
    + destruct Hel as [E|[E|[E|[]]]]; injection E as <- <-; cbn [aeval aoff sptr_exp]; lia. }
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk_cf. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left.
  unfold sec_junk in *. rewrite Rarr, Rres, SF_chunks, flat_map_app in Hx. cbn [flat_map ck_beg ImgBaseAG.new_chunk app] in Hx. rewrite app_nil_r in Hx. exact Hx. }
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk_cf. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left.
  unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply vis_keep. left. intros x Hx. unfold ajunk_cf. do 2 right. do 5 (apply in_app_iff; right). exact Hx.
Qed.

Lemma areas_final : Forall (range_vis B ly rd') (aareas SF).
Proof.
pose proof SF_same as (Rregs & _ & _ & _ & Rres & _).
replace (aareas SF) with (aareas S); [apply vis_keep; right; left; intros x Hx; exact Hx|].
unfold aareas, reg. rewrite Rregs, Rres, SF_chunks, flat_map_app. cbn [flat_map ck_beg ImgBaseAG.new_chunk]. rewrite app_nil_r. reflexivity.
Qed.

Lemma client_final : Forall (range_vis B ly rd') (aclient SF).
Proof.
pose proof SF_parts as (_ & _ & _ & Rfr & _). pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). pose proof Kc_user as [KU1 KU2]. pose proof t_geom as TG.
unfold aclient. rewrite Rfr, SF_chunks, flat_map_app.
apply Forall_app; split; [apply Forall_app; split|].
- apply vis_keep. right; right. intros x Hx. unfold aclient. apply in_app_iff. left. exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_user. rewrite KS, KN.
  constructor; [|apply Forall_nil]. intros i Hi. cbn [fst snd] in *. rewrite KU2.
  apply apresent_vis_h. apply PRW. right; left. lia.
- apply vis_keep. right; right. intros x Hx. unfold aclient. apply in_app_iff. right. exact Hx.
Qed.

Lemma zero_final : Forall (range_zero B ly rd') (ialloc_zero B).
Proof.
pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ vM)) as [I1 I2].
apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) (amc_zero _ _ _ _ _ vM) r Hr i Hi).
assert (Ha : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
{ unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
apply AGX; [| exact (LOC_ial _ Ha)].
eapply (own_area_cf B ly S Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact vM | unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia].
Qed.

Lemma hp_final : Forall (fun p => exists k, In k (st_chunks SF) /\ ck_state k = CAllocated /\ p = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k) Hp.
Proof.
eapply Forall_impl; [|exact (amc_hp_live _ _ _ _ _ vM)]. intros p (k & Hk & Hst & Hpk & Hhd). exists k.
split; [rewrite SF_chunks; apply in_or_app; left; exact Hk|]. tauto.
Qed.

(* ---- the ledger, the budget and the hidden shadow ---- *)
Lemma ledger_final : ALedger_cf im_segs ly SF (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
pose proof SF_same as (Rregs & _ & Rsecs & _ & Rres & _). pose proof SF_parts as (_ & _ & _ & _ & Rsx & Rxs).
assert (EZ : errb_zone ly SF = errb_zone ly S) by (unfold errb_zone; exact Rxs).
assert (EE : eager_cf ly SF md0 = eager_cf ly S md0) by (unfold eager_cf, prim_committed, reg; rewrite Rregs, Rres, Rsx, EZ; reflexivity).
apply (ALedger_same_cf im_segs ly SF md0); [| reflexivity | reflexivity | unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; reflexivity].
pose proof vL as L. destruct L.
constructor; try assumption; try (rewrite ?EZ, ?Rsx, ?Rxs, ?EE; assumption).
match goal with H : exists pieces, prim_pieces_ok ly S pieces /\ _ |- _ =>
  destruct H as (pieces & (Q1 & Q2 & Q3) & P2) end.
exists pieces. split; [|exact P2].
unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in *. rewrite Rregs. exact (conj Q1 (conj Q2 Q3)).
Qed.

Lemma budget_final : abudget_ok_cf im_segs ly SF W.
Proof.
pose proof SF_same as (Rregs & _ & Rsecs & _ & Rres & _). pose proof SF_parts as (_ & _ & _ & _ & Rsx & _).
destruct HAR as (_ & _ & (B1 & B2 & B3) & _).
assert (EH : cf_hull SF = cf_hull S).
{ apply cf_hull_frame; [exact Rsecs|]. unfold sec_live_hulls. rewrite SF_chunks, fold_right_app. cbn. reflexivity. }
assert (EB : abudget_cf SF = abudget_cf S).
{ unfold abudget_cf. rewrite EH. unfold prim_committed, sec_live_bytes, errb_cap_cf, errb_e.
  rewrite Rregs, Rres, Rsecs, SF_chunks, !fold_right_app. cbn. reflexivity. }
split; [rewrite EB; exact B1|]. split; [|exact B3]. unfold asecA. rewrite Rsx. exact B2.
Qed.

Lemma band_hidden_keep : forall a, in_band_rw a -> w_H W (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a).
Proof.
intros a Hb Hh. assert (Ra : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia).
assert (Bd : kLowShadowBeg <= a < kHighMemBeg) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
pose proof SK_range as (SK1 & SK2 & SK3). pose proof Kv_geom as (G1 & _).
assert (NSH : ~ (shadow_addr Kv <= a < shadow_addr Kv + class_size cl / 8)).
{ intros Hs. destruct (shadow_present a Hs) as [_ [Hh' _]]. congruence. }
pose proof t_geom as TG.
apply MEQF; rewrite unsigned_lit_small by exact Ra.
- unfold hWIN. intros [Hs|[Hw|[Hk|[Ho Hpb]]]].
  + destruct Hsp as [S1 S2]. pose proof (lo_top _ vLY) as (_ & _ & _ & _ & _ & _ & TP7). unfold AFSTACK, kHighMemBeg in *. lia.
  + exact (app_not_band (ly_T ly) kThreadObjSize a (oapp (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) (WINT_T a Hw) Bd).
  + unfold kHighMemBeg in *. lia.
  + apply NSH. pose proof (SHX_where a (or_intror (conj Ho Hpb))) as X. lia.
- intros Hd. destruct (DZ_loc a Hd) as [H|[H|H]].
  + pose proof (img_low a H). unfold kImgEnd, kLowShadowBeg in *. lia.
  + exact (app_not_band _ _ a (oapp (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) H Bd).
  + exact (app_not_band _ _ a (oapp (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) H Bd).
- intros Hk. unfold kHighMemBeg in *. lia.
- intros Hs. apply NSH. pose proof (SHX_where a (or_introl Hs)) as X. lia.
Qed.

Lemma client_band : forall a, in_band_rw a -> aclient_byte B ly SF a -> aclient_byte B ly S a.
Proof.
intros a Hb [(k & Hk & Hst & Hr)|(fcp & Hcp & Hr)].
- rewrite SF_chunks in Hk. apply in_app_iff in Hk as [Hk|[<-|[]]].
  + left. exists k. tauto.
  + exfalso. pose proof Kc_user as [KU1 _]. pose proof Kv_geom as (G1 & _). pose proof t_geom as (T1 & _). rewrite KU1 in Hr.
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, YG0f.kHighMemBeg in *. lia.
- right. exists fcp. pose proof SF_parts as (_ & _ & _ & Rfr & _). rewrite Rfr in Hcp. tauto.
Qed.

Lemma hfree_keep : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> w_H W (Z_to_bv 64 (shadow_addr g)) = false ->
  aview im_segs (w_H W) mem' (shadow_addr g) = aview im_segs (w_H W) mem0 (shadow_addr g).
Proof.
intros g Hg HA HF _. apply AGX; [exact (hfree_shadow_owned_cf B ly S Hp _ g vM Hg HA HF)|].
pose proof (shadow_addr_band_rw g HA) as SB.
apply Z_band; [unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia|].
intros Hs. apply SHX_where in Hs. pose proof SK_range as (SK1 & _).
pose proof (sh_in_chunk g Hg ltac:(lia)) as HK. pose proof Kv_geom as (_ & _ & _ & G4 & G5 & _).
unfold hfree in HF. pose proof (proj1 (Forall_forall _ _) HF (ly_prim ly, kPrimResvSize) ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; left; reflexivity)) as X.
cbn [fst snd] in X. pose proof cls_geom as (K1 & _). lia.
Qed.

(* ---- the two machine cells of ARmcf (amc_exh_cell / amc_errb_cells, field round 2) ---- *)
(* A byte the walk does not write keeps its value: off the changed set XC and off Allocate's stack window, at_RETw's
   raw frame MEQF gives it (no ownership needed, unlike AGX). *)
Lemma raw_keep : forall a, 0 <= a < 2 ^ 64 -> ~ XC a -> ~ (sp0 - AFSTACK <= a < sp0) -> rd' a = rd0 a.
Proof.
intros a Ra Hx Hs. pose proof t_geom as TG. unfold hXC, hSHX in Hx.
apply aview_same_h. apply MEQF; rewrite unsigned_lit_small by exact Ra.
- intros Hw. unfold hWIN in Hw. destruct Hw as [Hw|[Hw|[Hk|Ho]]].
  + exact (Hs Hw).
  + apply Hx. left. exact Hw.
  + apply Hx. right; left. lia.
  + apply Hx. right; right; left. right. exact Ho.
- intros Hd. apply Hx. right; right; right. exact Hd.
- intros Hk. apply Hx. right; left. lia.
- intros Hs'. apply Hx. right; right; left. left. exact Hs'.
Qed.

(* Allocate's stack window lies in the layout's stack (static extent 8), apart from every other static extent. *)
Lemma stk_apart : forall i e a, nth_error (static_extents ly) i = Some e -> in_zr a e -> i <> 8%nat ->
  ~ (sp0 - AFSTACK <= a < sp0).
Proof.
intros i e a Hi Ha Hne Hs. pose proof Hsp as [S1 S2].
apply (ext_apart i e a Hi Ha 8 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) eq_refl Hne).
unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma app_range : forall lo len a, in_app lo len -> lo <= a < lo + len -> 0 <= a < 2 ^ 64.
Proof. intros lo len a H Ha. ceil. unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia. Qed.

(* The primary's RegionInfo page [space + kRegionInfoOff, + 4096) is kept: it lies in the primary reservation above
   every class region, so off the cached chunk, and off the stack. *)
Lemma rinfo_keep : forall a, ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> rd' a = rd0 a.
Proof.
intros a Ha. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & V6). pose proof cl_range as CR. pose proof (lo_space_in _ vLY) as [SP1 SP2].
assert (HP : ly_prim ly <= a < ly_prim ly + kPrimResvSize) by (unfold kRegionInfoOff, kSpaceSize in *; lia).
apply raw_keep.
- exact (app_range (ly_prim ly) kPrimResvSize a (oapp (ly_prim ly, kPrimResvSize) ltac:(unfold owned_extents; cbn; tauto)) HP).
- apply Z_prim; [exact HP|]. unfold region_base in V6. rewrite region_off_eq in V6 by lia. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
- exact (stk_apart 0 (ly_prim ly, kPrimResvSize) a eq_refl ltac:(unfold in_zr; cbn [fst snd]; exact HP) ltac:(lia)).
Qed.

(* The error-message-buffer object is kept: it is owned static data (errb_obj_owned_t), so in the image window, and
   off the depot's write zone (the ag_dzone part of YGcfErrbSep.ERRB_SEP_t); the image is off XC and off the stack. *)
Lemma errb_obj_keep : errb_obj_owned_t B ->
  (forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a -> ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56)) ->
  forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> rd' a = rd0 a.
Proof.
intros OWN DZE a Ha.
assert (HI : in_zr a (ly_img ly)).
{ pose proof (OWN a Ha) as O. apply Exists_exists in O as (r & Hr & [X1 X2]).
  pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ vM) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
  unfold in_zr. lia. }
pose proof (img_low a HI) as IL.
apply raw_keep.
- unfold kImgLo, kImgEnd in IL. lia.
- apply Z_img; [exact HI|]. intros Hd. exact (DZE ly a vLY (HIMG ly S md0 vL) (amc_tsd _ _ _ _ _ vM) Hd Ha).
- exact (stk_apart 9 (ly_img ly) a eq_refl HI ltac:(lia)).
Qed.

(* exh_cell_cf: the hit keeps the regions (so the exhausted bits) and the RegionInfo bytes. *)
Lemma exh_final : 0 <= cf_exh_off < 128 -> exh_cell_cf B ly S rd0 -> exh_cell_cf B ly SF rd'.
Proof.
intros EXH HE. pose proof SF_same as (Rregs & _).
apply (YGcfInstBase.exh_cell_cf_frame B ly ly S SF rd0 rd' HE).
- intros c. unfold exh_mem_cf, reg. rewrite Rregs. reflexivity.
- intros c Hc.
  replace (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off)) with (ly_space ly + (kRegionInfoOff + 128 * c + cf_exh_off))
    by reflexivity.
  apply rinfo_keep. lia.
Qed.

(* errb_cells_cf: the hit keeps st_secs (so the buffer's model values) and the object's bytes, and makes no byte
   invisible (VIS_MONO). *)
Lemma errb_final : errb_obj_owned_t B ->
  (forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a -> ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56)) ->
  errb_cells_cf B ly S rd0 -> errb_cells_cf B ly SF rd'.
Proof.
intros OWN DZE HE. pose proof SF_same as (_ & _ & Rsecs & _).
apply (YGcfInstBase.errb_cells_cf_frame B ly ly S SF rd0 rd' HE).
- unfold errb_mapped_cf. rewrite Rsecs. reflexivity.
- unfold errb_data_cf. rewrite Rsecs. reflexivity.
- unfold errb_cap_cf, errb_e. rewrite Rsecs. reflexivity.
- unfold errb_size_cf. rewrite Rsecs. reflexivity.
- exact (errb_obj_keep OWN DZE).
- exact VIS_MONO.
Qed.

(* The hit post's ARmcf carries the two cells; the errbuf object's separation from the depot's write zone is the
   one image row the relation does not hold (ag_dzone is a class field). *)
Hypothesis ERRB_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).

(* Printf's two writable image cells (ARmcf's amc_pf_cells, field round 3) lie off the depot's write zone: the
   ag_dzone twin of ERRB_AG for the two cells' 16 bytes (pf_cells_owned_t places them in the owned static data, apart
   from the instance object only). *)
Hypothesis PF_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8).

(* The two cells hold at the memory the hit returns: their bytes are owned static data, so in the image, and off
   the depot's write zone, so off what the hit changes (Z_img); AGX keeps them. *)
Lemma pf_final : pf_cells_owned_t B -> pf_cells_cf B ly rd0 -> pf_cells_cf B ly rd'.
Proof.
intros HO HP. apply (pf_cells_move_cf B ly S Hp rd0 rd' (fun a => ~ XC a) vM HO); [exact AGX| |exact HP].
intros a Ha. pose proof (proj1 HO) as HS. unfold pf_cells_static_t in HS. pose proof (proj1 (HS a Ha)) as O. apply Exists_exists in O as (r & Hr & [X1 X2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ vM) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
apply Z_img; [unfold in_zr; lia|].
intros Hd. exact (PF_AG ly a vLY (HIMG ly S md0 vL) (amc_tsd _ _ _ _ _ vM) Hd Ha).
Qed.

(* ---- THE TRANSPORT: ARcf at the state the hit leaves, at the memory it returns. ---- *)
Theorem hit_ARcf : ARcf im_segs B ly SF Hp W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof SF_same as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rcache & Rdep).
pose proof SF_parts as (Rreg & Rother & Rcl & Rfr & Rsx & Rxs).
pose proof (amc_cells_owned _ _ _ _ _ M0) as [EXH OWN].
split; [|split; [exact ledger_final | split; [exact budget_final | split]]].
- constructor.
  + exact MPwf.
  + exact (amc_universe _ _ _ _ _ M0).
  + exact (amc_syms _ _ _ _ _ M0).
  + exact (amc_layout _ _ _ _ _ M0).
  + unfold sec_placed. rewrite Rsx. exact (amc_placed _ _ _ _ _ M0).
  + exact const_final.
  + exact (amc_const_owned _ _ _ _ _ M0).
  + exact cells_final.
  + exact fa_final.
  + exact flags_final.
  + pose proof (proj1 (proj2 depot_final)) as D. revert D. unfold depot_ok, depot_ids, depot_traces. rewrite Rdep. exact (fun H => H).
  + exact shadow_final.
  + exact zshadow_final.
  + exact junk_final.
  + exact areas_final.
  + exact client_final.
  + exact zero_final.
  + exact (amc_tsd _ _ _ _ _ M0).
  + exact (amc_static_img _ _ _ _ _ M0).
  + exact hp_final.
  + unfold xs_placed_cf. rewrite Rxs, Rsx. exact (amc_xs_placed _ _ _ _ _ M0).
  + exact (exh_final (YGcfImgRows.EXH_OFF_bound EXH) (amc_exh_cell _ _ _ _ _ M0)).
  + exact (errb_final (proj1 OWN) ERRB_AG (amc_errb_cells _ _ _ _ _ M0)).
  + exact (conj EXH OWN).
  + exact (pf_final (amc_pf_owned _ _ _ _ _ M0) (amc_pf_cells _ _ _ _ _ M0)).
  + exact (amc_pf_owned _ _ _ _ _ M0).
- exact (amwf_same md0 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW).
- exact (ahs_transfer_cf im_segs B ly S Hp SF (w_H W) mem0 mem' (al_img_env_cf im_segs ly S md0 vLY vL) M0 HS0 VIS_MONO band_hidden_keep client_band Rsx hfree_keep).
Qed.

End t.
End a.
