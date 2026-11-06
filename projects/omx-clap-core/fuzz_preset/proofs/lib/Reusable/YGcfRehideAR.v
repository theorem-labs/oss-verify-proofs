(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstDrainQ.v, with its module paths and module names changed; 938 of its 969 lines of code are new or changed and 111 lines of the source are left out. *)
(* The F1 re-hide step's relation transfer: the cf relation across YA0nR.wrehide (group T2-T5 of the re-hide design).
   rule 24: no function proved (kind: segment lemma).

   At the recycle walk's return world W the dead secondary slot r's map (MAP, LEN), MAP = ly_sec ly r and
   LEN = sm_len sm2, has left the allowance with its munmap's refund, while its shadow hull h := shull (MAP, LEN) is
   still in w_A W. The re-hide step hides the hull's madvised interior [PB, PE) := [rh_lo MAP, rh_hi MAP LEN)
   (YGcfRehidePost) and replaces h by its two edges (YA0nR.A_rehide). ARcf_rehide carries the relation, and
   ARcfR_rehide the cut relation (YGcfInstDrainR.ARcfR), from (S', W) to the re-hidden world:
   - T2 (ARmcf_rehide, R.ARmcfR_rehide): the reader changes only on [PB, PE), where it becomes None
     (aview_rehide_out), and no field of the record reads there. Every address a field reads is application memory,
     image memory, or the shadow of an extent that M1 places apart from the dead map, and the interior of the dead
     map's shadow hull is the shadow of the dead map alone (rout_shadow_range).
   - T3 (ahs_rehide): the newly hidden bytes are mapped (the interior premise); ahz reads memory only.
   - T4 (abudget_ok_rehide): the ledger only drops (YA0nR.A_bytes_rehide); asecA keeps every live map and hull,
     because A_drop removes only entries equal to h, a live map is application memory, and a live hull differs from h
     when LEN >= kMaxSize + kPage (asecA_rehide); the class-1 band is the shadow of the primary reservation, which is
     apart from the dead map (cls1_band_rehide).
   Premises besides the relation and the walk's facts (the dead slot's identity, HULL, the interior mapped): M1 (the dead map
   is page aligned and apart from every live secondary extent and every static extent), M2 (LEN is at least
   kMaxSize + kPage), and JUNK (every byte of the image's junk ranges lies in a segment: the body of
   YGcfInstRcSec.IMG_JUNK over the theorem's segs). M1 and M2 are not invariants of the relation: a later mmap may
   reuse a dead slot's range. They hold at the recycle's pre-state, where the slot is live; M1_of_pre, M2_of_pre and
   SREAL_of_pre derive them there. The proof reads the dead slot's identity only through in_app, M1 and M2.
   rehide_HO / rehide_HA build the re-hidden world's two proofs. ARcf_rehide_satisfiable derives every premise that is
   not about the walk from the live pre-state, and shows that the hidden interval is not empty and lies in RZ_cf. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG03cf YGcfInstDrainR YGcfInstDrainRL.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG0tcf YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfn YA0nR YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 0. Helpers.                                                                                                      *)
(* An address outside the hidden interval [PB, PE), and inside the 64-bit range (so its word is itself).            *)
Definition rout (PB PE a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (PB <= a < PE).

(* preset-side hunk: this unit's world carries the field w_H8 (YA0n.v:25), so YA0nR.wrehide takes its proof as a
   further argument (YA0nR.v:144-147). rh_lo and rh_hi are multiples of 4096 (YGcfRehidePost.v:30-31), hence
   8-aligned, so YA0nR.H_rehide_H8 builds that proof from w_H8 W. Nothing else changes. *)
Lemma rh_mod8 : forall x : Z, (x / 4096 * 4096) mod 8 = 0.
Proof. intros x. replace 4096 with (512 * 8) by lia. rewrite Z.mul_assoc. apply Z_mod_mult. Qed.

Definition rh_H8 (segs : list Segment) (W : world segs) (MAP LEN : Z) :
  forall a : Z, YG0f.in_band_rw a ->
    H_rehide (w_H W) (rh_lo MAP) (rh_hi MAP LEN) (Z_to_bv 64 a) =
    H_rehide (w_H W) (rh_lo MAP) (rh_hi MAP LEN) (Z_to_bv 64 (a - a mod 8)) :=
  YA0nR.H_rehide_H8 (w_H W) (rh_lo MAP) (rh_hi MAP LEN)
    (rh_mod8 (shadow_addr MAP + 4095)) (rh_mod8 (shadow_addr MAP + LEN / 8)) (w_H8 W).

Lemma zdisjoint_sym_rh : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

Lemma zdisjoint_sub : forall d e lo len, zdisjoint d e -> fst e <= lo -> lo + len <= fst e + snd e -> 0 <= len ->
  zdisjoint d (lo, len).
Proof. intros d e lo len D H1 H2 H3. unfold zdisjoint in *. cbn [fst snd]. lia. Qed.

Lemma pairwise_neq_rh {T : Type} (R : T -> T -> Prop) : (forall x y, R x y -> R y x) ->
  forall l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y.
Proof.
intros Hs l. induction l as [|h t IH]; intros x y P Hx Hy Hne; [destruct Hx|].
cbn [pairwise] in P. destruct P as [F P].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. exact (Hne eq_refl).
- exact (proj1 (Forall_forall _ _) F y Hy).
- apply Hs. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy Hne).
Qed.

Lemma last_cap_none_rh : forall l i acc, last_cap_idx l i acc = None -> acc = None /\ List.filter is_errb_cap l = [].
Proof.
induction l as [|h t IH]; intros i acc H; [split; [exact H | reflexivity]|].
cbn [last_cap_idx] in H. destruct (IH _ _ H) as [H1 H2]. cbn [List.filter].
destruct (is_errb_cap h); [discriminate H1 | split; [exact H1 | exact H2]].
Qed.

(* The re-hidden reader is the old one off [PB, PE). *)
Lemma aview_rehide_out : forall segs (H : word -> bool) mem PB PE a, rout PB PE a ->
  aview segs (H_rehide H PB PE) mem a = aview segs H mem a.
Proof.
intros segs H mem PB PE a [Ha Hn]. unfold aview, mbyte, mrestrict, H_rehide, in_ivb. cbv beta.
rewrite (u64_rh a Ha).
assert (E : ((PB <=? a) && (a <? PE))%bool = false).
{ apply andb_false_iff. destruct (Z_le_gt_dec PB a) as [L|L]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
rewrite E, orb_false_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The dead hull's geometry: from a page-aligned in_app map of at least kMaxSize + kPage bytes, the interior      *)
(*    [rh_lo MAP, rh_hi MAP LEN) is not empty, lies in the map's shadow, and has YA0nR's rh_shape.                  *)
Lemma rh_geom : forall MAP LEN, MAP mod page_size = 0 -> in_app MAP LEN -> kMaxSize + kPage <= LEN ->
  MAP mod 8 = 0 /\ shadow_addr MAP <= rh_lo MAP /\ rh_hi MAP LEN <= shadow_addr MAP + LEN / 8 /\
  rh_lo MAP < rh_hi MAP LEN /\ rh_shape (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN).
Proof.
intros MAP LEN HM HIA HL. unfold page_size in HM.
assert (H8 : MAP mod 8 = 0).
{ apply Z.mod_divide in HM as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
pose proof HIA as [H0 HC]. ceil.
unfold rh_shape, rh_lo, rh_hi, shull, page_size. cbn [fst snd].
remember (shadow_addr MAP) as x eqn:Ex. unfold shadow_addr in Ex.
pose proof (Z.div_mod MAP 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound MAP 8 ltac:(lia)). rewrite H8 in DM.
pose proof (Z.div_mod LEN 8 ltac:(lia)). pose proof (Z.mod_pos_bound LEN 8 ltac:(lia)).
pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod (x + LEN / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + LEN / 8) 4096 ltac:(lia)).
pose proof (Z.div_mod (x + LEN / 8 + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + LEN / 8 + 4095) 4096 ltac:(lia)).
unfold kMaxSize, kPage, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
split; [exact H8|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [apply Z_mod_mult|]. split; [apply Z_mod_mult|]. split; apply Z_mod_mult.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. T2: ARmcf moves to a reader that agrees with the old one off [PB, PE).                                        *)
Section T2.
Variable B : asyms.
Variables MAP LEN PB PE : Z.
Hypothesis H8 : MAP mod 8 = 0.
Hypothesis HIA : in_app MAP LEN.
Hypothesis HL0 : 0 <= LEN.
Hypothesis HPB : shadow_addr MAP <= PB.
Hypothesis HPE : PE <= shadow_addr MAP + LEN / 8.

Lemma rout_bounds : SHADOW_OFF <= PB /\ PE <= kHighMemBeg.
Proof using All.
pose proof HIA as [H0 HC]. ceil. unfold shadow_addr in *.
pose proof (Z.div_mod MAP 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound MAP 8 ltac:(lia)).
pose proof (Z.div_mod LEN 8 ltac:(lia)). pose proof (Z.mod_pos_bound LEN 8 ltac:(lia)).
rewrite H8 in DM. unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. destruct HC as [HC|[HC1 HC2]]; lia.
Qed.

Lemma rout_low : forall a, 0 <= a < SHADOW_OFF -> rout PB PE a.
Proof using All. intros a Ha. pose proof rout_bounds as [B1 B2]. unfold rout. unfold SHADOW_OFF, kHighMemBeg in *. lia. Qed.

Lemma rout_high : forall a, kHighMemBeg <= a < 2 ^ 64 -> rout PB PE a.
Proof using All. intros a Ha. pose proof rout_bounds as [B1 B2]. unfold rout. unfold SHADOW_OFF, kHighMemBeg in *. lia. Qed.

Lemma rout_app : forall a, app_addr a -> rout PB PE a.
Proof using All.
intros a [H0 HC]. ceil. destruct HC as [HC|[HC1 HC2]].
- apply rout_low. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
- apply rout_high. unfold ASAN_CEIL in *. lia.
Qed.

Lemma rout_inapp : forall lo len a, in_app lo len -> lo <= a < lo + len -> rout PB PE a.
Proof using All. intros lo len a HI Ha. exact (rout_app a (in_app_addr lo len a HI Ha)). Qed.

(* The shadow of any range apart from the dead map avoids the interior. *)
Lemma rout_shadow_range : forall lo len a, 0 <= lo -> lo + len <= kHighMemEnd ->
  zdisjoint (MAP, LEN) (lo, len) -> shadow_addr lo <= a < shadow_addr lo + (len + 7) / 8 -> rout PB PE a.
Proof using All.
intros lo len a Hlo Hhi D Ha. pose proof rout_bounds as [B1 B2].
unfold rout, zdisjoint in *. cbn [fst snd] in D. unfold shadow_addr in *.
pose proof (Z.div_mod MAP 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound MAP 8 ltac:(lia)).
pose proof (Z.div_mod LEN 8 ltac:(lia)). pose proof (Z.mod_pos_bound LEN 8 ltac:(lia)).
pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)).
pose proof (Z.div_mod (len + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)).
rewrite H8 in DM. unfold SHADOW_OFF, kHighMemEnd, kHighMemBeg in *. split; lia.
Qed.

Lemma rout_shadow_pt : forall g, 0 <= g < kHighMemEnd -> ~ (MAP <= g < MAP + LEN) -> rout PB PE (shadow_addr g).
Proof using All.
intros g Hg Hn. apply (rout_shadow_range g 1); [lia | lia | unfold zdisjoint; cbn [fst snd]; lia |].
change ((1 + 7) / 8) with 1. lia.
Qed.

(* The zones the record's cells live in. *)
Lemma out_prim : forall ly a, layout_ok ly -> ly_prim ly <= a < ly_prim ly + kPrimResvSize -> rout PB PE a.
Proof using All. intros ly a LO Ha. exact (rout_inapp _ _ a (in_high_app _ _ (lo_high _ LO)) Ha). Qed.

Lemma out_owned : forall ly e a, layout_ok ly -> In e (owned_extents ly) -> fst e <= a < fst e + snd e -> rout PB PE a.
Proof using All. intros ly e a LO He Ha. exact (rout_inapp _ _ a (proj1 (Forall_forall _ _) (lo_app _ LO) e He) Ha). Qed.

Lemma out_img : forall ly a, layout_ok ly -> in_zr a (ly_img ly) -> rout PB PE a.
Proof using All.
intros ly a LO Ha. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). unfold in_zr in Ha. rewrite I0 in Ha.
apply rout_low. unfold kImgLo, kImgEnd, SHADOW_OFF in *. lia.
Qed.

Lemma out_sec : forall ly S e a, sec_placed ly S -> In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> rout PB PE a.
Proof using All.
intros ly S e a [PL _] He Ha. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & IA & _). exact (rout_inapp _ _ a IA Ha).
Qed.

Lemma fp_zones_out : forall ly S Hp rd, ARmcf B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) -> fp_zones B (rout PB PE) ly S.
Proof using All.
intros ly S Hp rd M D. pose proof (amc_layout _ _ _ _ _ M) as LO. constructor.
- intros a Ha. exact (out_prim ly a LO Ha).
- intros e a He Ha. apply (out_owned ly e a LO); [|exact Ha]. unfold core_extents in He. unfold owned_extents. cbn in He |- *. tauto.
- intros a Ha. exact (out_img ly a LO Ha).
- intros e a He Ha. exact (out_sec ly S e a (amc_placed _ _ _ _ _ M) He Ha).
- intros a Ha. apply (out_owned ly (ly_F ly, kFakeStackSize) a LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeFlagsOff, kFakeStackSize in *; lia].
- intros r a Hr Ha.
  pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
  pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
  pose proof (proj1 (Forall_forall _ _) D (ly_img ly) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as DI.
  apply (rout_shadow_range (fst r) (snd r) a); [lia | unfold kImgEnd, kHighMemEnd in *; lia | | exact Ha].
  apply (zdisjoint_sub _ _ _ _ DI); [exact R1 | exact R2 | exact T2].
Qed.

Definition rng_out (ly : alayout) (r : aexp * Z) : Prop := forall i, 0 <= i < snd r -> rout PB PE (aeval B ly (fst r) + i).

Lemma cells_move : forall ly (rd rd' : reader) l, (forall a, rout PB PE a -> rd' a = rd a) ->
  Forall (cell_bytes_in B (rout PB PE) ly) l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof using All.
intros ly rd rd' l AG IN H. apply Forall_forall. intros c Hc.
apply (cell_holds_agree B ly rd rd' c (proj1 (Forall_forall _ _) H c Hc)). intros k Hk.
apply AG. exact (proj1 (Forall_forall _ _) IN c Hc k Hk).
Qed.

Lemma vis_move : forall ly (rd rd' : reader) l, (forall a, rout PB PE a -> rd' a = rd a) ->
  Forall (rng_out ly) l -> Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l.
Proof using All.
intros ly rd rd' l AG IN H. apply Forall_forall. intros r Hr i Hi.
rewrite (AG _ (proj1 (Forall_forall _ _) IN r Hr i Hi)). exact (proj1 (Forall_forall _ _) H r Hr i Hi).
Qed.

Lemma chunk_ext_out : forall ly S Hp rd k a, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
  ck_base B ly k <= a < ck_base B ly k + ck_extent k -> rout PB PE a.
Proof using All.
intros ly S Hp rd k a M Hk Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (extent_zone_cf B ly S Hp rd k M Hk) as [[P1 P2]|(m & len & Hin & E1 & E2)].
- apply (out_prim ly a LO). lia.
- apply (out_sec ly S (m, len) a (amc_placed _ _ _ _ _ M) Hin). cbn [fst snd]. unfold kPage in *. lia.
Qed.

(* Every shadow byte the strong shadow field reads is the shadow of a granule of the primary reservation or of a live
   secondary extent (YG0tcf.ashadow_app_zone_cf), both apart from the dead map. *)
Lemma ashadow_out : forall ly S Hp rd g v, ARmcf B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  ashadow B ly S g = Some v -> rout PB PE (shadow_addr g).
Proof using All.
intros ly S Hp rd g v M D Hv. pose proof (ashadow_app_cf B ly S Hp rd g v M Hv) as [G1 G2].
apply rout_shadow_pt; [lia|].
destruct (ashadow_app_zone_cf B ly S Hp rd g v M Hv) as [HP|(m & len & Hin & E1)].
- pose proof (proj1 (Forall_forall _ _) D (ly_prim ly, kPrimResvSize) ltac:(apply in_app_iff; right; unfold static_extents, owned_extents; cbn; tauto)) as DP.
  unfold zdisjoint in DP. cbn [fst snd] in DP. lia.
- pose proof (proj1 (Forall_forall _ _) D (m, len) ltac:(apply in_app_iff; left; exact Hin)) as DE. unfold zdisjoint in DE. cbn [fst snd] in DE. lia.
Qed.

Lemma junk_out : forall ly S Hp rd, ARmcf B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  (forall r0 j, In r0 (as_junk B ly) -> 0 <= j < snd r0 -> rout PB PE (aeval B ly (fst r0) + j)) ->
  Forall (rng_out ly) (ajunk_cf B ly S).
Proof using All.
intros ly S Hp rd M D JX. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (amc_syms _ _ _ _ _ M) as SY. pose proof (aso_cells _ SY) as AC. pose proof (lo_space_in _ LO) as [SP1 SP2].
pose proof (fp_zones_out ly S Hp rd M D) as FZ.
assert (RI : forall a, ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> rout PB PE a).
{ intros a Ha. apply (out_prim ly a LO). unfold kRegionInfoOff, kSpaceSize in *. lia. }
assert (TT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> rout PB PE a).
{ intros a Ha. apply (out_owned ly (ly_T ly, kThreadObjSize) a LO); [unfold owned_extents; cbn; tauto | exact Ha]. }
unfold ajunk_cf.
apply Forall_cons; [intros i Hi; cbn [aeval fst snd] in *; apply RI; lia|].
apply Forall_cons; [intros i Hi; cbn [snd] in Hi; lia|].
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  unfold region_junk_cf, region_junk in Hin.
  destruct Hin as [EE|[EE|[EE|[]]]]; injection EE as <- <-; cbn [aeval aoff fst snd] in Hi |- *; apply RI;
  unfold kRegionInfoOff in *; lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  revert Hin. unfold cache_junk. cbv zeta. destruct (st_cache_inited S); intros Hin;
  destruct Hin as [EE|[]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *; apply TT;
  unfold t_cache, kThreadObjSize in *; lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q2 & _).
  assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
  { intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
  apply (chunk_ext_out ly S Hp rd k _ M Hk).
  unfold chunk_junk in Hin. rewrite !in_app_iff in Hin. unfold kChunkHeaderSize in Hin.
  destruct Hin as [Hin|[[EE|[]]|[Hin|[EE|[]]]]];
  [destruct (ck_rz k =? 16); [destruct Hin | destruct Hin as [EE|[]]] | | destruct (ck_state k); [destruct Hin | destruct Hin as [EE|[]]] |];
  injection EE as <- <-; cbn [fst snd] in Hi |- *; rewrite ?EA in *; unfold ck_n in *; lia. }
apply Forall_app; split.
{ unfold sec_junk. pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as SR.
  apply Forall_cons; [intros i Hi; cbn [aeval fst snd] in *; apply rout_low; unfold o_sec_sorted, kLowMemEnd, SHADOW_OFF in *; lia|].
  apply Forall_cons; [intros i Hi; cbn [aeval fst snd] in *; apply rout_low; unfold o_sec_stats, o_sec_mutex, kLowMemEnd, SHADOW_OFF in *; lia|].
  apply Forall_cons.
  { intros i Hi. cbn [aeval fst snd] in Hi |- *.
    apply (out_owned ly (ly_Q ly, kPtrArrayResv) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia]. }
  apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  assert (Gin : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S))
    by (unfold sec_extents; apply in_flat_map; exists k; split; [exact Hk | rewrite Eb; left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) (sec_extents_len_cf B ly S Hp rd M) _ Gin) as LB. cbn [snd] in LB.
  cbn [aeval fst snd] in Hi |- *. apply (out_sec ly S _ _ (amc_placed _ _ _ _ _ M) Gin). cbn [fst snd]. unfold kPage in *. lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (b & Hb & Hin). destruct Hin as [EE|[]]. injection EE as <- <-.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ WF)) b Hb) as [L1 L2].
  cbn [aeval aoff batch_exp fst snd] in Hi |- *. apply (batch_in_cf B (rout PB PE) ly S Hp rd b _ M FZ Hb).
  unfold kBatchSlots, kBatchBytes in *. lia. }
apply Forall_app; split.
{ unfold thread_junk. apply Forall_forall. intros [e len] Hin i Hi.
  destruct Hin as [EE|[EE|[EE|[EE|[]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *; apply TT;
  unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi.
  destruct Hin as [EE|[EE|[EE|[EE|[]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *; apply rout_low;
  unfold d_nuniq, kLowMemEnd, SHADOW_OFF in *; lia. }
apply Forall_forall. intros r0 Hr0 i Hi. exact (JX r0 i Hr0 Hi).
Qed.

Lemma areas_out : forall ly S Hp rd, ARmcf B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) -> Forall (rng_out ly) (aareas S).
Proof using All.
intros ly S Hp rd M D. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (lo_space_in _ LO) as [SP1 SP2].
unfold aareas. apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _).
  pose proof (wfc_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 _].
  pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F2. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
  destruct Hin as [EE|[EE|[]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *;
  apply (out_prim ly _ LO); unfold region_base, kFreeArrayOffset, kFreeArrayMax in *; lia. }
apply Forall_app; split.
{ apply Forall_cons; [|apply Forall_nil]. intros i Hi. cbn [aeval fst snd] in Hi |- *.
  pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as SR.
  apply (out_owned ly (ly_Q ly, kPtrArrayResv) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia]. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  assert (Gin : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S))
    by (unfold sec_extents; apply in_flat_map; exists k; split; [exact Hk | rewrite Eb; left; reflexivity]).
  cbn [aeval fst snd] in Hi |- *. apply (out_sec ly S _ _ (amc_placed _ _ _ _ _ M) Gin). cbn [fst snd]. lia. }
pose proof (proj1 (Forall_forall _ _) D (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; left; unfold owned_extents; cbn; tauto)) as DF.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IF. cbn [fst snd] in IF.
apply Forall_forall. intros [e len] Hin i Hi.
destruct Hin as [EE|[EE|[EE|[EE|[EE|[EE|[]]]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *.
- apply (out_owned ly (ly_F ly, kFakeStackSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_owned ly (ly_NB ly, kNodesBlockSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_owned ly (ly_SB ly, kStoreBlockSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_owned ly (ly_T ly, kThreadObjSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_prim ly _ LO). unfold kRegionInfoOff, kSpaceSize in *. lia.
- change ((kFakeStackSize - kFakeFramesOff) / 8) with 1441792 in Hi.
  destruct IF as [IF0 IF1]. ceil.
  apply (rout_shadow_range (ly_F ly + kFakeFramesOff) (kFakeStackSize - kFakeFramesOff)).
  + unfold kFakeFramesOff. lia.
  + unfold kFakeFramesOff, kFakeStackSize, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *. destruct IF1 as [IL|[IH1 IH2]]; lia.
  + apply (zdisjoint_sub _ _ _ _ DF); cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize; lia.
  + change ((kFakeStackSize - kFakeFramesOff + 7) / 8) with 1441792. lia.
Qed.

Lemma client_out : forall ly S Hp rd, ARmcf B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) -> Forall (rng_out ly) (aclient S).
Proof using All.
intros ly S Hp rd M D. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (proj1 (Forall_forall _ _) D (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; left; unfold owned_extents; cbn; tauto)) as DF.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IF. cbn [fst snd] in IF.
unfold aclient. apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  unfold chunk_user in Hin. destruct (ck_state k); [|destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  cbn [fst snd] in Hi |- *. apply (chunk_ext_out ly S Hp rd k _ M Hk).
  change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *. lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_map_iff in Hin as ([cid pos] & EE & Hcp). injection EE as <- <-.
  pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfc_fakestack _ _ _ _ _ WF)) (cid, pos) Hcp) as [C1 C2]. cbn [fst snd] in C1, C2.
  pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
  cbn [aeval fst snd] in Hi |- *. change (2 ^ 20) with 1048576 in *.
  apply (out_owned ly (ly_F ly, kFakeStackSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeStackSize, kFakeFramesOff in *; lia]. }
apply Forall_forall. intros [e len] Hin i Hi. apply in_map_iff in Hin as ([cid pos] & EE & Hcp). injection EE as <- <-.
pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfc_fakestack _ _ _ _ _ WF)) (cid, pos) Hcp) as [C1 C2]. cbn [fst snd] in C1, C2.
pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
cbn [aeval fst snd] in Hi |- *. change (2 ^ 20) with 1048576 in *.
destruct IF as [IF0 IF1]. ceil.
assert (DV : fs_frame_bytes cid / 8 <= (fs_frame_bytes cid + 7) / 8) by (apply Z.div_le_mono; lia).
apply (rout_shadow_range (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid)).
- unfold kFakeFramesOff in *. lia.
- unfold kFakeFramesOff, kFakeStackSize, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *. destruct IF1 as [IL|[IH1 IH2]]; lia.
- apply (zdisjoint_sub _ _ _ _ DF); cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia.
- lia.
Qed.

(* T2: every field of ARmcf moves to a reader that agrees with the old one at every address outside [PB, PE). *)
Lemma ARmcf_rehide : forall ly S Hp (rd rd' : reader),
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  (forall r0 j, In r0 (as_junk B ly) -> 0 <= j < snd r0 -> rout PB PE (aeval B ly (fst r0) + j)) ->
  (forall a, rout PB PE a -> rd' a = rd a) ->
  ARmcf B ly S Hp rd -> ARmcf B ly S Hp rd'.
Proof using All.
intros ly S Hp rd rd' D JX AG M.
pose proof M as M0. pose proof (fp_zones_out ly S Hp rd M D) as FZ.
destruct (amc_cells_owned _ _ _ _ _ M) as [HEXO [HEO _]].
assert (FH : forall a, ly_F ly <= a < ly_F ly + 88 -> rout PB PE a).
{ intros a Ha. apply (out_owned ly (ly_F ly, kFakeStackSize) a (amc_layout _ _ _ _ _ M)); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeStackSize; lia]. }
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp Xxs Xexh Xerr Xown Xpf Xpfo].
constructor; try assumption.
- exact (cells_move ly rd rd' _ AG (const_cells_in_cf B (rout PB PE) ly S Hp rd M0 FZ) Xconst).
- exact (cells_move ly rd rd' _ AG (acells_in_cf B (rout PB PE) ly S Hp rd M0 FZ FH) Xcells).
- intros c i v Hc Hi Hv k Hk. rewrite AG; [exact (Xfa c i v Hc Hi Hv k Hk)|].
  pose proof (wfc_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
  pose proof (region_in_prim ly c Xlay Hc) as (R1 & R2 & R3 & R4 & R5).
  apply (out_prim ly _ Xlay). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
- intros cid pos Hc Hpos. rewrite AG; [exact (Xflags cid pos Hc Hpos)|].
  pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr.
  apply (out_owned ly (ly_F ly, kFakeStackSize) _ Xlay); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia].
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. rewrite AG; [exact (H2 k Hk)|].
    pose proof (aso_cells _ Xsyms) as AC. apply rout_low. unfold d_tab_words, kLowMemEnd, SHADOW_OFF in *. lia.
  + intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
    assert (NB : depot_ids S <= 4097).
    { unfold depot_ids. pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold DEPOT_MAX in DL. lia. }
    assert (OR : forall k, 0 <= k < 16 -> rout PB PE (ly_NB ly + 16 * id + k)).
    { intros k Hk. apply (out_owned ly (ly_NB ly, kNodesBlockSize) _ Xlay); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kNodesBlockSize; lia]. }
    split; intros k Hk; rewrite AG; auto; [apply OR; lia|].
    replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. apply OR. lia.
- intros g v Hg Hv. rewrite (AG _ (ashadow_out ly S Hp rd g v M0 D Hv)). exact (Xshadow g v Hg Hv).
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi.
  assert (XA : rout PB PE (shadow_of_addr SHADOW_OFF (fst r) + i)).
  { change (shadow_of_addr SHADOW_OFF (fst r)) with (shadow_addr (fst r)).
    destruct (zshadow_range_facts_cf B ly S Hp rd r M0 Hr) as (Z1 & Z2 & Z3 & Z4 & _).
    assert (DR : zdisjoint (MAP, LEN) r).
    { unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
      - exact (proj1 (Forall_forall _ _) D _ ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; right; left; reflexivity)).
      - pose proof (proj1 (Forall_forall _ _) Ximg r ltac:(apply in_app_iff; right; exact Hr)) as [R1 R2].
        pose proof (proj1 (Forall_forall _ _) D (ly_img ly) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as DI.
        destruct r as [lo len]. cbn [fst snd] in *. apply (zdisjoint_sub _ _ lo len DI); lia. }
    assert (snd r / 8 <= (snd r + 7) / 8) by (apply Z.div_le_mono; lia).
    destruct r as [lo len]. cbn [fst snd] in *. apply (rout_shadow_range lo len); [lia | lia | exact DR | lia]. }
  rewrite (AG _ XA). exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi).
- exact (vis_move ly rd rd' _ AG (junk_out ly S Hp rd M0 D JX) Xjunk).
- exact (vis_move ly rd rd' _ AG (areas_out ly S Hp rd M0 D) Xareas).
- exact (vis_move ly rd rd' _ AG (client_out ly S Hp rd M0 D) Xclient).
- apply Forall_forall. intros r Hr i Hi. rewrite AG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
  pose proof (aso_ialloc _ Xsyms) as [I1 I2]. pose proof (aso_cells _ Xsyms) as AC. apply rout_low.
  unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; unfold kLowMemEnd, SHADOW_OFF in *; lia.
- refine (exh_cell_move_cf B ly S S Hp rd rd' (rout PB PE) M0 HEXO (fun c => eq_refl) (fun a _ Ha => AG a Ha) _ Xexh).
  intros c Hc. pose proof (exh_byte_where_cf B ly S Hp rd c M0 HEXO Hc) as [_ W2]. exact (out_prim ly _ Xlay W2).
- destruct Xerr as (Pc & Q & Dd & Cc & SZ & V & LE & MD).
  assert (CK : forall (A v : Z), cf_errbuf_obj <= A -> A + 8 <= cf_errbuf_obj + 56 ->
    cell_holds B ly rd (z8 (ANum A) v) -> cell_holds B ly rd' (z8 (ANum A) v)).
  { intros A v HA HA' H. apply (cell_holds_agree B ly rd rd' _ H). intros k Hk. cbn [c_w c_at z8 c8 aeval] in Hk |- *.
    apply AG. pose proof (errb_obj_byte_img_cf B ly S Hp rd (A + k) M0 HEO ltac:(lia)) as [I1 I2].
    pose proof (lo_img _ Xlay) as (J0 & J1 & J2 & J3). apply rout_low. rewrite J0 in *. unfold kImgLo, kImgEnd, SHADOW_OFF in *. lia. }
  assert (XB : forall a, errb_data_cf ly S <= a < errb_data_cf ly S + errb_cap_cf S -> rout PB PE a).
  { intros a. unfold errb_data_cf. destruct (last_cap_idx (st_secs S) 0 None) as [j|] eqn:E; intros Ha.
    - unfold xs_placed_cf, xs_cf in Xxs. rewrite E in Xxs. apply Forall_cons_iff in Xxs as [(_ & IAx & _) _]. cbn [fst snd] in IAx.
      exact (rout_inapp _ _ a IAx Ha).
    - exfalso. destruct (last_cap_none_rh _ _ _ E) as [_ HF]. unfold errb_cap_cf, errb_e in Ha. rewrite HF in Ha. cbn [last sm_len] in Ha. lia. }
  unfold errb_cells_cf. cbv zeta.
  split; [apply (CK cf_errbuf_obj); [lia | lia | exact Pc]|].
  split; [apply (CK (cf_errbuf_obj + 16)); [lia | lia | exact Q]|].
  split; [apply (CK (cf_errbuf_obj + 32)); [lia | lia | exact Dd]|].
  split; [apply (CK (cf_errbuf_obj + 40)); [lia | lia | exact Cc]|].
  split; [apply (CK (cf_errbuf_obj + 48)); [lia | lia | exact SZ]|].
  split; [intros a Ha; rewrite (AG _ (XB a Ha)); exact (V a Ha)|]. split; [exact LE | exact MD].
(* field round 3: Printf's two cells are owned static data, inside every zone family (YG0tcf.pf_cells_move_fz_cf) *)
- exact (pf_cells_move_fz_cf B (rout PB PE) ly S Hp rd rd' M0 FZ (fun a _ Ha => AG a Ha)).
Qed.
End T2.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. T3: ahs at the re-hidden set. ahs_pres asks a hidden band byte to be mapped; the newly hidden bytes are mapped *)
(*    by the walk's zero-fill (the premise). ahz reads memory only.                                                 *)
Lemma ahs_rehide : forall B ly S (H : word -> bool) mem PB PE,
  ahs B ly S H mem -> (forall a, PB <= a < PE -> mem (w64 a) <> None) -> ahs B ly S (H_rehide H PB PE) mem.
Proof.
intros B ly S H mem PB PE [HA HZ] HM. split; [|exact HZ].
intros a Ha NC HV. destruct (H (YG0n.w64 a)) eqn:E.
- exact (HA a Ha NC (or_introl E)).
- destruct HV as [HV|HV]; [|exact (HA a Ha NC (or_intror HV))].
  unfold H_rehide, in_ivb in HV. cbv beta in HV. rewrite E in HV. cbn [orb] in HV.
  apply andb_true_iff in HV as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (HM _ (conj H1 H2)) as X. unfold YG0n.w64, YG0d.w64 in *. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. T4 and T5.                                                                                                    *)
Section T5.
Variable segs : list Segment.
Variable B : asyms.
Variable ly : alayout.

(* T4 (ii): A_drop removes only entries equal to h. A live map is application memory and h is shadow; a live hull
   equal to h would make the live map overlap the dead one, or the dead map shorter than kMaxSize + kPage. *)
Lemma asecA_rehide : forall S A MAP LEN, sec_placed ly S -> Forall (fun e => 4096 < snd e) (sec_extents ly S) ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  kMaxSize + kPage <= LEN -> in_app MAP LEN ->
  asecA ly S A -> asecA ly S (A_rehide A (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN)).
Proof using All.
intros S A MAP LEN PL SL [HM D] HL HIA SA e He.
destruct (rh_geom MAP LEN HM HIA HL) as (H8 & _ & _ & _ & _).
destruct (SA e He) as [I1 I2].
pose proof (proj1 (Forall_forall _ _) (proj1 PL) e He) as (_ & IAe & _).
pose proof (proj1 (Forall_forall _ _) SL e He) as LE. cbv beta in LE.
pose proof (proj1 (Forall_forall _ _) D e ltac:(apply in_app_iff; left; exact He)) as DE.
pose proof HIA as [M0 MC]. ceil.
pose proof (Z.div_mod MAP 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound MAP 8 ltac:(lia)). rewrite H8 in DM.
pose proof (Z.div_mod LEN 8 ltac:(lia)). pose proof (Z.mod_pos_bound LEN 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + MAP / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (SHADOW_OFF + MAP / 8) 4096 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + MAP / 8 + LEN / 8 + 4095) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + MAP / 8 + LEN / 8 + 4095) 4096 ltac:(lia)).
unfold A_rehide. split; apply in_or_app; left; apply A_drop_In; split; try assumption.
- intros EQ. unfold shull in EQ. cbn [fst snd] in EQ. unfold shadow_addr in EQ. injection EQ as E1 E2.
  pose proof (in_app_addr (fst e) (snd e) (fst e) IAe ltac:(lia)) as [A0 AA].
  unfold kLowShadowBeg, kHighMemBeg, kMaxSize, kPage, SHADOW_OFF, ASAN_CEIL in *. lia.
- intros EQ. destruct e as [m l]. unfold shull in EQ. cbn [fst snd] in EQ, DE, LE. unfold shadow_addr in EQ. injection EQ as E1 E2.
  unfold zdisjoint in DE. cbn [fst snd] in DE.
  pose proof (Z.div_mod m 8 ltac:(lia)). pose proof (Z.mod_pos_bound m 8 ltac:(lia)).
  pose proof (Z.div_mod l 8 ltac:(lia)). pose proof (Z.mod_pos_bound l 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + m / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (SHADOW_OFF + m / 8) 4096 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + m / 8 + l / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + m / 8 + l / 8 + 4095) 4096 ltac:(lia)).
  unfold kMaxSize, kPage, SHADOW_OFF in *. lia.
Qed.

(* T4 (iii): the class-1 band is the shadow of region 1, which lies in the primary reservation. *)
Lemma cls1_band_rehide : forall S (H : word -> bool) MAP LEN, layout_ok ly ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  kMaxSize + kPage <= LEN -> in_app MAP LEN ->
  cls1_band_vis_cf ly H -> cls1_band_vis_cf ly (H_rehide H (rh_lo MAP) (rh_hi MAP LEN)).
Proof using All.
intros S H MAP LEN LO [HM D] HL HIA BAND a Ha.
destruct (rh_geom MAP LEN HM HIA HL) as (H8 & HPB & HPE & HLT & SH).
assert (HL0 : 0 <= LEN) by (unfold kMaxSize, kPage in HL; lia).
pose proof (region_in_prim ly 1 LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (proj1 (Forall_forall _ _) D (ly_prim ly, kPrimResvSize) ltac:(apply in_app_iff; right; unfold static_extents, owned_extents; cbn; tauto)) as DP.
assert (XA : rout (rh_lo MAP) (rh_hi MAP LEN) a).
{ apply (rout_shadow_range B MAP LEN _ _ H8 HIA HL0 HPB HPE (region_base ly 1) (kFreeArrayOffset + 1) a).
  - unfold kHighMemBeg in R4. lia.
  - ceil. unfold kHighMemEnd, kFreeArrayOffset, ASAN_CEIL in *. lia.
  - apply (zdisjoint_sub _ _ _ _ DP); cbn [fst snd]; unfold kFreeArrayOffset in *; lia.
  - change ((kFreeArrayOffset + 1 + 7) / 8) with 469762049.
    assert (RB8 : region_base ly 1 mod 8 = 0).
    { apply Z.mod_divide in R3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with ((q * 8192) * 8) by lia. apply Z_mod_mult. }
    unfold shadow_addr in *.
    pose proof (Z.div_mod (region_base ly 1) 8 ltac:(lia)) as DR. pose proof (Z.mod_pos_bound (region_base ly 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (region_base ly 1 + kFreeArrayOffset) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (region_base ly 1 + kFreeArrayOffset) 8 ltac:(lia)).
    rewrite RB8 in DR. unfold kFreeArrayOffset in *. lia. }
destruct XA as [XA1 XA2]. unfold H_rehide, in_ivb. cbv beta. rewrite (BAND a Ha). cbn [orb].
unfold YG0n.w64. rewrite (u64_rh a XA1).
apply andb_false_iff. destruct (Z_le_gt_dec (rh_lo MAP) a) as [L|L]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
Qed.

(* The budget conjunct loosened by d bytes, and the relation with it: the state a secondary recycle leaves before its
   re-hide. There the world still holds the dead hull while abudget_cf no longer pays for all of it (sec_live_hulls on
   round 2, cf_hull on the hull round), so abudget_ok_cf itself fails; the re-hide pays the difference. *)
Definition abudget_sl_cf (S : astate) (W : world segs) (d : Z) : Prop :=
  A_bytes (w_A W) <= abudget_cf S + d /\ asecA ly S (w_A W) /\ cls1_band_vis_cf ly (w_H W).
Definition ARcf_sl (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) (d : Z) : Prop :=
  ARmcf B ly S Hp (aview segs (w_H W) mem) /\ ALedger_cf segs ly S md /\ abudget_sl_cf S W d /\ amwf md
  /\ ahs B ly S (w_H W) mem.

Lemma ARcf_sl_of : forall S Hp W mem md d, 0 <= d -> ARcf segs B ly S Hp W mem md -> ARcf_sl S Hp W mem md d.
Proof using All.
intros S Hp W mem md d Hd (M & L & (LB & SA & BAND) & MW & HS).
unfold ARcf_sl, abudget_sl_cf. refine (conj M (conj L (conj (conj _ (conj SA BAND)) (conj MW HS)))). lia.
Qed.

Lemma ARcf_sl_mono : forall S Hp W mem md d d', d <= d' -> ARcf_sl S Hp W mem md d -> ARcf_sl S Hp W mem md d'.
Proof using All.
intros S Hp W mem md d d' Hd (M & L & (LB & SA & BAND) & MW & HS).
unfold ARcf_sl, abudget_sl_cf. refine (conj M (conj L (conj (conj _ (conj SA BAND)) (conj MW HS)))). lia.
Qed.

(* The re-hidden interior is at least LEN / 8 - 8190 bytes, at any MAP: rh_lo rounds shadow_addr MAP up by at most
   4095 and rh_hi rounds shadow_addr MAP + LEN / 8 down by at most 4095. *)
Lemma rh_interior_lb : forall MAP LEN, 0 <= MAP -> 0 <= LEN -> LEN / 8 - 8190 <= rh_hi MAP LEN - rh_lo MAP.
Proof.
intros MAP LEN H0 HL. unfold rh_lo, rh_hi, shadow_addr.
pose proof (Z.div_pos MAP 8 H0 ltac:(lia)). pose proof (Z.div_pos LEN 8 HL ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + MAP / 8 + 4095) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + MAP / 8 + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + MAP / 8 + LEN / 8) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + MAP / 8 + LEN / 8) 4096 ltac:(lia)). lia.
Qed.

(* Each unit's cf_rec_drop law against the interior, at every LEN, the minimum included. Reply's drop
   (YGcfAbudget.reply_rec_drop_cf: the hull less the 16384 the dead entry keeps) is LEN / 8 - 8192, two bytes
   under the interior's bound; preset's drop is 0. *)
Lemma reply_rec_drop_le_rh : forall MAP LEN, 0 <= MAP -> 0 <= LEN ->
  Z.max 0 (LEN / 8 + 8192) - 16384 <= rh_hi MAP LEN - rh_lo MAP.
Proof.
intros MAP LEN H0 HL. pose proof (rh_interior_lb MAP LEN H0 HL). pose proof (Z.div_pos LEN 8 HL ltac:(lia)). lia.
Qed.

Lemma preset_rec_drop_le_rh : forall MAP LEN, 0 <= MAP -> kMaxSize + kPage <= LEN -> 0 <= rh_hi MAP LEN - rh_lo MAP.
Proof.
intros MAP LEN H0 HL. assert (HL0 : 0 <= LEN) by (unfold kMaxSize, kPage in HL; lia).
pose proof (rh_interior_lb MAP LEN H0 HL0).
assert (8704 <= LEN / 8) by (apply (Z.div_le_lower_bound LEN 8 8704); unfold kMaxSize, kPage in HL; lia). lia.
Qed.

(* T4: abudget_ok_cf at the re-hidden world, from the budget loosened by the interior's size: A_bytes_rehide lowers
   A_bytes by at least PE - PB. *)
Lemma abudget_ok_rehide : forall S (W : world segs) MAP LEN HO HA, layout_ok ly -> sec_placed ly S ->
  Forall (fun e => 4096 < snd e) (sec_extents ly S) ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  kMaxSize + kPage <= LEN -> in_app MAP LEN -> In (shull (MAP, LEN)) (w_A W) ->
  abudget_sl_cf S W (rh_hi MAP LEN - rh_lo MAP) ->
  abudget_ok_cf segs ly S (wrehide segs W (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN) HO HA (rh_H8 segs W MAP LEN)).
Proof using All.
intros S W MAP LEN HO HA LO PL SL M1 HL HIA HULL (LB & SA & BAND).
pose proof M1 as [HM _]. destruct (rh_geom MAP LEN HM HIA HL) as (_ & _ & _ & HLT & SH).
unfold abudget_ok_cf. cbn [w_H w_A wrehide]. split; [|split].
- pose proof (A_bytes_rehide (w_A W) (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN) (w_Awf W) HULL SH). lia.
- exact (asecA_rehide S (w_A W) MAP LEN PL SL M1 HL HIA SA).
- exact (cls1_band_rehide S (w_H W) MAP LEN LO M1 HL HIA BAND).
Qed.

(* JUNK places every junk byte in a segment, so (alc_img, lo_img) below kImgEnd, outside the interior. *)
Lemma junk_rout : forall S md MAP LEN, ALedger_cf segs ly S md -> layout_ok ly ->
  MAP mod page_size = 0 -> in_app MAP LEN -> kMaxSize + kPage <= LEN ->
  (forall r0, In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
    exists sg, In sg segs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  forall r0 j, In r0 (as_junk B ly) -> 0 <= j < snd r0 -> rout (rh_lo MAP) (rh_hi MAP LEN) (aeval B ly (fst r0) + j).
Proof using All.
intros S md MAP LEN L LO HM HIA HL JK r0 j Hr Hj.
destruct (rh_geom MAP LEN HM HIA HL) as (H8 & HPB & HPE & _ & _).
assert (HL0 : 0 <= LEN) by (unfold kMaxSize, kPage in HL; lia).
destruct (JK r0 Hr j Hj) as (sg & Hsg & S1 & S2).
pose proof (alc_img _ _ _ _ L sg Hsg) as [G1 G2]. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
apply (rout_low B MAP LEN _ _ H8 HIA HL0 HPB HPE). rewrite I0 in G1, G2. unfold kImgLo, kImgEnd, SHADOW_OFF in *. lia.
Qed.

(* T5. The premises, in the consumer's order: the dead slot's identity at S', M1, M2, JUNK, HULL, the relation at
   (S', W) with the budget loosened by the interior's size (ARcf_sl), and the interior mapped. The identity premises
   are read only through in_app; the others name the slot for the consumer. *)
Theorem ARcf_rehide : forall S' Hp (W : world segs) mem md MAP LEN r sm2
  (HO : H_off_segments segs (H_rehide (w_H W) (rh_lo MAP) (rh_hi MAP LEN)))
  (HA : A_wf (A_rehide (w_A W) (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN))),
  nth_error (st_secs S') r = Some sm2 -> sm_live sm2 = false -> 0 <= sm_size sm2 -> in_app MAP LEN ->
  MAP = ly_sec ly r -> LEN = sm_len sm2 ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly S' ++ static_extents ly) ->
  kMaxSize + kPage <= LEN ->
  (forall r0, In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
    exists sg, In sg segs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  In (shull (MAP, LEN)) (w_A W) ->
  ARcf_sl S' Hp W mem md (rh_hi MAP LEN - rh_lo MAP) ->
  (forall a, rh_lo MAP <= a < rh_hi MAP LEN -> mem (w64 a) <> None) ->
  ARcf segs B ly S' Hp (wrehide segs W (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN) HO HA (rh_H8 segs W MAP LEN)) mem md.
Proof.
intros S' Hp W mem md MAP LEN r sm2 HO HA _ _ _ HIA _ _ M1 HL JK HULL (M & L & BU & MW & HS) HMEM.
pose proof M1 as [HM D].
destruct (rh_geom MAP LEN HM HIA HL) as (H8 & HPB & HPE & HLT & SH).
assert (HL0 : 0 <= LEN) by (unfold kMaxSize, kPage in HL; lia).
pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (junk_rout S' md MAP LEN L LO HM HIA HL JK) as JX.
unfold ARcf. cbn [w_H w_A wrehide].
split; [|split; [exact L | split; [|split; [exact MW|]]]].
- apply (ARmcf_rehide B MAP LEN (rh_lo MAP) (rh_hi MAP LEN) H8 HIA HL0 HPB HPE ly S' Hp (aview segs (w_H W) mem));
    [exact D | exact JX | | exact M].
  intros a Ha. exact (aview_rehide_out segs (w_H W) mem _ _ a Ha).
- exact (abudget_ok_rehide S' W MAP LEN HO HA LO (amc_placed _ _ _ _ _ M) (sec_extents_len_cf B ly S' Hp _ M) M1 HL HIA HULL BU).
- exact (ahs_rehide B ly S' (w_H W) mem _ _ HS HMEM).
Qed.

(* The re-hidden world's two proofs. The interior is shadow, above the image window, so no segment holds it. *)
Lemma rehide_HO : forall S md (W : world segs) MAP LEN, ALedger_cf segs ly S md -> layout_ok ly ->
  MAP mod page_size = 0 -> in_app MAP LEN -> kMaxSize + kPage <= LEN ->
  H_off_segments segs (H_rehide (w_H W) (rh_lo MAP) (rh_hi MAP LEN)).
Proof.
intros S md W MAP LEN L LO HM HIA HL. destruct (rh_geom MAP LEN HM HIA HL) as (H8 & HPB & _ & _ & _).
apply (Hoff_rehide segs (w_H W) _ _ (w_Hoff W)). intros a Ha.
destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:E; [|reflexivity]. exfalso.
apply find_segment_some_spec in E as (Hsg & S1 & S2).
pose proof (alc_img _ _ _ _ L sg Hsg) as [G1 G2]. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof HIA as [M0 _]. unfold shadow_addr in HPB.
pose proof (Z.div_mod MAP 8 ltac:(lia)). pose proof (Z.mod_pos_bound MAP 8 ltac:(lia)).
rewrite I0 in *. unfold kImgLo, kImgEnd, SHADOW_OFF in *. lia.
Qed.

Lemma rehide_HA : forall (W : world segs) MAP LEN, MAP mod page_size = 0 -> in_app MAP LEN -> kMaxSize + kPage <= LEN ->
  A_wf (A_rehide (w_A W) (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN)).
Proof.
intros W MAP LEN HM HIA HL. destruct (rh_geom MAP LEN HM HIA HL) as (_ & _ & _ & _ & SH).
exact (Awf_rehide _ _ _ _ (w_Awf W) SH).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The pre-state sources of M1, M2 and the dead slot's sm_size, and the premises' satisfiability.               *)
(* M1 from the pre-state's placement (ARmcf's amc_placed), where the freed extent is live, given that the
   post-state's live extents are pre-state ones other than the freed one. *)
Lemma M1_of_pre : forall S S' MAP LEN, sec_placed ly S -> In (MAP, LEN) (sec_extents ly S) ->
  (forall e, In e (sec_extents ly S') -> In e (sec_extents ly S) /\ e <> (MAP, LEN)) ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly S' ++ static_extents ly).
Proof.
intros S S' MAP LEN [PL PD] Hin SUB.
pose proof (proj1 (Forall_forall _ _) PL _ Hin) as (PA & _ & _). cbn [fst] in PA. unfold page_aligned in PA.
split; [unfold page_size; exact PA|].
apply Forall_forall. intros e He. apply in_app_iff in He as [He|He].
- destruct (SUB e He) as [HeS Hne].
  apply (pairwise_neq_rh zdisjoint zdisjoint_sym_rh _ _ _ PD).
  + apply in_app_iff. left. exact Hin.
  + apply in_app_iff. left. exact HeS.
  + intros E. apply Hne. symmetry. exact E.
- exact (pairwise_In zdisjoint _ (MAP, LEN) e (sec_extents ly S) (static_extents ly) eq_refl PD Hin He).
Qed.

(* M2 from the freed chunk's chunk_ok_cf (its wfc_chunks entry) and secondary_geometry. *)
Lemma M2_of_pre : forall S k r o sm, chunk_ok_cf S k -> ck_beg k = PSec r o -> nth_error (st_secs S) r = Some sm ->
  kMaxSize + kPage <= sm_len sm.
Proof.
intros S k r o sm [Hn CK] Eb Hsm. rewrite Eb in CK. destruct CK as (Hfp & _ & sm' & Hsm' & _ & _ & Hlen).
rewrite Hsm in Hsm'. injection Hsm' as <-. rewrite Hlen.
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (G1 & _ & _ & [G4 _] & _).
unfold kMaxSize, kPage in *. lia.
Qed.

(* The dead slot is real: its size entry is the freed chunk's needed_size, above kMaxSize. *)
Lemma SREAL_of_pre : forall S k r o sm, chunk_ok_cf S k -> ck_beg k = PSec r o -> nth_error (st_secs S) r = Some sm ->
  0 <= sm_size sm.
Proof.
intros S k r o sm [Hn CK] Eb Hsm. rewrite Eb in CK. destruct CK as (Hfp & _ & sm' & Hsm' & _ & Hsz & _).
rewrite Hsm in Hsm'. injection Hsm' as <-. rewrite Hsz.
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (G1 & _).
unfold kMaxSize in *. lia.
Qed.

(* The premises that are not about the walk hold together: at a pre-state where the freed slot r is live, M1, M2,
   in_app and the size entry hold at the post-state S' (whose live extents are the other pre-state ones, and whose
   entry sm2 keeps sm's length), and then the hidden interval is not empty, has rh_shape, and lies in RZ_cf. *)
Lemma ARcf_rehide_satisfiable : forall S S' k r o sm sm2,
  sec_placed ly S -> In k (st_chunks S) -> chunk_ok_cf S k -> ck_beg k = PSec r o ->
  nth_error (st_secs S) r = Some sm -> sm_len sm2 = sm_len sm -> sm_size sm2 = sm_size sm ->
  (forall e, In e (sec_extents ly S') -> In e (sec_extents ly S) /\ e <> (ly_sec ly r, sm_len sm2)) ->
  (ly_sec ly r mod page_size = 0 /\ Forall (zdisjoint (ly_sec ly r, sm_len sm2)) (sec_extents ly S' ++ static_extents ly)) /\
  kMaxSize + kPage <= sm_len sm2 /\ 0 <= sm_size sm2 /\ in_app (ly_sec ly r) (sm_len sm2) /\
  rh_lo (ly_sec ly r) < rh_hi (ly_sec ly r) (sm_len sm2) /\
  rh_shape (shull (ly_sec ly r, sm_len sm2)) (rh_lo (ly_sec ly r)) (rh_hi (ly_sec ly r) (sm_len sm2)) /\
  (forall a, rh_lo (ly_sec ly r) <= a < rh_hi (ly_sec ly r) (sm_len sm2) -> RZ_cf a).
Proof.
intros S S' k r o sm sm2 PL Hk CK Eb Hsm E2 E3 SUB.
pose proof CK as [Hn CK']. rewrite Eb in CK'. destruct CK' as (Hfp & _ & sm' & Hsm' & _ & _ & Hlen).
rewrite Hsm in Hsm'. injection Hsm' as <-.
assert (Hin : In (ly_sec ly r, sm_len sm2) (sec_extents ly S)).
{ rewrite E2, Hlen. unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk | rewrite Eb; left; reflexivity]. }
pose proof (M1_of_pre S S' _ _ PL Hin SUB) as M1.
pose proof (M2_of_pre S k r o sm CK Eb Hsm) as M2. rewrite <- E2 in M2.
pose proof (proj1 (Forall_forall _ _) (proj1 PL) _ Hin) as (_ & IA & _). cbn [fst snd] in IA.
destruct (rh_geom _ _ (proj1 M1) IA M2) as (_ & _ & _ & HLT & SH).
split; [exact M1|]. split; [exact M2|]. split; [rewrite E3; exact (SREAL_of_pre S k r o sm CK Eb Hsm)|]. split; [exact IA|].
split; [exact HLT|]. split; [exact SH|].
intros a Ha. exact (rh_interior_RZ _ _ a IA ltac:(unfold kMaxSize, kPage in M2; lia) Ha).
Qed.
End T5.
End U.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The cut relation's twin (YGcfInstDrainR.ARcfR). Module R is section 2 over ARmcfR, with RL's ARcfR library   *)
(*    for the chunk, shadow and footprint facts (RL is YG0scf / YG0qcf / YG0tcf over ARmcfR); the arithmetic is     *)
(*    section 2's, at R's section variables. ARcfR_rehide below is ARcf_rehide over ARcfR.                          *)
Module R.
Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* YG0tcf.ashadow_app_zone_cf over ARmcfR. *)
Lemma ashadow_where : forall B ly S Hp rd g v, ARmcfR B ly S Hp rd -> ashadow B ly S g = Some v ->
  (ly_prim ly <= g < ly_prim ly + kPrimResvSize) \/ Exists (in_zr g) (sec_extents ly S).
Proof.
intros B ly S Hp rd g v M H. unfold ashadow in H.
destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
  destruct (RL.extent_zone_cf B ly S Hp rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
  + left. lia.
  + right. apply Exists_exists. exists (m, len). split; [exact Hin | unfold in_zr; cbn [fst snd]; unfold kPage in *; lia].
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
  apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
  + apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
    pose proof (region_in_prim ly c (amr_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c ltac:(lia)) as CL.
    pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
    pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
    left. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  + right. apply Exists_exists. exists (lo, len). split; [exact Hin | exact Hg].
Qed.

Section T2.
Variable B : asyms.
Variables MAP LEN PB PE : Z.
Hypothesis H8 : MAP mod 8 = 0.
Hypothesis HIA : in_app MAP LEN.
Hypothesis HL0 : 0 <= LEN.
Hypothesis HPB : shadow_addr MAP <= PB.
Hypothesis HPE : PE <= shadow_addr MAP + LEN / 8.

(* Section 2's arithmetic at these variables. *)
Lemma rout_low : forall a, 0 <= a < SHADOW_OFF -> rout PB PE a.
Proof using All. exact (rout_low B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma rout_inapp : forall lo len a, in_app lo len -> lo <= a < lo + len -> rout PB PE a.
Proof using All. exact (rout_inapp B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma rout_shadow_range : forall lo len a, 0 <= lo -> lo + len <= kHighMemEnd ->
  zdisjoint (MAP, LEN) (lo, len) -> shadow_addr lo <= a < shadow_addr lo + (len + 7) / 8 -> rout PB PE a.
Proof using All. exact (rout_shadow_range B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma rout_shadow_pt : forall g, 0 <= g < kHighMemEnd -> ~ (MAP <= g < MAP + LEN) -> rout PB PE (shadow_addr g).
Proof using All. exact (rout_shadow_pt B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma out_prim : forall ly a, layout_ok ly -> ly_prim ly <= a < ly_prim ly + kPrimResvSize -> rout PB PE a.
Proof using All. exact (out_prim B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma out_owned : forall ly e a, layout_ok ly -> In e (owned_extents ly) -> fst e <= a < fst e + snd e -> rout PB PE a.
Proof using All. exact (out_owned B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma out_img : forall ly a, layout_ok ly -> in_zr a (ly_img ly) -> rout PB PE a.
Proof using All. exact (out_img B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma out_sec : forall ly S e a, sec_placed ly S -> In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> rout PB PE a.
Proof using All. exact (out_sec B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Definition rng_out (ly : alayout) (r : aexp * Z) : Prop := forall i, 0 <= i < snd r -> rout PB PE (aeval B ly (fst r) + i).
Lemma cells_move : forall ly (rd rd' : reader) l, (forall a, rout PB PE a -> rd' a = rd a) ->
  Forall (RL.cell_bytes_in B (rout PB PE) ly) l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof using All. exact (cells_move B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.
Lemma vis_move : forall ly (rd rd' : reader) l, (forall a, rout PB PE a -> rd' a = rd a) ->
  Forall (rng_out ly) l -> Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l.
Proof using All. exact (vis_move B MAP LEN PB PE H8 HIA HL0 HPB HPE). Qed.

Lemma fp_zones_out : forall ly S Hp rd, ARmcfR B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) -> RL.fp_zones B (rout PB PE) ly S.
Proof using All.
intros ly S Hp rd M D. pose proof (amr_layout _ _ _ _ _ M) as LO. constructor.
- intros a Ha. exact (out_prim ly a LO Ha).
- intros e a He Ha. apply (out_owned ly e a LO); [|exact Ha]. unfold core_extents in He. unfold owned_extents. cbn in He |- *. tauto.
- intros a Ha. exact (out_img ly a LO Ha).
- intros e a He Ha. exact (out_sec ly S e a (amr_placed _ _ _ _ _ M) He Ha).
- intros a Ha. apply (out_owned ly (ly_F ly, kFakeStackSize) a LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeFlagsOff, kFakeStackSize in *; lia].
- intros r a Hr Ha.
  pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
  pose proof (proj1 (Forall_forall _ _) (aso_static _ (amr_syms _ _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
  pose proof (proj1 (Forall_forall _ _) D (ly_img ly) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as DI.
  apply (rout_shadow_range (fst r) (snd r) a); [lia | unfold kImgEnd, kHighMemEnd in *; lia | | exact Ha].
  apply (zdisjoint_sub _ _ _ _ DI); [exact R1 | exact R2 | exact T2].
Qed.

Lemma chunk_ext_out : forall ly S Hp rd k a, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
  ck_base B ly k <= a < ck_base B ly k + ck_extent k -> rout PB PE a.
Proof using All.
intros ly S Hp rd k a M Hk Ha. pose proof (amr_layout _ _ _ _ _ M) as LO.
destruct (RL.extent_zone_cf B ly S Hp rd k M Hk) as [[P1 P2]|(m & len & Hin & E1 & E2)].
- apply (out_prim ly a LO). lia.
- apply (out_sec ly S (m, len) a (amr_placed _ _ _ _ _ M) Hin). cbn [fst snd]. unfold kPage in *. lia.
Qed.

Lemma ashadow_out : forall ly S Hp rd g v, ARmcfR B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  ashadow B ly S g = Some v -> rout PB PE (shadow_addr g).
Proof using All.
intros ly S Hp rd g v M D Hv. pose proof (RL.ashadow_app_cf B ly S Hp rd g v M Hv) as [G1 G2].
apply rout_shadow_pt; [lia|].
destruct (ashadow_where B ly S Hp rd g v M Hv) as [HP|HE].
- pose proof (proj1 (Forall_forall _ _) D (ly_prim ly, kPrimResvSize) ltac:(apply in_app_iff; right; unfold static_extents, owned_extents; cbn; tauto)) as DP.
  unfold zdisjoint in DP. cbn [fst snd] in DP. lia.
- apply Exists_exists in HE as (e & He & [E1 E2]).
  pose proof (proj1 (Forall_forall _ _) D e ltac:(apply in_app_iff; left; exact He)) as DE. unfold zdisjoint in DE. cbn [fst snd] in DE. lia.
Qed.

Lemma junk_out : forall ly S Hp rd, ARmcfR B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  (forall r0 j, In r0 (as_junk B ly) -> 0 <= j < snd r0 -> rout PB PE (aeval B ly (fst r0) + j)) ->
  Forall (rng_out ly) (ajunk_cf B ly S).
Proof using All.
intros ly S Hp rd M D JX. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (amr_syms _ _ _ _ _ M) as SY. pose proof (aso_cells _ SY) as AC. pose proof (lo_space_in _ LO) as [SP1 SP2].
pose proof (fp_zones_out ly S Hp rd M D) as FZ.
assert (RI : forall a, ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> rout PB PE a).
{ intros a Ha. apply (out_prim ly a LO). unfold kRegionInfoOff, kSpaceSize in *. lia. }
assert (TT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> rout PB PE a).
{ intros a Ha. apply (out_owned ly (ly_T ly, kThreadObjSize) a LO); [unfold owned_extents; cbn; tauto | exact Ha]. }
unfold ajunk_cf.
apply Forall_cons; [intros i Hi; cbn [aeval fst snd] in *; apply RI; lia|].
apply Forall_cons; [intros i Hi; cbn [snd] in Hi; lia|].
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  unfold region_junk_cf, region_junk in Hin.
  destruct Hin as [EE|[EE|[EE|[]]]]; injection EE as <- <-; cbn [aeval aoff fst snd] in Hi |- *; apply RI;
  unfold kRegionInfoOff in *; lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  revert Hin. unfold cache_junk. cbv zeta. destruct (st_cache_inited S); intros Hin;
  destruct Hin as [EE|[]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *; apply TT;
  unfold t_cache, kThreadObjSize in *; lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  pose proof (RL.chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q2 & _).
  assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
  { intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
  apply (chunk_ext_out ly S Hp rd k _ M Hk).
  unfold chunk_junk in Hin. rewrite !in_app_iff in Hin. unfold kChunkHeaderSize in Hin.
  destruct Hin as [Hin|[[EE|[]]|[Hin|[EE|[]]]]];
  [destruct (ck_rz k =? 16); [destruct Hin | destruct Hin as [EE|[]]] | | destruct (ck_state k); [destruct Hin | destruct Hin as [EE|[]]] |];
  injection EE as <- <-; cbn [fst snd] in Hi |- *; rewrite ?EA in *; unfold ck_n in *; lia. }
apply Forall_app; split.
{ unfold sec_junk. pose proof (wsc_reserved _ (wfr_secondary _ _ _ _ _ WF)) as SR.
  apply Forall_cons; [intros i Hi; cbn [aeval fst snd] in *; apply rout_low; unfold o_sec_sorted, kLowMemEnd, SHADOW_OFF in *; lia|].
  apply Forall_cons; [intros i Hi; cbn [aeval fst snd] in *; apply rout_low; unfold o_sec_stats, o_sec_mutex, kLowMemEnd, SHADOW_OFF in *; lia|].
  apply Forall_cons.
  { intros i Hi. cbn [aeval fst snd] in Hi |- *.
    apply (out_owned ly (ly_Q ly, kPtrArrayResv) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia]. }
  apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  assert (Gin : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S))
    by (unfold sec_extents; apply in_flat_map; exists k; split; [exact Hk | rewrite Eb; left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) (RL.sec_extents_len_cf B ly S Hp rd M) _ Gin) as LB. cbn [snd] in LB.
  cbn [aeval fst snd] in Hi |- *. apply (out_sec ly S _ _ (amr_placed _ _ _ _ _ M) Gin). cbn [fst snd]. unfold kPage in *. lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (b & Hb & Hin). destruct Hin as [EE|[]]. injection EE as <- <-.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfr_quarantine _ _ _ _ _ WF)) b Hb) as [L1 L2].
  cbn [aeval aoff batch_exp fst snd] in Hi |- *. apply (RL.batch_in_cf B (rout PB PE) ly S Hp rd b _ M FZ Hb).
  unfold kBatchSlots, kBatchBytes in *. lia. }
apply Forall_app; split.
{ unfold thread_junk. apply Forall_forall. intros [e len] Hin i Hi.
  destruct Hin as [EE|[EE|[EE|[EE|[]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *; apply TT;
  unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi.
  destruct Hin as [EE|[EE|[EE|[EE|[]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *; apply rout_low;
  unfold d_nuniq, kLowMemEnd, SHADOW_OFF in *; lia. }
apply Forall_forall. intros r0 Hr0 i Hi. exact (JX r0 i Hr0 Hi).
Qed.

Lemma areas_out : forall ly S Hp rd, ARmcfR B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) -> Forall (rng_out ly) (aareas S).
Proof using All.
intros ly S Hp rd M D. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (lo_space_in _ LO) as [SP1 SP2].
unfold aareas. apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _).
  pose proof (wfr_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 _].
  pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F2. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
  destruct Hin as [EE|[EE|[]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *;
  apply (out_prim ly _ LO); unfold region_base, kFreeArrayOffset, kFreeArrayMax in *; lia. }
apply Forall_app; split.
{ apply Forall_cons; [|apply Forall_nil]. intros i Hi. cbn [aeval fst snd] in Hi |- *.
  pose proof (wsc_reserved _ (wfr_secondary _ _ _ _ _ WF)) as SR.
  apply (out_owned ly (ly_Q ly, kPtrArrayResv) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia]. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  assert (Gin : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S))
    by (unfold sec_extents; apply in_flat_map; exists k; split; [exact Hk | rewrite Eb; left; reflexivity]).
  cbn [aeval fst snd] in Hi |- *. apply (out_sec ly S _ _ (amr_placed _ _ _ _ _ M) Gin). cbn [fst snd]. lia. }
pose proof (proj1 (Forall_forall _ _) D (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; left; unfold owned_extents; cbn; tauto)) as DF.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IF. cbn [fst snd] in IF.
apply Forall_forall. intros [e len] Hin i Hi.
destruct Hin as [EE|[EE|[EE|[EE|[EE|[EE|[]]]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hi |- *.
- apply (out_owned ly (ly_F ly, kFakeStackSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_owned ly (ly_NB ly, kNodesBlockSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_owned ly (ly_SB ly, kStoreBlockSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_owned ly (ly_T ly, kThreadObjSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (out_prim ly _ LO). unfold kRegionInfoOff, kSpaceSize in *. lia.
- change ((kFakeStackSize - kFakeFramesOff) / 8) with 1441792 in Hi.
  destruct IF as [IF0 IF1]. ceil.
  apply (rout_shadow_range (ly_F ly + kFakeFramesOff) (kFakeStackSize - kFakeFramesOff)).
  + unfold kFakeFramesOff. lia.
  + unfold kFakeFramesOff, kFakeStackSize, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *. destruct IF1 as [IL|[IH1 IH2]]; lia.
  + apply (zdisjoint_sub _ _ _ _ DF); cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize; lia.
  + change ((kFakeStackSize - kFakeFramesOff + 7) / 8) with 1441792. lia.
Qed.

Lemma client_out : forall ly S Hp rd, ARmcfR B ly S Hp rd ->
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) -> Forall (rng_out ly) (aclient S).
Proof using All.
intros ly S Hp rd M D. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (proj1 (Forall_forall _ _) D (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; left; unfold owned_extents; cbn; tauto)) as DF.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IF. cbn [fst snd] in IF.
unfold aclient. apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_flat_map in Hin as (k & Hk & Hin).
  unfold chunk_user in Hin. destruct (ck_state k); [|destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  pose proof (RL.chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  cbn [fst snd] in Hi |- *. apply (chunk_ext_out ly S Hp rd k _ M Hk).
  change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *. lia. }
apply Forall_app; split.
{ apply Forall_forall. intros [e len] Hin i Hi. apply in_map_iff in Hin as ([cid pos] & EE & Hcp). injection EE as <- <-.
  pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfr_fakestack _ _ _ _ _ WF)) (cid, pos) Hcp) as [C1 C2]. cbn [fst snd] in C1, C2.
  pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
  cbn [aeval fst snd] in Hi |- *. change (2 ^ 20) with 1048576 in *.
  apply (out_owned ly (ly_F ly, kFakeStackSize) _ LO); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeStackSize, kFakeFramesOff in *; lia]. }
apply Forall_forall. intros [e len] Hin i Hi. apply in_map_iff in Hin as ([cid pos] & EE & Hcp). injection EE as <- <-.
pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfr_fakestack _ _ _ _ _ WF)) (cid, pos) Hcp) as [C1 C2]. cbn [fst snd] in C1, C2.
pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
cbn [aeval fst snd] in Hi |- *. change (2 ^ 20) with 1048576 in *.
destruct IF as [IF0 IF1]. ceil.
assert (DV : fs_frame_bytes cid / 8 <= (fs_frame_bytes cid + 7) / 8) by (apply Z.div_le_mono; lia).
apply (rout_shadow_range (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid)).
- unfold kFakeFramesOff in *. lia.
- unfold kFakeFramesOff, kFakeStackSize, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *. destruct IF1 as [IL|[IH1 IH2]]; lia.
- apply (zdisjoint_sub _ _ _ _ DF); cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia.
- lia.
Qed.

(* T2 over the cut record: section 2's field proofs, the weak shadow in place of the strong one. *)
Lemma ARmcfR_rehide : forall ly S Hp (rd rd' : reader),
  Forall (zdisjoint (MAP, LEN)) (sec_extents ly S ++ static_extents ly) ->
  (forall r0 j, In r0 (as_junk B ly) -> 0 <= j < snd r0 -> rout PB PE (aeval B ly (fst r0) + j)) ->
  (forall a, rout PB PE a -> rd' a = rd a) ->
  ARmcfR B ly S Hp rd -> ARmcfR B ly S Hp rd'.
Proof using All.
intros ly S Hp rd rd' D JX AG M.
pose proof M as M0. pose proof (fp_zones_out ly S Hp rd M D) as FZ.
assert (FH : forall a, ly_F ly <= a < ly_F ly + 88 -> rout PB PE a).
{ intros a Ha. apply (out_owned ly (ly_F ly, kFakeStackSize) a (amr_layout _ _ _ _ _ M)); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeStackSize; lia]. }
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor; try assumption.
- exact (cells_move ly rd rd' _ AG (RL.const_cells_in_cf B (rout PB PE) ly S Hp rd M0 FZ) Xconst).
- exact (cells_move ly rd rd' _ AG (RL.acells_in_cf B (rout PB PE) ly S Hp rd M0 FZ FH) Xcells).
- intros c i v Hc Hi Hv k Hk. rewrite AG; [exact (Xfa c i v Hc Hi Hv k Hk)|].
  pose proof (wfr_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
  pose proof (region_in_prim ly c Xlay Hc) as (R1 & R2 & R3 & R4 & R5).
  apply (out_prim ly _ Xlay). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
- intros cid pos Hc Hpos. rewrite AG; [exact (Xflags cid pos Hc Hpos)|].
  pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr.
  apply (out_owned ly (ly_F ly, kFakeStackSize) _ Xlay); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia].
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. rewrite AG; [exact (H2 k Hk)|].
    pose proof (aso_cells _ Xsyms) as AC. apply rout_low. unfold d_tab_words, kLowMemEnd, SHADOW_OFF in *. lia.
  + intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
    assert (NB : depot_ids S <= 4097).
    { unfold depot_ids. pose proof (depot_len_bound _ _ Xuni (wfr_depot _ _ _ _ _ Xwf)) as DL. unfold DEPOT_MAX in DL. lia. }
    assert (OR : forall k, 0 <= k < 16 -> rout PB PE (ly_NB ly + 16 * id + k)).
    { intros k Hk. apply (out_owned ly (ly_NB ly, kNodesBlockSize) _ Xlay); [unfold owned_extents; cbn; tauto | cbn [fst snd]; unfold kNodesBlockSize; lia]. }
    split; intros k Hk; rewrite AG; auto; [apply OR; lia|].
    replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. apply OR. lia.
- intros g v Hg Hv. pose proof (ashadow_out ly S Hp rd g v M0 D Hv) as XG.
  destruct (Xshadow g v Hg Hv) as [HL|[HP HV]]; [left; rewrite (AG _ XG); exact HL|].
  right. split; [exact HP|]. rewrite (AG _ XG). exact HV.
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi.
  assert (XA : rout PB PE (shadow_of_addr SHADOW_OFF (fst r) + i)).
  { change (shadow_of_addr SHADOW_OFF (fst r)) with (shadow_addr (fst r)).
    destruct (RL.zshadow_range_facts_cf B ly S Hp rd r M0 Hr) as (Z1 & Z2 & Z3 & Z4 & _).
    assert (DR : zdisjoint (MAP, LEN) r).
    { unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
      - exact (proj1 (Forall_forall _ _) D _ ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; right; left; reflexivity)).
      - pose proof (proj1 (Forall_forall _ _) Ximg r ltac:(apply in_app_iff; right; exact Hr)) as [R1 R2].
        pose proof (proj1 (Forall_forall _ _) D (ly_img ly) ltac:(apply in_app_iff; right; unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as DI.
        destruct r as [lo len]. cbn [fst snd] in *. apply (zdisjoint_sub _ _ lo len DI); lia. }
    assert (snd r / 8 <= (snd r + 7) / 8) by (apply Z.div_le_mono; lia).
    destruct r as [lo len]. cbn [fst snd] in *. apply (rout_shadow_range lo len); [lia | lia | exact DR | lia]. }
  rewrite (AG _ XA). exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi).
- exact (vis_move ly rd rd' _ AG (junk_out ly S Hp rd M0 D JX) Xjunk).
- exact (vis_move ly rd rd' _ AG (areas_out ly S Hp rd M0 D) Xareas).
- exact (vis_move ly rd rd' _ AG (client_out ly S Hp rd M0 D) Xclient).
- apply Forall_forall. intros r Hr i Hi. rewrite AG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
  pose proof (aso_ialloc _ Xsyms) as [I1 I2]. pose proof (aso_cells _ Xsyms) as AC. apply rout_low.
  unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; unfold kLowMemEnd, SHADOW_OFF in *; lia.
- destruct Xown as [EXO _]. apply (YGcfInstBase.exh_cell_cf_frame B ly ly S S rd rd' Xexh); [intros c; reflexivity|].
  intros c Hc. apply AG. apply (out_prim ly _ Xlay). pose proof (lo_space_in _ Xlay) as [SP1 SP2].
  unfold YGcfImgRows.EXH_OFF_t in EXO. cbn [aoff aeval]. rewrite EXO. unfold kRegionInfoOff, kSpaceSize in *. lia.
- destruct Xown as [_ [HEO _]].
  assert (XB : forall a, errb_data_cf ly S <= a < errb_data_cf ly S + errb_cap_cf S -> rout PB PE a).
  { intros a. unfold errb_data_cf. destruct (last_cap_idx (st_secs S) 0 None) as [j|] eqn:E; intros Ha.
    - unfold xs_placed_cf, xs_cf in Xxs. rewrite E in Xxs. apply Forall_cons_iff in Xxs as [(_ & IAx & _) _]. cbn [fst snd] in IAx.
      exact (rout_inapp _ _ a IAx Ha).
    - exfalso. destruct (last_cap_none_rh _ _ _ E) as [_ HF]. unfold errb_cap_cf, errb_e in Ha. rewrite HF in Ha. cbn [last sm_len] in Ha. lia. }
  apply (RL.errb_cells_cf_frame_on B ly ly S S rd rd' Xerrb eq_refl eq_refl eq_refl eq_refl).
  + intros a Ha. apply AG. exact (RL.static_in_cf B (rout PB PE) ly S Hp rd a M0 FZ (HEO a Ha)).
  + intros a Ha HV. rewrite (AG _ (XB a Ha)). exact HV.
(* field round 3: Printf's two cells are owned static data (amr_pf_owned), so outside [PB, PE) *)
- apply (pf_cells_frame_cf B ly rd rd'); [|exact Xpf].
  intros a Ha. apply AG. exact (RL.static_in_cf B (rout PB PE) ly S Hp rd a M0 FZ (proj1 (proj1 Xpfo a Ha))).
Qed.
End T2.
End U.
End R.

Section V. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Variable ly : alayout.

(* The cut relation with the budget loosened by d bytes (ARcf_sl over ARmcfR). *)
Definition ARcfR_sl (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) (d : Z) : Prop :=
  ARmcfR B ly S Hp (aview segs (w_H W) mem) /\ ALedger_cf segs ly S md /\ abudget_sl_cf segs ly S W d /\ amwf md
  /\ ahs B ly S (w_H W) mem.

Lemma ARcfR_sl_of : forall S Hp W mem md d, 0 <= d -> ARcfR segs B ly S Hp W mem md -> ARcfR_sl S Hp W mem md d.
Proof.
intros S Hp W mem md d Hd (M & L & (LB & SA & BAND) & MW & HS).
unfold ARcfR_sl, abudget_sl_cf. refine (conj M (conj L (conj (conj _ (conj SA BAND)) (conj MW HS)))). lia.
Qed.

Lemma ARcfR_sl_mono : forall S Hp W mem md d d', d <= d' -> ARcfR_sl S Hp W mem md d -> ARcfR_sl S Hp W mem md d'.
Proof.
intros S Hp W mem md d d' Hd (M & L & (LB & SA & BAND) & MW & HS).
unfold ARcfR_sl, abudget_sl_cf. refine (conj M (conj L (conj (conj _ (conj SA BAND)) (conj MW HS)))). lia.
Qed.

(* T5 over the cut relation: ARcf_rehide's premises, in the same order, with ARcfR_sl at (S', W). *)
Theorem ARcfR_rehide : forall S' Hp (W : world segs) mem md MAP LEN r sm2
  (HO : H_off_segments segs (H_rehide (w_H W) (rh_lo MAP) (rh_hi MAP LEN)))
  (HA : A_wf (A_rehide (w_A W) (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN))),
  nth_error (st_secs S') r = Some sm2 -> sm_live sm2 = false -> 0 <= sm_size sm2 -> in_app MAP LEN ->
  MAP = ly_sec ly r -> LEN = sm_len sm2 ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly S' ++ static_extents ly) ->
  kMaxSize + kPage <= LEN ->
  (forall r0, In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
    exists sg, In sg segs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  In (shull (MAP, LEN)) (w_A W) ->
  ARcfR_sl S' Hp W mem md (rh_hi MAP LEN - rh_lo MAP) ->
  (forall a, rh_lo MAP <= a < rh_hi MAP LEN -> mem (w64 a) <> None) ->
  ARcfR segs B ly S' Hp (wrehide segs W (shull (MAP, LEN)) (rh_lo MAP) (rh_hi MAP LEN) HO HA (rh_H8 segs W MAP LEN)) mem md.
Proof.
intros S' Hp W mem md MAP LEN r sm2 HO HA _ _ _ HIA _ _ M1 HL JK HULL (M & L & BU & MW & HS) HMEM.
pose proof M1 as [HM D].
destruct (rh_geom MAP LEN HM HIA HL) as (H8 & HPB & HPE & HLT & SH).
assert (HL0 : 0 <= LEN) by (unfold kMaxSize, kPage in HL; lia).
pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (junk_rout segs B ly S' md MAP LEN L LO HM HIA HL JK) as JX.
unfold ARcfR. cbn [w_H w_A wrehide].
split; [|split; [exact L | split; [|split; [exact MW|]]]].
- apply (R.ARmcfR_rehide B MAP LEN (rh_lo MAP) (rh_hi MAP LEN) H8 HIA HL0 HPB HPE ly S' Hp (aview segs (w_H W) mem));
    [exact D | exact JX | | exact M].
  intros a Ha. exact (aview_rehide_out segs (w_H W) mem _ _ a Ha).
- exact (abudget_ok_rehide segs B ly S' W MAP LEN HO HA LO (amr_placed _ _ _ _ _ M) (RL.sec_extents_len_cf B ly S' Hp _ M) M1 HL HIA HULL BU).
- exact (ahs_rehide B ly S' (w_H W) mem _ _ HS HMEM).
Qed.
End V.
