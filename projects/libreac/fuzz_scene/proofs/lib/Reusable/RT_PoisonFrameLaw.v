(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene, shared by both images (lib/Reusable).

   AR is kept when a run writes ONLY inside the shadow of ONE fake-stack frame (and outside what AR owns).
   This is what __asan::PoisonShadow's post needs, and no field of AR_laws (lib/Reusable/YG0d.v:496-511) gives it:

   - Frame LIVE in S (__asan_stack_malloc_8's call, v = 0): its shadow bytes are aclient_byte
     (YG0n.v:230-235), so they are not aowned (YG0n.v:236-242), and AR_frame_law (YG0d.v:439-446) closes
     the case on its own.
   - Frame FREE in S (__asan_stack_free_8's tail jump, v = 0xf5, S = stack_free_state cid pos S0): the
     shadow bytes ARE aowned - the last disjunct of aowned (YG0n.v:241) holds every shadow byte of
     hm_zone / lm_zone, and aclient_byte asks for (cid, pos) in frames S, which a free frame is not in.
     AR_frame_law's premise (:442) therefore fails and the law does not apply.

   The fact is still true, because no field of ARm (YG0n.v:205-225) puts a value on the shadow of a fake
   frame: am_cells and am_const read cells of the image and of the fake-stack header (fs_cells, YG0n.v:100-102),
   am_shadow only the granules of heap chunks and of fa_poison_ranges (:181-187), am_zshadow only the real
   stack and the static zero-shadow ranges (:188-191), am_zero only the internal-alloc ranges, and am_junk,
   am_areas and am_client are presence only. ahz (YG0n.v:447-448) speaks of hfree granules, and the fake
   stack is in static_extents, so no granule of it is hfree. The proof below is that walk over the fields,
   in the shape of astack_malloc_law_ok (YG0t.v:662-843), from which it takes every separation lemma.

   One lemma serves both call sites: S is arbitrary, so the frame may be live or free in it.
   Owner: a Theorem Labs lane. Consumers: lib/A/RT_poison_shadow.v (asan) and lib/AU/RT_poison_shadow.v (asan-ubsan). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG05 YG0s YG0q YG0t.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section u.
Variable segs : list Segment.
Variable B : asyms.

(* The shadow bytes of fake frame (cid, pos): the only range outside AR's reach that the writes may touch. *)
Definition frame_shadow (ly : alayout) (cid pos : Z) : Z * Z :=
(shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).

Lemma AR_poison_frame : forall ly S W mem md mem' md' cid pos,
AR segs B ly S W mem md -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ in_zr a (frame_shadow ly cid pos) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
AR segs B ly S W mem' md'.
Proof.
intros ly S W mem md mem' md' cid pos (M & L & BUD & MW & HS) Hc Hp AGR VIS Hvm Hlz He HK.
unfold frame_shadow in AGR.
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
pose proof (am_layout _ _ _ _ M) as LO.
pose proof (frame_off_bounds cid pos Hc Hp) as (FO1 & FO2 & FO3 & FO4 & FO5 & FO6).
destruct (F_app ly LO) as (FH0 & FHZ & _). ceil.
assert (FR2 : ly_F ly + kFakeStackSize <= SHADOW_OFF \/ kHighMemBeg <= ly_F ly)
by (clear - FHZ; unfold kLowShadowBeg, SHADOW_OFF in *; lia).
assert (F64 : ly_F ly + kFakeStackSize < 2 ^ 64)
by (clear - FHZ CR; unfold kLowShadowBeg, ASAN_CEIL in *; lia).
assert (FSL : shadow_addr (ly_F ly + fs_frame_off cid pos) + fs_frame_bytes cid / 8 <= kHighMemBeg).
{ apply shadow_range_below; [unfold kFakeFramesOff in FO1; lia | lia |
clear - FHZ FO2 FO6 CR; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg in *; lia]. }
pose proof (proj1 (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(unfold kFakeFramesOff in FO1; lia))) as FSLO.
(* Every byte of the fake stack - its header cells, its flags - is far from the frame's shadow. *)
assert (FRNG : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> 0 <= a < 2 ^ 64)
by (intros a Ha; clear - Ha FH0 F64; lia).
assert (NFS : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize ->
~ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)).
{ intros a Ha. unfold in_zr, frame_addr. cbn [fst snd]. intros [R1 R2].
clear - Ha R1 R2 FR2 FSL FSLO. unfold SHADOW_OFF, kHighMemBeg, kFakeStackSize in *. lia. }
(* The cells, the free arrays, the depot and the internal allocator are all nf: outside the fake stack and
   outside its shadow (YG0t.v:20-23), so AGR applies to them. *)
assert (AGN : forall a, aowned B ly S a -> nf ly a -> rd' a = rd a).
{ intros a Ha [Hn Hb]. apply AGR; [| exact Ha |].
- pose proof (AR_owned_low_law_ok segs B ly S W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha).
  ceil. unfold ASAN_CEIL in *. lia.
- unfold in_zr, frame_addr. cbn [fst snd]. intros [R1 R2].
  pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. apply Z.mod_divide in FAL as [qf Hqf]; [|lia].
  pose proof FO3 as FO3'. apply Z.mod_divide in FO3' as [qo Hqo]; [|lia].
  pose proof FO5 as FO5'. apply Z.mod_divide in FO5' as [qb Hqb]; [|lia].
  assert (E1 : (ly_F ly + fs_frame_off cid pos) / 8 = qf * 512 + qo * 8)
  by (rewrite Hqf, Hqo; replace (qf * 4096 + qo * 64) with ((qf * 512 + qo * 8) * 8) by lia; apply Z_div_mult; lia).
  assert (E2 : ly_F ly / 8 = qf * 512)
  by (rewrite Hqf; replace (qf * 4096) with ((qf * 512) * 8) by lia; apply Z_div_mult; lia).
  assert (E3 : fs_frame_bytes cid / 8 = qb * 8)
  by (rewrite Hqb; replace (qb * 64) with ((qb * 8) * 8) by lia; apply Z_div_mult; lia).
  unfold shadow_addr in Hb, R1, R2. rewrite E1 in R1, R2. rewrite E3 in R2. rewrite E2 in Hb.
  change (kFakeStackSize / 8) with 1446400 in Hb.
  clear - Hb R1 R2 Hqo Hqb FO2 FO6 FO1 Hc. unfold kFakeFramesOff, kFakeStackSize in *. nia. }
(* ahz: a granule outside the static extents is outside the fake stack, so its shadow byte is not written. *)
assert (AGF : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> w_H W (w64 (shadow_addr g)) = false ->
rd' (shadow_addr g) = rd (shadow_addr g)).
{ intros g Hg HA HFg _. pose proof HA as [HA0 HAZ].
pose proof (shadow_addr_bounds g ltac:(lia)) as [SB1 SB2'].
pose proof (SB2' ltac:(clear - HAZ CR; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg in *; lia)) as SB2.
pose proof (proj1 (Forall_forall _ _) HFg (ly_F ly, kFakeStackSize)
ltac:(unfold hfree; rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as XF.
cbn [fst snd] in XF.
apply AGR; [clear - SB1 SB2; unfold SHADOW_OFF, kHighMemBeg in *; lia
| eapply hfree_shadow_owned; [exact M | exact Hg | exact HA | exact HFg] |].
unfold in_zr, frame_addr. cbn [fst snd]. intros [R1 R2].
apply Z.mod_divide in Hg as [q Hq]; [|lia].
assert (F8 : (ly_F ly + fs_frame_off cid pos) mod 8 = 0).
{ pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. apply Z.mod_divide; [lia|].
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. apply Z.mod_divide in FO3 as [qo Hqo]; [|lia].
exists (qf * 512 + qo * 8). lia. }
apply Z.mod_divide in F8 as [qa Hqa]; [|lia]. apply Z.mod_divide in FO5 as [qb Hqb]; [|lia].
unfold shadow_addr, SHADOW_OFF in R1, R2. rewrite Hq, Hqa, Hqb in *. rewrite !Z.div_mul in R1, R2 by lia.
replace (qb * 64 / 8) with (qb * 8) in R2 by (symmetry; replace (qb * 64) with (qb * 8 * 8) by lia; apply Z.div_mul; lia).
unfold kFakeFramesOff, kFakeStackSize in *. nia. }
split; [|split; [exact (ALedger_same segs ly S md md' L Hvm Hlz He) | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer_grow segs B ly S S (w_H W) mem mem' (al_img_env segs ly S md LO L) HS VIS HK (fun a _ C => C) eq_refl AGF)]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg].
constructor; try assumption.
-   exact (Forall_cell_holds_agree_nf B ly S rd rd' _ AGN (const_cells_owned B ly S rd M0) (const_cells_nf B ly S rd M0) Xconst).
-
replace (acells B ly S) with (acells B ly (set_fs (st_fs S) S)) by (destruct S; reflexivity).
apply (am_cells_set_fs B ly S rd rd' (st_fs S) M0 AGN).
pose proof Xcells as XC. unfold acells in XC. rewrite (fs_cells_split S) in XC.
do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _]. apply Forall_app in XF as [_ XH].
pose proof (acells_owned B ly S rd M0) as OW. unfold acells in OW. rewrite (fs_cells_split S) in OW.
do 5 (apply Forall_app in OW as [_ OW]). apply Forall_app in OW as [OWF _]. apply Forall_app in OWF as [_ OWH].
apply Forall_forall. intros c Hcin.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) XH c Hcin)|]. intros kk Hkk.
assert (HA : ly_F ly <= aeval B ly (c_at c) + kk < ly_F ly + kFakeStackSize).
{ clear - Hcin Hkk. unfold fs_hints in Hcin. apply in_map_iff in Hcin as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih.
cbn [c_at c_w z8 c8 aeval aoff fst snd] in Hkk |- *. unfold kFakeStackSize. lia. }
apply AGR; [apply FRNG; exact HA | exact (proj1 (Forall_forall _ _) OWH c Hcin kk Hkk) | apply NFS; exact HA].
-
intros c i v Hc' Hi Hv k Hk.
pose proof (wf_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wr_fa_len _ _ _ _ _ _ CLS) as FL.
pose proof (wr_fa_bound _ _ _ _ _ _ CLS) as FB'.
rewrite AGN; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa; [exact M0 | exact Hc' | lia] |].
apply (nf_prim ly _ Xlay). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _).
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ Xlay) as [S1 S2]. rewrite region_off_eq in * by lia.
unfold kPrimResvSize, kSpaceSize in *. nia.
-
intros c q Hc' Hq. pose proof (flag_off_bounds c q Hc' Hq) as FB''.
rewrite AGR; [exact (Xflags c q Hc' Hq)
| apply FRNG; clear - FB''; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia
| eapply own_F_low; [exact M0 | clear - FB''; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *; lia]
| apply NFS; clear - FB''; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia].
-
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk.
rewrite AGN; [exact (H2 k Hk)
| eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |].
eapply (nf_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ unfold depot_ids. pose proof (wf_depot _ _ _ _ _ Xwf) as [ND' INC]. pose proof (NoDup_incl_length ND' INC).
destruct Xuni as (U1 & _). unfold DEPOT_MAX in U1. lia. }
assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)).
{ intros k Hk. apply AGN.
- eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
- eapply (nf_core B ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. rewrite OR by lia.
replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (H3 k Hk).
-
intros g v Hg Hv0.
pose proof (ashadow_low B ly S rd g v M0 Hv0) as SL.
rewrite AGR; [exact (Xshadow g v Hg Hv0)
| clear - SL; unfold SHADOW_OFF, kHighMemBeg in *; lia
| eapply ashadow_owned; [exact M0 | exact Hv0]
| exact (ashadow_not_frame_shadow B ly S rd g v cid pos M0 Hv0 Hc Hp)].
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr.
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0.
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
pose proof (zshadow_low B ly S rd r i M0 Hr Hi) as SL.
rewrite AGR; [exact Z0
| clear - SL; unfold SHADOW_OFF, kHighMemBeg in *; lia
| eapply own_shadow_zero; [exact M0 | exact Hr | exact Hi]
| exact (zshadow_not_frame_shadow B ly S rd r i cid pos M0 Hr Hi Hc Hp)].
- eapply Forall_range_vis_keep; [exact VIS | exact Xjunk].
- eapply Forall_range_vis_keep; [exact VIS | exact Xareas].
- eapply Forall_range_vis_keep; [exact VIS | exact Xclient].
-
apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
assert (RG : forall z, as_ialloc_lo B <= z < as_ialloc_hi B -> rd' z = rd z).
{ intros z Hz. apply AGN.
- eapply (own_area B ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
- eapply (nf_area B ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia]. }
rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
Qed.
End u.
End j.
