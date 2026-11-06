(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from commit 7fb5e1d920f1a960ba591aa28cade9497d873d3c,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainRL.v, sha256 453c99b06ab44767c00f08e915fd22554341dfea7f23e001cab979959c1e9478 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree (lane W's AllocG / DeallocG / DMspec / DMiface / ImgBaseDG / DGif0, the F1 core's
   YGcfRehidePost / YGcfRecStep, and the per-image cf files of this carry) name lib/B; a sentence is split at a directory
   change, the module order kept.
*)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the lemma library of the drain's
   CUT relation YGcfInstDrainR.ARcfR, in Module RL.
   rule 24: no function proved (kind: relation-level facts of the instance's cut relation; mechanical twin of the
   ARcf library).

   ARcfR is YG0ncf.ARcf with YG03cf.WfR_cf for Wf_cf (YGcfInstDrainR.v).  None of the ARcf library's owned-set, chunk,
   frame and shadow facts reads wfc_compl0, the one clause WfR_cf lacks, so each is restated here over ARcfR with the
   same script, by these substitutions and nothing else: ARmcf -> ARmcfR, amc_X -> amr_X (amc_wf -> amr_wfr),
   wfc_X -> wfr_X, WfP_cf -> WfR_cf, ARcf -> ARcfR, YG01cf.mapped_bound_cf -> YG03cf.mapped_bound_r_cf.  Sources, at
   commit 89e87f66e02 (taken by path from commit a0fed4266a1b):
   - the fourteen laws' statements, YG0dcf.v:324-414 (Definitions AR_*_law_cf over ARcfR);
   - YG0scf.v:30-626 (helpers and the twelve non-shadow laws' proofs);
   - YG0qcf.v:30-716 (the owned-set lemmas and AR_frame_law_ok_cf);
   - YG0tcf.v:40-487 (fp_zones and the *_in_cf family, the zero-shadow and shadow-address zone facts).
   Inside Module RL every name is the source's, so RL.X is the ARcfR twin of X.  Image-free and event-free (no event-count
   term, no event regime, no event-keyed budget appears). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK15 YK0j YK18 YG05 YG05cf YG0t.
From stdpp Require Import bitvector.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG03cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstDrainR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* YGcfInstDrainR now Requires YGcfInstBase, whose closure leaves lia's euclidean-division flag off; this file's
   proofs were written with it on (the load order before that Require).  Restored here, for this file only. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module RL.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The laws' statements over ARcfR (YG0dcf.v:501-590).                                                               *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.
Definition AR_blocks_law_cf : Prop :=
forall ly S Hp W mem md p n,
ARcfR segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\
0 <= n < cf_malloc_max.
Definition AR_shadow_law_cf : Prop :=
forall ly S Hp W mem md p n,
ARcfR segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF (p + hd_skip Hp p) (req_size n - hd_skip Hp p) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
Definition AR_zshadow_law_cf : Prop :=
forall ly S Hp W mem md r,
ARcfR segs B ly S Hp W mem md -> In r (zero_shadow_ranges B ly) ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Definition AR_frame_law_cf : Prop :=
forall ly S Hp W mem md mem' md',
ARcfR segs B ly S Hp W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcfR segs B ly S Hp W mem' md'.
Definition AR_frames_law_cf : Prop :=
forall ly S Hp W mem md cid pos,
ARcfR segs B ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i) /\
~ aowned B ly S (shadow_addr (frame_addr ly cid pos) + i)).
Definition AR_flag_law_cf : Prop :=
forall ly S Hp (W : world segs) mem md cid pos,
ARcfR segs B ly S Hp W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.
Definition AR_const_law_cf : Prop :=
forall ly S Hp W mem md,
ARcfR segs B ly S Hp W mem md ->
rdword (aview segs (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
rd32 (aview segs (w_H W) mem) (as_uar_cell B) 1 /\
rdword (aview segs (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
rdword (aview segs (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B).
Definition AR_stack_law_cf : Prop :=
forall ly S Hp W mem md a,
ARcfR segs B ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Definition AR_owned_low_law_cf : Prop :=
forall ly S Hp W mem md a, ARcfR segs B ly S Hp W mem md -> aowned B ly S a -> 0 <= a < alloc_ceiling.
Definition AR_owned_image_law_cf : Prop :=
forall ly S Hp W mem md a, ARcfR segs B ly S Hp W mem md -> in_img segs a ->
(aowned B ly S a <-> Exists (in_zr a) (as_owned_static B)).
Definition AR_sep_law_cf : Prop :=
forall ly S Hp W mem md, ARcfR segs B ly S Hp W mem md ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)
++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)) /\
Forall (fun f => 4096 <= frame_addr ly (fst f) (snd f) /\ frame_addr ly (fst f) (snd f) + fs_frame_bytes (fst f) <= alloc_ceiling) (frames S).
Definition AR_layout_law_cf : Prop :=
forall ly S Hp W mem md ly',
ARcfR segs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
ablocks B ly' S = ablocks B ly S /\ (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) /\
(forall a, aowned B ly' S a <-> aowned B ly S a).
Definition AR_wle_law_cf : Prop :=
forall ly S Hp W W' mem md,
ARcfR segs B ly S Hp W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) ->
A_bytes (w_A W') <= abudget_cf S -> ARcfR segs B ly S Hp W' mem md.
Definition AR_client_img_law_cf : Prop :=
forall ly S Hp W mem md a, ARcfR segs B ly S Hp W mem md ->
((exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
(exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)) ->
~ in_zr a (ly_img ly) /\ ~ in_img segs a.

(* The law AR_laws_cf lacked, VERBATIM from h-rw-man-5's YGcfHp.v:63-76 (29c8b46b1cef):
   cgif's AR_frame_law (YG0d.v:445) with two changes: the owned bytes that may change are
   the hidden-head shadow bytes of Hp and Hp', and each such byte that shadow_ok_cf governs
   takes the value shadow_ok_cf at Hp' demands; the result is ARcfR at Hp', given that every
   base in Hp' is live. *)
Definition AR_head_frame_law_cf : Prop :=
forall ly S Hp Hp' W mem md mem' md',
ARcfR segs B ly S Hp W mem md ->
Forall (hp_live_cf B ly S) Hp' ->
(forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v -> in_head Hp g = true \/ in_head Hp' g = true ->
aview segs (w_H W) mem' (shadow_addr g) = Some (if in_head Hp' g then shUserPoison else v)) ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ hd_shadow (Hp ++ Hp') a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcfR segs B ly S Hp' W mem' md'.
End J.
End G.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YG0scf.v:30-626 over ARcfR.                                                                                        *)
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

(* ---------------------------------------------------------------------------- *)
(* cf forms of cgif helpers that live outside YG0s.v.                            *)
(* YG07.v:174, with the class window re-based on wrc_mapped_bound.               *)
Lemma prim_chunk_off_cf : forall U pp cc bb s k off, WfR_cf U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim off ->
let c := prim_class off in
1 <= c <= 30 /\ c = chunk_class (ck_req k) /\ from_primary (ck_req k) = true /\ 0 <= ck_req k /\
0 <= off - region_off c < kFreeArrayOffset /\ (off - region_off c) mod class_size c = 0.
Proof.
intros U pp cc bb s k off W Hk Hb c.
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hk) as [CKn CK]. rewrite Hb in CK. destruct CK as (CKp & CKc & CKo).
pose proof (primary_geometry (ck_req k) ltac:(lia) CKp) as (Gc & _).
assert (Hc : 1 <= c <= 30) by (subst c; rewrite CKc; exact Gc).
pose proof (In_chunk_offs s k off Hk Hb) as Hin. fold c in Hin.
pose proof (wfr_classes _ _ _ _ _ W c ltac:(lia)) as CL.
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) (off - region_off c)) as E.
specialize (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin)).
pose proof (wrc_alloc _ _ _ _ _ _ CL). pose proof (mapped_bound_r_cf U pp cc bb s c W ltac:(lia)).
subst c. destruct E as [E1 E2]. splits; try lia; try assumption.
Qed.

(* YG0n.v:508. *)
(* The buffer-cell keep for a step that drops presence somewhere (the secondary recycle's munmap): presence is
   needed on the buffer's data range only, which xs_placed_cf keeps apart from every secondary extent, the dead
   map included.  Base's errb_cells_cf_frame asks for presence everywhere; this is the same proof with the weaker
   premise (lane F2b, for CfF2bRChunk's rc_sec_step_cf). *)
Lemma errb_cells_cf_frame_on : forall B ly ly' S S' (rd rd' : reader),
  errb_cells_cf B ly S rd ->
  errb_mapped_cf S' = errb_mapped_cf S -> errb_data_cf ly' S' = errb_data_cf ly S ->
  errb_cap_cf S' = errb_cap_cf S -> errb_size_cf S' = errb_size_cf S ->
  (forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> rd' a = rd a) ->
  (forall a, errb_data_cf ly S <= a < errb_data_cf ly S + errb_cap_cf S -> rd a <> None -> rd' a <> None) ->
  errb_cells_cf B ly' S' rd'.
Proof.
intros B ly ly' S S' rd rd' (P & M & D & C & SZ & V & LE & MD) EM ED EC EZ F VIS.
unfold errb_cells_cf. rewrite EM, ED, EC, EZ.
assert (CK : forall (A v : Z), cf_errbuf_obj <= A -> A + 8 <= cf_errbuf_obj + 56 ->
  cell_holds B ly rd (z8 (ANum A) v) -> cell_holds B ly' rd' (z8 (ANum A) v)).
{ intros A v HA HA' H. unfold cell_holds in *. cbn [c_at c_w c_val z8 c8] in *.
  intros k Hk. specialize (H k Hk).
  change (aeval B ly' (ANum A)) with A. change (aeval B ly (ANum A)) with A in H.
  change (aeval B ly' (ANum v)) with v. change (aeval B ly (ANum v)) with v in H.
  assert (Hk' : 0 <= Z.of_nat k < 8) by (split; [apply Nat2Z.is_nonneg | apply (Nat2Z.inj_lt k 8); exact Hk]).
  rewrite F; [exact H|]. unfold aeval in *. cbn in *. YM03.lf_lia_orig. }
split; [apply (CK cf_errbuf_obj); [YM03.lf_lia_orig | YM03.lf_lia_orig | exact P]|].
split; [apply (CK (cf_errbuf_obj + 16)); [YM03.lf_lia_orig | YM03.lf_lia_orig | exact M]|].
split; [apply (CK (cf_errbuf_obj + 32)); [YM03.lf_lia_orig | YM03.lf_lia_orig | exact D]|].
split; [apply (CK (cf_errbuf_obj + 40)); [YM03.lf_lia_orig | YM03.lf_lia_orig | exact C]|].
split; [apply (CK (cf_errbuf_obj + 48)); [YM03.lf_lia_orig | YM03.lf_lia_orig | exact SZ]|].
split; [intros a Ha; exact (VIS a Ha (V a Ha))|]. split; [exact LE | exact MD].
Qed.

(* field round 2: the two machine cells transfer along rd_ext, since every byte they pin is a Some. *)
Lemma exh_cell_cf_ext : forall B ly S (rd rd' : reader), rd_ext rd rd' -> exh_cell_cf B ly S rd -> exh_cell_cf B ly S rd'.
Proof.
intros B ly S rd rd' Hx [H1 H2]. split; [|exact H2]. intros c Hc i Hi. apply Hx. exact (H1 c Hc i Hi).
Qed.

Lemma errb_cells_cf_ext : forall B ly S (rd rd' : reader), rd_ext rd rd' -> errb_cells_cf B ly S rd -> errb_cells_cf B ly S rd'.
Proof.
intros B ly S rd rd' Hx (C1 & C2 & C3 & C4 & C5 & P & M1 & M2).
split; [intros i Hi; apply Hx; exact (C1 i Hi)|].
split; [intros i Hi; apply Hx; exact (C2 i Hi)|].
split; [intros i Hi; apply Hx; exact (C3 i Hi)|].
split; [intros i Hi; apply Hx; exact (C4 i Hi)|].
split; [intros i Hi; apply Hx; exact (C5 i Hi)|].
split; [|exact (conj M1 M2)].
intros a Ha. destruct (rd a) as [w|] eqn:E; [rewrite (Hx _ w E); discriminate | exfalso; exact (P a Ha E)].
Qed.

Lemma ARmcf_ext : forall B ly S Hp rd rd', rd_ext rd rd' -> ARmcfR B ly S Hp rd -> ARmcfR B ly S Hp rd'.
Proof.
intros B ly S HG rd rd' Hx M.
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Xsimg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor; try assumption.
(* field round 2's three fields and field round 3's two cells, closed first so the bullets below keep their order *)
all: try (first [ exact Xown | exact (exh_cell_cf_ext B ly S rd rd' Hx Xexh)
                | exact (errb_cells_cf_ext B ly S rd rd' Hx Xerrb) | exact (pf_cells_cf_ext B ly rd rd' Hx Xpf) ]).
- eapply Forall_cell_holds_ext; eassumption.
- eapply Forall_cell_holds_ext; eassumption.
- intros c i v Hc Hi Hv k Hk. apply Hx. exact (Xfa c i v Hc Hi Hv k Hk).
- intros cid pos Hc Hq. apply Hx. exact (Xflags cid pos Hc Hq).
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. apply Hx, H2, Hk.
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|]. split; intros k Hk; apply Hx; auto.
- intros g v Hg Hv. destruct (Xshadow g v Hg Hv) as [HL|[HP HV]]; [left; apply Hx; exact HL|].
right. split; [exact HP|]. intros HN. apply HV. destruct (rd (shadow_addr g)) as [w|] eqn:E; [|reflexivity].
rewrite (Hx _ w E) in HN. discriminate.
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr.
eapply zero_shadow_ext; [exact Hx|]. exact (proj1 (Forall_forall _ _) Xzsh r Hr).
- eapply Forall_range_vis_ext; eassumption.
- eapply Forall_range_vis_ext; eassumption.
- eapply Forall_range_vis_ext; eassumption.
- apply Forall_forall. intros r Hr i Hi. apply Hx. exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi).
Qed.

Section m.
Variable segs : list Segment.
Variable B : asyms.

(* YG0n.v:526; the band (abudget_ok_cf's third conjunct) passes by hsub (cls1_band_vis_hsub_cf). *)
Lemma AR_wle_cf : forall ly S Hp W W' mem md,
ARcfR segs B ly S Hp W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) -> A_bytes (w_A W') <= abudget_cf S ->
ARcfR segs B ly S Hp W' mem md.
Proof.
intros ly S HG W W' mem md (M & L & (_ & PIN & BAND) & MW & HS) Hs HI Hb.
split; [|split; [exact L | split; [exact (conj Hb (conj (asecA_transfer ly ly S S _ _ PIN (fun e He => He) HI)
(cls1_band_vis_hsub_cf ly _ _ Hs BAND))) |
split; [exact MW | exact (ahs_hsub B ly S _ _ mem Hs HS)]]]].
eapply ARmcf_ext; [|exact M]. apply aview_ext; [apply w_Hoff | exact Hs].
Qed.

(* ---------------------------------------------------------------------------- *)
(* The helpers of YG0s.v, in its order.                                          *)
Lemma sec_extents_len_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (fun e => 4096 < snd e) (sec_extents ly S).
Proof.
intros ly S HG rd M. pose proof (wfr_chunks _ _ _ _ _ (amr_wfr _ _ _ _ _ M)) as CK. unfold sec_extents.
apply Forall_forall. intros e He. apply in_flat_map in He as (k & Hk & He).
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn C]. destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He.
cbn [snd]. destruct C as (Hfp & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (G1 & G2 & G3 & G4 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)). unfold kPage, kSecRz in *. lia.
Qed.
Lemma owned_shadow_ranges_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd ->
Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kHighMemEnd) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
intros ly S HG rd M. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_placed _ _ _ _ _ M) as [PL _]. pose proof (amr_syms _ _ _ _ _ M) as SY.
pose proof (lo_top _ LO) as TOP. pose proof (lo_app _ LO) as HI. pose proof (lo_img _ LO) as IMG. pose proof ASAN_CEIL_range as [CR _].
unfold kHighMemEnd, kHighMemBeg, kLowMemEnd, kImgLo, kImgEnd in *.
apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|constructor; [unfold hm_zone; cbn; unfold kHighMemBeg, kHighMemEnd; lia | constructor; [unfold lm_zone; cbn; unfold kLowMemEnd, kHighMemEnd; lia | constructor]]]]]].
- unfold static_extents. apply Forall_app. split.
+ apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) HI e He) as [H1 H2].
assert (Hs : 0 <= snd e).
{ unfold owned_extents in He. unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize in He.
repeat (destruct He as [<-|He]; [cbn; lia|]). destruct He. }
unfold kLowShadowBeg, kHighMemBeg in H2. lia.
+ constructor; [cbn; lia | constructor; [cbn [fst snd]; unfold page_aligned in IMG; lia | constructor]].
- apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & [H1 H2] & H3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_len_cf ly S HG rd M) e He) as H4. cbv beta in H4. unfold kLowShadowBeg, kHighMemBeg in *. lia.
- unfold zero_shadow_ranges. constructor; [cbn; lia|]. eapply Forall_impl; [|exact (aso_zshadow _ SY)]. cbv beta. intros r Hr. unfold kLowMemEnd in Hr. lia.
- eapply Forall_impl; [|exact (aso_static _ SY)]. cbv beta. intros r Hr. unfold kImgEnd in Hr. lia.
Qed.
Lemma owned_sec_bound_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> Exists (in_zr a) (sec_extents ly S) ->
app_addr a /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly).
Proof.
intros ly S HG rd a M H. apply Exists_exists in H as (e & He & [H1 H2]). pose proof (amr_placed _ _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & K & K3).
pose proof (pairwise_In zdisjoint _ e (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents; apply in_app_iff; right; left; reflexivity)) as D.
pose proof (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as D2.
unfold zdisjoint, in_zr in *. cbn [fst snd] in D. split; [exact (in_app_addr _ _ _ K (conj H1 H2)) | lia].
Qed.
Lemma owned_shadow_bound_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd ->
Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]) ->
SHADOW_OFF <= a < kHighMemBeg.
Proof.
intros ly S HG rd a M H. apply Exists_exists in H as (r & Hr & [H1 H2]). cbn [fst snd] in H1, H2.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges_cf ly S HG rd M) r Hr) as (K1 & K2 & K3).
pose proof (shadow_addr_bounds (fst r) K1) as [P1 _].
unfold shadow_addr, SHADOW_OFF, kHighMemEnd, kHighMemBeg in *.
assert (fst r / 8 + (snd r + 7) / 8 <= 17592186044416); [|lia].
assert (L : (fst r + snd r + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia).
change (140737488355335 / 8) with 17592186044416 in L.
assert (fst r / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|].
pose proof (Z.mul_div_le (fst r) 8 ltac:(lia)). pose proof (Z.mul_div_le (snd r + 7) 8 ltac:(lia)). lia.
Qed.
(* CHANGED beyond the substitutions: cgif's `rg_holes (reg S c) = []` is false here, since a cf class may
   carry the one sentinel hole (EXH_HOLE, 0) (wrc_holes, YG01cf.v). *)
Lemma am_noholes_cf : forall ly S Hp rd c, ARmcfR B ly S Hp rd -> 1 <= c <= 31 ->
Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes (reg S c)).
Proof. intros ly S HG rd c M Hc. exact (proj1 (wrc_holes _ _ _ _ _ _ (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c Hc))). Qed.
(* The sentinel has length 0, so it covers no address and the cgif statement stands. *)
Lemma wf_no_prim_hole_cf : forall U pp cc bb s ly a, WfR_cf U pp cc bb s -> ~ prim_hole_at ly s a.
Proof.
intros U pp cc bb s ly a W (c & h & Hc & Hin & Hz).
pose proof (proj1 (Forall_forall _ _) (proj1 (wrc_holes _ _ _ _ _ _ (wfr_classes _ _ _ _ _ W c Hc))) h Hin) as Eh.
cbv beta in Eh. subst h. unfold in_zr in Hz. cbn [fst snd] in Hz. lia.
Qed.
Lemma am_no_prim_hole_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> ~ prim_hole_at ly S a.
Proof. intros ly S HG rd a M. exact (wf_no_prim_hole_cf _ _ _ _ _ ly a (amr_wfr _ _ _ _ _ M)). Qed.
Lemma al_prim_covered_cf : forall ly S Hp rd md a, ARmcfR B ly S Hp rd -> ALedger_cf segs ly S md -> ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
exists e, In e (vm_maps (m_vmmaps md)) /\ bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
intros ly S HG rd md a M L Ha. destruct (alc_prim _ _ _ _ L) as (pieces & (_ & _ & COV) & PCS).
pose proof (proj2 (COV a Ha) (am_no_prim_hole_cf ly S HG rd a M)) as Hx.
apply Exists_exists in Hx as (q & Hq & HQ). destruct (proj1 (PCS q) Hq) as (Hin & Hpos & Hlo & Hhi).
pose proof (lo_high _ (amr_layout _ _ _ _ _ M)) as [K1 K2].
cbn [fst snd] in K1, K2.
exists (wiv q). split; [exact Hin|]. unfold wiv, w64. cbn [fst snd]. destruct HQ as [Q1 Q2].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); ceil; unfold in_high, kPrimResvSize, ASAN_CEIL, kHighMemBeg in *; lia). lia.
Qed.
(* CHANGED beyond the substitutions: the request bound is chunk_ok_cf's cf_malloc_max, and the class bound is
   wrc_mapped_bound's kFreeArrayOffset (3.5 GiB, still below a region's 2 ^ 32), not cgif's 2 ^ 31. The
   conjuncts are cgif's, in cgif's order, so cgif's destruct patterns carry over. *)
Definition cfacts_cf (ly : alayout) (S : astate) (k : chunk) : Prop :=
in_app (ck_base B ly k) (ck_extent k) /\ ck_base B ly k + ck_extent k <= ASAN_CEIL /\ ck_base B ly k mod 16 = 0 /\
sptr_addr B ly (ck_user k) = ck_base B ly k + ck_rz k /\ 16 <= ck_rz k <= 2048 /\ ck_rz k mod 16 = 0 /\
0 <= ck_req k < cf_malloc_max /\ ck_rz k + req_size (ck_req k) <= ck_extent k /\
match ck_beg k with
| PPrim off => let c := prim_class off in let x := off - region_off c in
1 <= c <= 30 /\ from_primary (ck_req k) = true /\ chunk_class (ck_req k) = c /\ ck_extent k = class_size c /\
ck_base B ly k = region_base ly c + x /\ 0 <= x /\ x mod class_size c = 0 /\ x + class_size c <= rg_alloc_user (reg S c) /\
rg_alloc_user (reg S c) <= rg_mapped_user (reg S c) <= kFreeArrayOffset
| PSec r o => o = kPage /\ from_primary (ck_req k) = false /\ ck_base B ly k = ly_sec ly r + kPage /\
ck_extent k = sec_map_size (ck_req k) - kPage /\ In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S) /\
page_aligned (ly_sec ly r) /\ (r < length (st_secs S))%nat
| _ => False
end.
Lemma chunk_facts_cf : forall ly S Hp rd k, ARmcfR B ly S Hp rd -> In k (st_chunks S) -> cfacts_cf ly S k.
Proof.
intros ly S HG rd k M Hk. pose proof (amr_wfr _ _ _ _ _ M) as W. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_placed _ _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hk) as [Hn CK].
pose proof (rz_size_bounds (ck_req k)) as [RZ1 RZ2]. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
unfold cfacts_cf, ck_base, ck_user, ck_rz.
destruct (ck_beg k) as [|off|r o|c p] eqn:Eb; try solve [destruct CK].
-
destruct CK as (Hfp & Hc & Hoff).
pose proof (prim_chunk_off_cf (as_universe B) 0 0 0 S k off W Hk Eb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
set (c := prim_class off) in *. set (x := off - region_off c) in *.
pose proof (primary_geometry (ck_req k) ltac:(lia) Hfp) as (P1 & P2 & P3 & P4 & P5). rewrite <- G2 in P2, P3, P4, P5.
pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & _).
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wfr_classes _ _ _ _ _ W c ltac:(lia)) as CL. pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S c W ltac:(lia)) as MB. unfold kFreeArrayOffset in *.
assert (XA : 0 <= x < rg_alloc_user (reg S c)).
{ pose proof (In_chunk_offs S k off Hk Eb) as IN. fold c x in IN.
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x) as E.
exact (proj1 (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact IN))). }
assert (XS : x + class_size c <= rg_alloc_user (reg S c)).
{ pose proof G6 as G6'. apply Z.mod_divide in G6' as [qx Hqx]; [|lia]. pose proof A2 as A2'. apply Z.mod_divide in A2' as [qa Hqa]; [|lia].
assert (Hq : qx < qa) by (apply (Z.mul_lt_mono_pos_r (class_size c)); lia).
pose proof (Z.mul_le_mono_nonneg_r (qx + 1) qa (class_size c) ltac:(lia) ltac:(lia)). lia. }
assert (EXT : ck_extent k = class_size c) by (unfold ck_extent; rewrite Hfp, G2; reflexivity).
assert (BASE : sptr_addr B ly (PPrim off) = region_base ly c + x).
{ unfold sptr_addr, region_base. cbn. subst x. lia. }
rewrite EXT, BASE. cbn [padd]. unfold sptr_addr at 1. cbn [sptr_exp aeval].
assert (XM16 : x mod 16 = 0).
{ apply Z.mod_divide in G6 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [q' Hq']; [|lia]. apply Z.mod_divide; [lia|]. exists (q * (q' * 2)). lia. }
ceil; unfold ASAN_CEIL, kHighMemBeg, kMaxSize in *.
split. { apply in_high_app. unfold in_high, ASAN_CEIL, kHighMemBeg in *. split; [clear - R4 XA; lia | clear - XS A1 MB R5; lia]. }
splits; try lia; try assumption; try (unfold region_base; subst x; lia).
all: apply Z.mod_divide; [lia|]; apply Z.mod_divide in R3 as [q Hq]; [|lia]; apply Z.mod_divide in XM16 as [q' Hq']; [|lia]; exists (q * 4096 + q'); lia.
-
destruct CK as (Hfp & -> & sm & Hsm & Hlive & Hsz & Hlen).
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (S1 & S2 & S3 & S4 & S5 & S6).
assert (INE : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S)).
{ unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Eb. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) PL _ INE) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
assert (EXT : ck_extent k = sec_map_size (ck_req k) - kPage) by (unfold ck_extent; rewrite Hfp; reflexivity).
rewrite EXT. unfold sptr_addr. cbn [sptr_exp aeval padd]. ceil; unfold page_aligned, kPage, kSecRz, ASAN_CEIL, kHighMemBeg in *.
split; [eapply in_app_sub; [exact (conj I1 I2) | lia | lia | lia] |].
assert (I2' : ly_sec ly r + sec_map_size (ck_req k) <= alloc_ceiling) by exact I3.
splits; try lia; try assumption; try reflexivity; try (eapply nth_error_lt; exact Hsm).
all: apply Z.mod_divide; [lia|]; apply Z.mod_divide in PA as [q Hq]; [|lia]; exists (q * 256 + 256); lia.
Qed.
Lemma chunk_apart_cf : forall ly S Hp rd k a, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ in_zr a (ly_img ly) /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof.
intros ly S HG rd k a M Hk Ha. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; lia])) as (_ & NS & NI). tauto.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
destruct (owned_sec_bound_cf ly S HG _ a M ltac:(apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req k)); split; [exact Gin | unfold in_zr; cbn [fst snd]; unfold kPage in *; lia])) as (_ & NS & NI). tauto.
Qed.
Lemma chunks_disjoint_cf : forall ly S Hp rd k1 k2, ARmcfR B ly S Hp rd -> In k1 (st_chunks S) -> In k2 (st_chunks S) -> ck_beg k1 <> ck_beg k2 ->
zdisjoint (ck_base B ly k1, ck_extent k1) (ck_base B ly k2, ck_extent k2).
Proof.
intros ly S HG rd k1 k2 M H1 H2 Hne.
pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_placed _ _ _ _ _ M) as [PL PD]. pose proof (amr_wfr _ _ _ _ _ M) as W.
pose proof (chunk_facts_cf ly S HG rd k1 M H1) as F1. pose proof (chunk_facts_cf ly S HG rd k2 M H2) as F2.
unfold cfacts_cf in F1, F2.
destruct F1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & C1). destruct F2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & C2).
assert (PRIMSEC : forall ka kb oa rb ob, In ka (st_chunks S) -> In kb (st_chunks S) -> ck_beg ka = PPrim oa -> ck_beg kb = PSec rb ob ->
cfacts_cf ly S ka -> cfacts_cf ly S kb -> zdisjoint (ck_base B ly ka, ck_extent ka) (ck_base B ly kb, ck_extent kb)).
{ intros ka kb oa rb ob Ha Hb Ea Eb (X1 & X2 & _ & _ & _ & _ & _ & _ & Xa) (Y1 & Y2 & _ & _ & _ & _ & _ & _ & Yb). rewrite Ea in Xa. rewrite Eb in Yb.
cbv zeta in Xa. destruct Xa as (Xc & _ & _ & Xext & Xbase & Xx & _ & Xxs & Xal). destruct Yb as (_ & _ & Ybase & Yext & Yin & _). unfold kFreeArrayOffset in Xal.
pose proof (region_in_prim ly (prim_class oa) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (pairwise_In zdisjoint _ (ly_sec ly rb, sec_map_size (ck_req kb)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly)
eq_refl PD Yin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia. }
destruct (ck_beg k1) as [|o1|r1 q1|c1 p1] eqn:E1; try solve [destruct C1]; destruct (ck_beg k2) as [|o2|r2 q2|c2 p2] eqn:E2; try solve [destruct C2].
-
cbv zeta in C1, C2. destruct C1 as (Xc & _ & _ & Xext & Xbase & Xx & Xxm & Xxs & Xal). destruct C2 as (Yc & _ & _ & Yext & Ybase & Yx & Yxm & Yxs & Yal). unfold kFreeArrayOffset in Xal, Yal.
rewrite Xext, Yext, Xbase, Ybase. unfold zdisjoint. cbn [fst snd].
destruct (Z.eq_dec (prim_class o1) (prim_class o2)) as [Ec|Hc].
+ rewrite <- Ec in *. set (c := prim_class o1) in *. set (x1 := o1 - region_off c) in *. set (x2 := o2 - region_off c) in *.
pose proof (class_ok c ltac:(lia)) as (K1 & _).
assert (x1 <> x2) by (intros E; apply Hne; f_equal; subst x1 x2; lia).
pose proof Xxm as D1. apply Z.mod_divide in D1 as [q1 Hq1]; [|lia]. pose proof Yxm as D2. apply Z.mod_divide in D2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia).
destruct (Z.lt_ge_cases q1 q2).
* pose proof (Z.mul_le_mono_nonneg_r (q1 + 1) q2 (class_size c) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (q2 + 1) q1 (class_size c) ltac:(lia) ltac:(lia)). lia.
+ pose proof (region_in_prim ly (prim_class o1) LO ltac:(lia)) as (R1 & R2 & _). pose proof (region_in_prim ly (prim_class o2) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base in *. rewrite !region_off_eq in * by lia.
destruct (Z.lt_ge_cases (prim_class o1) (prim_class o2)).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o1 + 1) (prim_class o2) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o2 + 1) (prim_class o1) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- exact (PRIMSEC k1 k2 o1 r2 q2 H1 H2 E1 E2 (chunk_facts_cf ly S HG rd k1 M H1) (chunk_facts_cf ly S HG rd k2 M H2)).
- apply zdisjoint_sym. exact (PRIMSEC k2 k1 o2 r1 q1 H2 H1 E2 E1 (chunk_facts_cf ly S HG rd k2 M H2) (chunk_facts_cf ly S HG rd k1 M H1)).
-
destruct C1 as (-> & _ & Xbase & Xext & Xin & _). destruct C2 as (-> & _ & Ybase & Yext & Yin & _).
rewrite Xbase, Ybase, Xext, Yext.
destruct (In_split_beg _ _ H1 (wfr_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & E & N1 & N2).
assert (E1in : In (ly_sec ly r1, sec_map_size (ck_req k1)) (sec_extents ly (set_chunks [k1] S))).
{ unfold sec_extents. cbn. rewrite E1. left. reflexivity. }
assert (H2' : In k2 l1 \/ In k2 l2).
{ rewrite E in H2. apply in_app_iff in H2 as [?|[E12|?]]; [left; assumption | exfalso; subst k2; apply Hne; congruence | right; assumption]. }
pose proof (sec_extents_split ly S l1 k1 l2 E) as SE. rewrite SE in PD.
assert (D : zdisjoint (ly_sec ly r1, sec_map_size (ck_req k1)) (ly_sec ly r2, sec_map_size (ck_req k2))).
{ destruct H2' as [H2'|H2'].
- apply zdisjoint_sym. rewrite <- !app_assoc in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S))); [reflexivity | exact PD | | apply in_app_iff; left; exact E1in].
unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity.
- rewrite <- !app_assoc in PD. rewrite (app_assoc (sec_extents ly (set_chunks l1 S))) in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S) ++ sec_extents ly (set_chunks [k1] S))); [reflexivity | exact PD | apply in_app_iff; right; exact E1in |].
apply in_app_iff. left. unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity. }
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage. lia.
Qed.
Lemma frame_facts_cf : forall ly S Hp rd cid pos, ARmcfR B ly S Hp rd -> In (cid, pos) (frames S) ->
0 <= cid <= 10 /\ 0 <= pos < fs_frames cid /\
in_app (ly_F ly) kFakeStackSize /\ ~ (exists a, in_zr a (ly_F ly, kFakeStackSize) /\ (in_zr a (ly_img ly) \/ ly_stk_lo ly <= a < ly_stk_hi ly)) /\ page_aligned (ly_F ly) /\
kFakeFramesOff + cid * 2 ^ 20 <= fs_frame_off cid pos /\ fs_frame_off cid pos + fs_frame_bytes cid <= kFakeStackSize /\
fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0 /\
kFakeFlagsOff <= fs_flag_off cid pos < kFakeFramesOff.
Proof.
intros ly S HG rd cid pos M Hin. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (wfs_live _ (wfr_fakestack _ _ _ _ _ (amr_wfr _ _ _ _ _ M))) as LV. unfold frames in Hin.
pose proof (proj1 (Forall_forall _ _) LV _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as F1. cbn [fst snd] in F1.
pose proof (frame_off_bounds cid pos H1 H2) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof (flag_off_bounds cid pos H1 H2) as A7.
splits; try assumption; try lia; [| exact (lo_F_al _ LO)].
intros (a & Ha & Hbad). destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_F ly, kFakeStackSize); split; [unfold owned_extents; cbn; tauto | exact Ha])) as (_ & NS & NI). tauto.
Qed.
Lemma aview_present_cf : forall ly S md H mem a, ALedger_cf segs ly S md -> 0 <= a < 2 ^ 64 -> ~ in_zr a (ly_img ly) ->
aview segs H mem a <> None -> apresent H mem a.
Proof.
intros ly S md H mem a L Ha Himg Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
assert (NIMG : seg_rom segs (Z_to_bv 64 a) = None).
{ destruct (seg_rom segs (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
destruct (seg_rom_in_img segs a Ha ltac:(rewrite E; discriminate)) as (sg & Hsg & Hr). pose proof (alc_img _ _ _ _ L sg Hsg). apply Himg. unfold in_zr. lia. }
destruct (H (Z_to_bv 64 a)) eqn:EH; [rewrite NIMG in Hv; exfalso; apply Hv; reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:EM; [split; [reflexivity | exists b; reflexivity]|].
rewrite NIMG in Hv. exfalso. apply Hv. reflexivity.
Qed.
Lemma chunk_vs_F_cf : forall ly S Hp rd k, ARmcfR B ly S Hp rd -> In k (st_chunks S) -> zdisjoint (ck_base B ly k, ck_extent k) (ly_F ly, kFakeStackSize).
Proof.
intros ly S HG rd k M Hk. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia.
Qed.
Lemma blocks_pairwise_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> pairwise zdisjoint (map (brange B ly) (List.filter is_alloc (st_chunks S))).
Proof.
intros ly S HG rd M.
apply (pairwise_map (fun k1 k2 => ck_beg k1 <> ck_beg k2) zdisjoint (brange B ly)).
- intros x y Hx Hy Hne. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
pose proof (chunks_disjoint_cf ly S HG rd x y M Hx Hy Hne) as D.
pose proof (chunk_facts_cf ly S HG rd x M Hx) as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (chunk_facts_cf ly S HG rd y M Hy) as (_ & _ & _ & Y4 & Y5 & _ & Y7 & Y8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)). pose proof (req_size_bounds (ck_req y) ltac:(lia)).
unfold brange, zdisjoint in *. cbn [fst snd] in *. lia.
- apply (pairwise_of_keys ck_beg). { apply NoDup_map_filter. exact (wfr_chunks_nodup _ _ _ _ _ (amr_wfr _ _ _ _ _ M)). }
intros x y _ _ Hne. exact Hne.
Qed.
Lemma frames_pairwise_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> pairwise zdisjoint (map (frange ly) (frames S)).
Proof.
intros ly S HG rd M. pose proof (wfs_nodup _ (wfr_fakestack _ _ _ _ _ (amr_wfr _ _ _ _ _ M))) as ND. unfold frames.
apply (pairwise_map (fun f1 f2 => f1 <> f2) zdisjoint (frange ly)).
- intros [c1 p1] [c2 p2] H1 H2 Hne.
pose proof (frame_facts_cf ly S HG rd c1 p1 M H1) as (A1 & A2 & _). pose proof (frame_facts_cf ly S HG rd c2 p2 M H2) as (B1 & B2 & _).
pose proof (frames_apart c1 p1 c2 p2 A1 A2 B1 B2 Hne) as D. unfold frange, frame_addr, zdisjoint in *. cbn [fst snd] in *. lia.
- apply (pairwise_of_keys (fun f : Z * Z => f)); [rewrite map_id; exact ND|]. intros x y _ _ Hne. exact Hne.
Qed.
Lemma client_byte_not_img_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> aclient_byte B ly S a -> ~ in_zr a (ly_img ly).
Proof.
intros ly S HG rd a M C. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as IMG.
destruct C as [(k & Hk & Hst & Hr)|(cp' & Hcp & Hr)].
- pose proof (chunk_facts_cf ly S HG rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
apply (proj1 (chunk_apart_cf ly S HG rd k a M Hk ltac:(rewrite G4 in Hr; unfold ck_n in Hr; lia))).
- destruct cp' as [cid pos]. cbn [fst snd] in Hr. pose proof (frame_facts_cf ly S HG rd cid pos M Hcp) as (C1 & _ & F1 & F2 & _ & P1 & P2 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
destruct Hr as [Hr|Hr].
+ intros Hi. apply F2. exists a. split; [unfold in_zr, frame_addr, kFakeFramesOff, kFakeStackSize in *; cbn [fst snd] in *; lia | left; exact Hi].
+ unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold in_app, kFakeFramesOff in *.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB _].
unfold SHADOW_OFF, in_zr, kImgLo, kImgEnd, page_aligned in *. cbn [fst snd] in *. lia.
Qed.
Lemma sec_extents_le_cf : forall ly ly' S U pp cc bb, layout_le (length (st_secs S)) ly ly' -> WfR_cf U pp cc bb S ->
sec_extents ly' S = sec_extents ly S.
Proof.
intros ly ly' S U pp cc bb LE W. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
unfold sec_extents. pose proof (wfr_chunks _ _ _ _ _ W) as CK.
induction (st_chunks S) as [|k t IH]; [reflexivity|]. inversion CK as [|k0 t0 [Hn C] CKt]; subst. cbn [flat_map].
rewrite (IH CKt). destruct (ck_beg k) as [|o|r o|c p]; try reflexivity. destruct C as (_ & _ & sm & Hsm & _).
rewrite E15 by (eapply nth_error_lt; exact Hsm). reflexivity.
Qed.
Lemma find_chunk_at_hit_cf : forall ly S Hp rd l k g, ARmcfR B ly S Hp rd -> incl l (st_chunks S) -> List.NoDup (map ck_beg l) -> In k l ->
ck_base B ly k <= g < ck_base B ly k + ck_extent k -> find_chunk_at B ly l g = Some k.
Proof.
intros ly S HG rd l k g M. induction l as [|k' t IH]; intros Hincl ND Hk Hg; [destruct Hk|]. cbn [find_chunk_at].
inversion ND as [|b0 l0 Hni ND']; subst.
destruct (andb (ck_base B ly k' <=? g) (g <? ck_base B ly k' + ck_extent k')) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. f_equal.
destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:Ebq; [apply sptr_eqb_spec in Ebq as Eb | assert (Nb : ck_beg k' <> ck_beg k) by (intros E'; apply sptr_eqb_spec in E'; congruence)].
+ destruct Hk as [->|Hk]; [reflexivity|]. exfalso. apply Hni. rewrite Eb. apply in_map_iff. exists k. auto.
+ exfalso. pose proof (chunks_disjoint_cf ly S HG rd k' k M (Hincl k' (or_introl eq_refl)) (Hincl k ltac:(exact (or_introl eq_refl) || (destruct Hk as [->|Hk]; [left; reflexivity | right; exact Hk]))) Nb) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (chunk_facts_cf ly S HG rd k M (Hincl k ltac:(destruct Hk as [->|Hk]; [left; reflexivity | right; exact Hk]))) as (_ & _ & _ & _ & X5 & _ & X7 & X8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
- destruct Hk as [->|Hk].
+ exfalso. apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
+ apply IH; [intros x Hx; apply Hincl; right; exact Hx | exact ND' | exact Hk | exact Hg].
Qed.

(* ---------------------------------------------------------------------------- *)
(* The twelve non-shadow laws of YG0s.v, over ARcfR.                              *)
Theorem AR_wle_law_ok_cf : AR_wle_law_cf segs B.
Proof. intros ly S HG W W' mem md. apply AR_wle_cf. Qed.
Theorem AR_zshadow_law_ok_cf : AR_zshadow_law_cf segs B.
Proof.
intros ly S HG W mem md r (M & _ & _) Hr. exact (proj1 (Forall_forall _ _) (amr_zshadow _ _ _ _ _ M) r Hr).
Qed.
Theorem AR_const_law_ok_cf : AR_const_law_cf segs B.
Proof.
intros ly S HG W mem md (M & _ & _).
pose proof (amr_const _ _ _ _ _ M) as C. pose proof (aso_const_law _ (amr_syms _ _ _ _ _ M) ly) as (I1 & I2 & I3 & I4).
pose proof (asyms_area_bound B (as_shadow_cell B, 8) (amr_syms _ _ _ _ _ M) ltac:(cbn; tauto)) as [A1 A2].
pose proof (asyms_area_bound B (as_uar_cell B, 4) (amr_syms _ _ _ _ _ M) ltac:(cbn; tauto)) as [A3 A4]. cbn [fst snd] in A1, A2, A3, A4.
assert (F := fun c (H : In c (as_const B ly)) => proj1 (Forall_forall _ _) C c H).
unfold SHADOW_OFF, kImgEnd in *. splits.
- eapply rdword_cell; [lia | exact (F _ I1)].
- pose proof (F _ I2) as H2. unfold cell_holds in H2. cbn [c_at c_val c_w z4 c4 aeval] in H2. intros k Hk. exact (H2 k Hk).
- eapply rdword_cell; [lia | exact (F _ I3)].
- eapply rdword_cell; [lia | exact (F _ I4)].
Qed.
Theorem AR_stack_law_ok_cf : AR_stack_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & _ & _) Ha [OW _]. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_top _ LO) as TOP.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound B a (amr_syms _ _ _ _ _ M) O). unfold kImgEnd, kHighMemBeg in *. lia.
- exact (proj1 (proj2 (owned_extents_bound ly a LO O)) Ha).
- apply (proj1 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) Ha).
- exact (proj1 (proj2 (owned_sec_bound_cf ly S HG _ a M O)) Ha).
- pose proof (owned_shadow_bound_cf ly S HG _ a M O). lia.
Qed.
Theorem AR_owned_low_law_ok_cf : AR_owned_low_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & _ & _) [OW _]. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof ASAN_CEIL_range as [CR _]. ceil; unfold ASAN_CEIL in CR.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound B a (amr_syms _ _ _ _ _ M) O). unfold kImgEnd in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_extents_bound ly a LO O))). ceil; unfold ASAN_CEIL in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O])))).
ceil; unfold ASAN_CEIL in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_sec_bound_cf ly S HG _ a M O))). ceil; unfold ASAN_CEIL in *. lia.
- pose proof (owned_shadow_bound_cf ly S HG _ a M O). unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Theorem AR_frames_law_ok_cf : AR_frames_law_cf segs B.
Proof.
intros ly S HG W mem md cid pos (M & L & _) Hin.
pose proof (frame_facts_cf ly S HG _ cid pos M Hin) as (C1 & C2 & F1 & F2 & FA & O1 & O2 & O3 & O4 & O5 & O6).
pose proof (lo_img _ (amr_layout _ _ _ _ _ M)) as IMG.
assert (IA : in_app (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid)).
{ eapply in_app_sub; [exact F1 | | |]; unfold kFakeFramesOff, kFakeStackSize in *; pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)); lia. }
ceil; unfold frame_addr, in_app, page_aligned, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kImgLo, kImgEnd, kFakeFramesOff, kFakeStackSize, kFakeFlagsOff in *.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
assert (VIS1 : forall i, 0 <= i < fs_frame_bytes cid -> aview segs (w_H W) mem (ly_F ly + fs_frame_off cid pos + i) <> None).
{ intros i Hi. pose proof (proj1 (Forall_forall _ _) (amr_client _ _ _ _ _ M) (AF (fs_frame_off cid pos), fs_frame_bytes cid)) as V.
unfold aclient in V. specialize (V ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hin])).
exact (V i Hi). }
assert (VIS2 : forall i, 0 <= i < fs_frame_bytes cid / 8 -> aview segs (w_H W) mem (shadow_addr (ly_F ly + fs_frame_off cid pos) + i) <> None).
{ intros i Hi. pose proof (proj1 (Forall_forall _ _) (amr_client _ _ _ _ _ M) (ASh (AF (fs_frame_off cid pos)), fs_frame_bytes cid / 8)) as V.
unfold aclient in V. specialize (V ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hin])).
exact (V i Hi). }
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB1 SB2]. unfold SHADOW_OFF, kHighMemEnd, kHighMemBeg in SB1, SB2.
assert (NI1 : forall a, ly_F ly + fs_frame_off cid pos <= a < ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid -> ~ in_zr a (ly_img ly)).
{ intros a Ha Hi. apply F2. exists a. split; [unfold in_zr; cbn [fst snd]; lia | left; exact Hi]. }
assert (NI2 : forall a, 2147450880 <= a -> ~ in_zr a (ly_img ly)) by (intros a Ha Hi; unfold in_zr, page_aligned in *; lia).
split; [|split; [exact IA | split]].
- apply Z.mod_divide; [lia|]. apply Z.mod_divide in FA as [q Hq]; [|lia]. apply Z.mod_divide in O3 as [q' Hq']; [|lia]. exists (q * 128 + q' * 2). lia.
- intros a Ha. split.
+ replace a with (ly_F ly + fs_frame_off cid pos + (a - (ly_F ly + fs_frame_off cid pos))) by lia.
eapply aview_present_cf; [exact L | lia | apply NI1; lia | apply VIS1; lia].
+ intros [_ NC]. apply NC. right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr, frame_addr. cbn [fst snd]. lia.
- intros i Hi. split.
+ eapply aview_present_cf; [exact L | lia | apply NI2; lia | apply VIS2; exact Hi].
+ intros [_ NC]. apply NC. right. exists (cid, pos). split; [exact Hin|]. right. unfold in_zr, frame_addr. cbn [fst snd]. lia.
Qed.
Theorem AR_flag_law_ok_cf : AR_flag_law_cf segs B.
Proof.
intros ly S HG W mem md cid pos (M & L & _) Hin.
pose proof (frame_facts_cf ly S HG _ cid pos M Hin) as (C1 & C2 & F1 & F2 & FA & O1 & O2 & O3 & O4 & O5 & O6).
pose proof (amr_flags _ _ _ _ _ M cid pos C1 C2) as FL.
pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as IMG.
assert (IA : in_app (ly_F ly + fs_flag_off cid pos) 1).
{ eapply in_app_sub; [exact F1 | | |]; unfold kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *; lia. }
pose proof (app_addr_below_ceil _ (in_app_addr _ _ (ly_F ly + fs_flag_off cid pos) IA ltac:(lia))) as AC.
assert (NI : ~ in_zr (ly_F ly + fs_flag_off cid pos) (ly_img ly)).
{ intros Hi. apply F2. exists (ly_F ly + fs_flag_off cid pos). split; [unfold in_zr, kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *; cbn [fst snd]; lia | left; exact Hi]. }
ceil; unfold flag_addr, in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kImgEnd, kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *.
split; [|split; [|split; [exact IA | exact (proj2 AC)]]].
- eapply aview_present_cf; [exact L | lia | exact NI | unfold flag_addr in FL; rewrite FL; discriminate].
- split.
+ right. left. apply Exists_exists. exists (ly_F ly, kFakeStackSize). split; [unfold owned_extents; cbn; tauto | unfold in_zr, kFakeStackSize; cbn; lia].
+ intros [(k & Hk & Hst & Hr)|(cp' & Hcp & [Hr|Hr])].
*
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
assert (D : zdisjoint (ck_base B ly k, ck_extent k) (ly_F ly, kFakeStackSize)).
{ destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia. }
unfold zdisjoint, kFakeStackSize, ck_n in *. cbn [fst snd] in D. lia.
* destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf ly S HG _ c2 p2 M Hcp) as (Q1 & _ & _ & _ & _ & P1 & P2 & _). unfold kFakeFramesOff, kFakeStackSize in P1, P2.
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
* destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf ly S HG _ c2 p2 M Hcp) as (Q1 & _ & _ & _ & _ & P1 & P2 & P3 & P4 & _). unfold kFakeFramesOff, kFakeStackSize in P1, P2.
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)).
pose proof (shadow_range_below (ly_F ly + fs_frame_off c2 p2) (fs_frame_bytes c2) ltac:(lia) ltac:(lia)) as SB.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off c2 p2) ltac:(lia)) as [SB0 _].
unfold kHighMemEnd, kHighMemBeg, SHADOW_OFF in SB, SB0. lia.
Qed.
Theorem AR_sep_law_ok_cf : AR_sep_law_cf segs B.
Proof.
intros ly S HG W mem md (M & L & _). split.
- rewrite blocks_ranges_eq. change (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) with (frange ly).
apply pairwise_app; [eapply blocks_pairwise_cf; exact M | eapply frames_pairwise_cf; exact M |].
intros x y Hx Hy. apply in_map_iff in Hx as (k & <- & Hk). apply filter_In in Hk as [Hk _]. apply in_map_iff in Hy as ([cid pos] & <- & Hf).
pose proof (chunk_vs_F_cf ly S HG _ k M Hk) as D. pose proof (chunk_facts_cf ly S HG _ k M Hk) as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (frame_facts_cf ly S HG _ cid pos M Hf) as (Fc & _ & _ & _ & _ & P1 & P2 & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)).
unfold brange, frange, frame_addr, zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in *. pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
- apply Forall_forall. intros [cid pos] Hf. cbn [fst snd].
pose proof (frame_facts_cf ly S HG _ cid pos M Hf) as (C1 & _ & F1 & F2 & _ & P1 & P2 & _).
ceil; unfold frame_addr, in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kFakeFramesOff, kFakeStackSize in *.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
Qed.
Theorem AR_blocks_law_ok_cf : AR_blocks_law_cf segs B.
Proof.
intros ly S HG W mem md p n (M & L & _) Hin. pose proof Hin as Hin0.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite G4.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (IA : in_app (ck_base B ly k + ck_rz k) (req_size (ck_req k))) by (eapply in_app_sub; [exact G1 | lia | lia | lia]).
ceil; unfold in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *.
splits; try lia.
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in G3 as [q Hq]; [|lia]; apply Z.mod_divide in G6 as [q' Hq']; [|lia]; exists (q + q'); lia).
- intros a Ha. split.
+ pose proof (proj1 (Forall_forall _ _) (amr_client _ _ _ _ _ M) (sptr_exp (ck_user k), ck_n k)) as V. unfold aclient in V.
specialize (V ltac:(apply in_app_iff; left; apply in_flat_map; exists k; split; [exact Hk | unfold chunk_user; rewrite Hst; left; reflexivity])).
unfold range_vis in V. cbn [fst snd] in V. fold (sptr_addr B ly (ck_user k)) in V. rewrite G4 in V.
replace a with (ck_base B ly k + ck_rz k + (a - (ck_base B ly k + ck_rz k))) by lia.
destruct (chunk_apart_cf ly S HG _ k (ck_base B ly k + ck_rz k + (a - (ck_base B ly k + ck_rz k))) M Hk ltac:(clear - Ha G5 G8; lia)) as [NI _].
eapply aview_present_cf; [exact L | lia | exact NI | apply V; unfold ck_n; lia].
+ intros [_ NC]. apply NC. left. exists k. rewrite G4. unfold ck_n. auto.
- rewrite blocks_ranges_eq. eapply blocks_pairwise_cf. exact M.
Qed.
Theorem AR_client_img_law_ok_cf : AR_client_img_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & L & _) HC.
assert (NZ : ~ in_zr a (ly_img ly)).
{ destruct HC as [(p & n & Hin & Hr)|[(cid & pos & Hin & Hr)|(cid & pos & Hin & ->)]].
- apply (client_byte_not_img_cf ly S HG _ a M).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn). subst p n. left. exists k. split; [exact Hk|]. split; [exact Hst|].
unfold ck_n. exact Hr.
- apply (client_byte_not_img_cf ly S HG _ a M).
right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. exact Hr.
-
pose proof (frame_facts_cf ly S HG _ cid pos M Hin) as (Fc & Fp & F1 & F2 & _). pose proof (flag_off_bounds cid pos Fc Fp) as FB.
intros IN. apply F2. exists (flag_addr ly cid pos).
split; [unfold in_zr, flag_addr; cbn [fst snd]; unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia | left; exact IN]. }
split; [exact NZ|]. intros (sg & Hsg & Ha). apply NZ. pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. unfold in_zr. lia.
Qed.
Theorem AR_owned_image_law_ok_cf : AR_owned_image_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & L & _) (sg & Hsg & Ha). pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (lo_img _ LO) as IMG.
assert (AI : in_zr a (ly_img ly)) by (unfold in_zr; lia).
split.
- intros [[O|[O|[O|[O|O]]]] _]; [exact O | exfalso ..].
+ exact (proj2 (proj2 (owned_extents_bound ly a LO O)) AI).
+ exact (proj2 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) AI).
+ exact (proj2 (proj2 (owned_sec_bound_cf ly S HG _ a M O)) AI).
+ pose proof (owned_shadow_bound_cf ly S HG _ a M O). unfold SHADOW_OFF, in_zr, kImgLo, kImgEnd, page_aligned in *. cbn [fst snd] in *. lia.
- intros O. split; [left; exact O|]. intros C. exact (client_byte_not_img_cf ly S HG _ a M C AI).
Qed.
Theorem AR_layout_law_ok_cf : AR_layout_law_cf segs B.
Proof.
intros ly S HG W mem md ly' (M & L & _) LE. pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
assert (USR : forall k, In k (st_chunks S) -> sptr_addr B ly' (ck_user k) = sptr_addr B ly (ck_user k)).
{ intros k Hk. apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|].
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ WF) k Hk) as [_ C]. unfold ck_user.
destruct (ck_beg k) as [|o|r o|c p]; cbn; try exact I. destruct C as (_ & _ & sm & Hsm & _). eapply nth_error_lt. exact Hsm. }
assert (FR : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) by (intros; unfold frame_addr; rewrite E6; reflexivity).
splits.
- unfold ablocks, blocks. rewrite !map_map. apply map_ext_in. intros k Hk. apply filter_In in Hk as [Hk _]. cbn [fst snd]. rewrite (USR k Hk). reflexivity.
- exact FR.
- intros a. unfold aowned, aclient_byte.
rewrite (sec_extents_le_cf ly ly' S _ _ _ _ LE WF).
assert (EO : owned_extents ly' = owned_extents ly) by (unfold owned_extents; rewrite E1, E3, E4, E5, E6, E7, E8, ED; reflexivity).
assert (ES : static_extents ly' = static_extents ly) by (unfold static_extents; rewrite EO, E10, E11, EI; reflexivity).
assert (EZ : zero_shadow_ranges B ly' = zero_shadow_ranges B ly) by (unfold zero_shadow_ranges; rewrite E10, E11; reflexivity).
rewrite EO, ES, EZ, E5.
assert (CB : (exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly' (ck_user k) <= a < sptr_addr B ly' (ck_user k) + ck_n k) <->
(exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly (ck_user k) <= a < sptr_addr B ly (ck_user k) + ck_n k)).
{ split; intros (k & Hk & Hs & Hr); exists k; rewrite ?(USR k Hk) in *; auto. }
assert (CF : forall cq, (in_zr a (frame_addr ly' (fst cq) (snd cq), fs_frame_bytes (fst cq)) \/ in_zr a (shadow_addr (frame_addr ly' (fst cq) (snd cq)), fs_frame_bytes (fst cq) / 8)) <->
(in_zr a (frame_addr ly (fst cq) (snd cq), fs_frame_bytes (fst cq)) \/ in_zr a (shadow_addr (frame_addr ly (fst cq) (snd cq)), fs_frame_bytes (fst cq) / 8))).
{ intros cq. rewrite !FR. tauto. }
split; intros [O NC]; (split; [exact O|]); intros C; apply NC; destruct C as [C|(cq & Hcq & C)].
+ left. apply CB. exact C.
+ right. exists cq. split; [exact Hcq|]. apply CF. exact C.
+ left. apply CB. exact C.
+ right. exists cq. split; [exact Hcq|]. apply CF. exact C.
Qed.
End m.
End j.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YG0qcf.v:30-716 over ARcfR.                                                                                        *)
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac show := match goal with |- ?g => idtac g end.
Section s.
Variable segs : list Segment.
Variable B : asyms.
(* ALedger_same_cf: the layer's YG0qcf.ALedger_same_cf (YG0qcf.v:37), not a copy (the copy broke on the ledger's
   new fields; ReallocPrimary / Main 2026-10-30). *)
Lemma nc_img_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> in_zr a (ly_img ly) -> ~ aclient_byte B ly S a.
Proof. intros ly S Hp rd a M Ha C. exact (client_byte_not_img_cf B ly S Hp rd a M C Ha). Qed.
Lemma nc_static_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> Exists (in_zr a) (as_owned_static B ++ as_zero_shadow B) -> ~ aclient_byte B ly S a.
Proof.
intros ly S Hp rd a M H. eapply nc_img_cf; [exact M|]. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r Hr) as [S1 S2]. unfold in_zr. lia.
Qed.
Lemma nc_app_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> app_addr a ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) ->
~ aclient_byte B ly S a.
Proof.
intros ly S Hp rd a M Ha NB NF [(k & Hk & Hst & Hr)|(fp & Hcp & [Hr|Hr])].
- pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & _). rewrite G4 in Hr. unfold ck_n in Hr. exact (NB k Hk Hst Hr).
- destruct fp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (C1 & _ & _ & _ & _ & P1 & P2 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
- destruct fp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (C1 & _ & F1 & F2 & _ & P1 & P2 & P3 & P4 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
ceil; unfold app_addr, in_app, kFakeFramesOff, kFakeStackSize, ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *.
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(unfold kHighMemEnd; lia)) as SB.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB0 _].
unfold kHighMemBeg, SHADOW_OFF in SB, SB0. lia.
Qed.
Lemma nc_high_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> kHighMemBeg <= a < ASAN_CEIL ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) ->
~ aclient_byte B ly S a.
Proof. intros ly S Hp rd a M Ha. apply (nc_app_cf ly S Hp rd a M). unfold app_addr, kHighMemBeg in *. lia. Qed.
Lemma nc_shadow_cf : forall ly S Hp rd a lo len, ARmcfR B ly S Hp rd -> lo mod 8 = 0 -> 0 <= lo -> lo + len <= kHighMemEnd ->
zdisjoint (lo, len) (ly_F ly, kFakeStackSize) ->
shadow_addr lo <= a < shadow_addr lo + (len + 7) / 8 -> ~ aclient_byte B ly S a.
Proof.
intros ly S Hp rd a lo len M Hlo8 Hlo0 Hhi D Ha [(k & Hk & Hst & Hr)|(fp & Hcp & [Hr|Hr])].
- pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & _ & G8 & _). rewrite G4 in Hr.
unfold in_app, kLowShadowBeg, ck_n in G1, Hr.
pose proof (shadow_range_below lo (len + 7) Hlo0 ltac:(lia)) as SB. unfold kHighMemBeg, kHighMemEnd in *.
assert ((len + 7) / 8 <= (len + 7) / 8) by lia.
pose proof (shadow_addr_bounds lo Hlo0) as [SB0 _]. unfold SHADOW_OFF in SB0.
assert (shadow_addr lo + (len + 7) / 8 <= 17594333495296); [|lia].
unfold shadow_addr, SHADOW_OFF in *.
assert (L : (lo + len + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia). change (140737488355335 / 8) with 17592186044416 in L.
assert (lo / 8 + (len + 7) / 8 <= (lo + len + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le lo 8 ltac:(lia)). pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)). lia.
- destruct fp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (C1 & _ & F1 & _ & _ & P1 & P2 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
ceil; unfold in_app, kLowShadowBeg, ASAN_CEIL, kFakeFramesOff, kFakeStackSize, kHighMemBeg, kHighMemEnd, shadow_addr, SHADOW_OFF in *.
assert (L : (lo + len + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia). change (140737488355335 / 8) with 17592186044416 in L.
assert (lo / 8 + (len + 7) / 8 <= (lo + len + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le lo 8 ltac:(lia)). pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)). lia.
-
destruct fp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (C1 & _ & F1 & F2 & FA & P1 & P2 & P3 & P4 & P5 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
set (f := ly_F ly + fs_frame_off cid pos) in *.
assert (F8 : f mod 8 = 0).
{ subst f. unfold page_aligned in FA. apply Z.mod_divide; [lia|]. apply Z.mod_divide in FA as [q Hq]; [|lia]. apply Z.mod_divide in P3 as [q' Hq']; [|lia]. exists (q * 512 + q' * 8). lia. }
apply Z.mod_divide in F8 as [qf Hqf]; [|lia]. apply Z.mod_divide in Hlo8 as [ql Hql]; [|lia]. apply Z.mod_divide in P5 as [qb Hqb]; [|lia].
unfold shadow_addr, SHADOW_OFF, zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in D.
rewrite Hqf, Hql, Hqb in *. rewrite !Z.div_mul in Hr by lia. rewrite Z.div_mul in Ha by lia.
replace (qb * 64 / 8) with (qb * 8) in Hr by (symmetry; replace (qb * 64) with (qb * 8 * 8) by lia; apply Z.div_mul; lia).
assert (8 * ((len + 7) / 8) <= len + 7) by (apply Z.mul_div_le; lia).
assert (0 <= (len + 7) / 8) by (apply Z.div_pos; lia).
destruct D as [D|D]; nia.
Qed.
Lemma user_in_extent_cf : forall ly S Hp rd k a, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k.
Proof. intros ly S Hp rd k a M Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & G5 & _ & _ & G8 & _). lia. Qed.
Lemma extent_zone_cf : forall ly S Hp rd k, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
(ly_prim ly <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= ly_prim ly + kPrimResvSize) \/
(exists m len, In (m, len) (sec_extents ly S) /\ m + kPage = ck_base B ly k /\ len = ck_extent k + kPage).
Proof.
intros ly S Hp rd k M Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amr_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _). lia.
- right. destruct GG as (_ & _ & Gbase & Gext & Gin & _). exists (ly_sec ly r), (sec_map_size (ck_req k)). unfold kPage in *. splits; [exact Gin | lia | lia].
Qed.
Lemma own_static_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> Exists (in_zr a) (as_owned_static B) -> aowned B ly S a.
Proof.
intros ly S Hp rd a M H. split; [left; exact H|]. eapply nc_static_cf; [exact M|].
apply Exists_exists in H as (r & Hr & Ha). apply Exists_exists. exists r. split; [apply in_app_iff; left; exact Hr | exact Ha].
Qed.
Lemma own_area_cf : forall ly S Hp rd r a, ARmcfR B ly S Hp rd -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> aowned B ly S a.
Proof.
intros ly S Hp rd r a M Hr Ha. eapply own_static_cf; [exact M|].
pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amr_syms _ _ _ _ _ M)) r Hr) as X. apply Exists_exists in X as (r' & Hr' & [S1 S2]).
apply Exists_exists. exists r'. split; [exact Hr'|]. unfold in_zr. lia.
Qed.
Lemma own_ext_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd ->
(Exists (in_zr a) (owned_extents ly) \/ Exists (in_zr a) (sec_extents ly S)) ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) -> aowned B ly S a.
Proof.
intros ly S Hp rd a M Z NB NF.
assert (AA : app_addr a).
{ destruct Z as [Z|Z]; [exact (proj1 (owned_extents_bound ly a (amr_layout _ _ _ _ _ M) Z)) | exact (proj1 (owned_sec_bound_cf B ly S Hp rd a M Z))]. }
split; [|eapply nc_app_cf; eassumption].
destruct Z as [Z|Z]; [right; left; exact Z | right; right; right; left; exact Z].
Qed.
Lemma own_high_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> kHighMemBeg <= a ->
(Exists (in_zr a) (owned_extents ly) \/ Exists (in_zr a) (sec_extents ly S)) ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) -> aowned B ly S a.
Proof. intros ly S Hp rd a M _ Z NB NF. exact (own_ext_cf ly S Hp rd a M Z NB NF). Qed.
Lemma own_core_cf : forall ly S Hp rd e a, ARmcfR B ly S Hp rd -> In e (core_extents ly) -> fst e <= a < fst e + snd e -> aowned B ly S a.
Proof.
intros ly S Hp rd e a M He Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (amr_placed _ _ _ _ _ M) as [PL PD].
assert (HeO : In e (owned_extents ly)) by (unfold core_extents in He; unfold owned_extents; cbn in He |- *; tauto).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e HeO) as H1.
assert (DP : zdisjoint (ly_prim ly, kPrimResvSize) e /\ zdisjoint e (ly_F ly, kFakeStackSize)).
{ pose proof (lo_disj _ LO) as D. unfold static_extents, owned_extents in D. cbn [pairwise app] in D.
destruct D as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & _).
repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end.
unfold core_extents in He. cbn in He.
destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [assumption | first [assumption | apply zdisjoint_sym; assumption]]). }
destruct DP as [DP DF].
assert (NF : ~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize)).
{ unfold zdisjoint, kFakeFramesOff in *. cbn [fst snd] in *. lia. }
eapply own_ext_cf; [exact M | left; apply Exists_exists; exists e; split; [exact HeO | exact Ha] | | exact NF].
intros k Hk Hst Hr. pose proof (user_in_extent_cf ly S Hp rd k a M Hk Hr) as HE.
destruct (extent_zone_cf ly S Hp rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
- unfold zdisjoint in DP. cbn [fst snd] in DP. lia.
- pose proof (pairwise_In zdisjoint _ (m, len) e (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(unfold static_extents; apply in_app_iff; left; exact HeO)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma secmaps_disjoint_cf : forall ly S Hp rd k1 k2 r1 o1 r2 o2, ARmcfR B ly S Hp rd -> In k1 (st_chunks S) -> In k2 (st_chunks S) ->
ck_beg k1 = PSec r1 o1 -> ck_beg k2 = PSec r2 o2 -> ck_beg k1 <> ck_beg k2 ->
zdisjoint (ly_sec ly r1, sec_map_size (ck_req k1)) (ly_sec ly r2, sec_map_size (ck_req k2)).
Proof.
intros ly S Hp rd k1 k2 r1 o1 r2 o2 M H1 H2 E1 E2 Hne. pose proof (amr_wfr _ _ _ _ _ M) as WF. pose proof (proj2 (amr_placed _ _ _ _ _ M)) as PD.
destruct (In_split_beg _ _ H1 (wfr_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2).
assert (E1in : In (ly_sec ly r1, sec_map_size (ck_req k1)) (sec_extents ly (set_chunks [k1] S))).
{ unfold sec_extents. cbn. rewrite E1. left. reflexivity. }
assert (H2' : In k2 l1 \/ In k2 l2).
{ rewrite E in H2. apply in_app_iff in H2 as [?|[E12|?]]; [left; assumption | exfalso; subst k2; exact (Hne eq_refl) | right; assumption]. }
pose proof (sec_extents_split ly S l1 k1 l2 E) as SE. rewrite SE in PD.
destruct H2' as [H2'|H2'].
- apply zdisjoint_sym. rewrite <- !app_assoc in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S))); [reflexivity | exact PD | | apply in_app_iff; left; exact E1in].
unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity.
- rewrite <- !app_assoc in PD. rewrite (app_assoc (sec_extents ly (set_chunks l1 S))) in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S) ++ sec_extents ly (set_chunks [k1] S))); [reflexivity | exact PD | apply in_app_iff; right; exact E1in |].
apply in_app_iff. left. unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity.
Qed.
Lemma prim_vs_secmap_cf : forall ly S Hp rd k o e, ARmcfR B ly S Hp rd -> In k (st_chunks S) -> ck_beg k = PPrim o -> In e (sec_extents ly S) ->
zdisjoint (ck_base B ly k, ck_extent k) e.
Proof.
intros ly S Hp rd k o e M Hk Hb He. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG). rewrite Hb in GG.
cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amr_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
Qed.
Lemma own_prim_nonuser_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
aowned B ly S a.
Proof.
intros ly S Hp rd a M Ha NB. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (lo_high _ LO) as [H1 H2].
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
eapply own_high_cf; [exact M | lia | left; apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; lia] | exact NB |].
unfold zdisjoint, kFakeFramesOff in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_meta_cf : forall ly S Hp rd k a, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> aowned B ly S a.
Proof.
intros ly S Hp rd k a M Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (NB : forall k', In k' (st_chunks S) -> ck_state k' = CAllocated ->
~ (ck_base B ly k' + ck_rz k' <= a < ck_base B ly k' + ck_rz k' + req_size (ck_req k'))).
{ intros k' Hk' Hst' Hr. pose proof (user_in_extent_cf ly S Hp rd k' a M Hk' Hr) as HE.
destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:Eq.
- apply sptr_eqb_spec in Eq. destruct (In_split_beg _ _ Hk (wfr_chunks_nodup _ _ _ _ _ (amr_wfr _ _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
assert (k' = k).
{ rewrite E in Hk'. apply in_app_iff in Hk' as [X|[<-|X]]; [exfalso; apply N1 | reflexivity | exfalso; apply N2]; rewrite <- Eq; apply in_map_iff; exists k'; auto. }
subst k'. destruct (ck_beg k); lia.
- assert (Hne : ck_beg k' <> ck_beg k) by (intros E'; apply sptr_eqb_spec in E'; congruence).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
+ pose proof (chunks_disjoint_cf B ly S Hp rd k' k M Hk' Hk ltac:(rewrite Eb; exact Hne)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
+ destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (chunk_facts_cf B ly S Hp rd k' M Hk') as (_ & _ & _ & _ & _ & _ & _ & _ & GG').
destruct (ck_beg k') as [|o'|r' o'|c' p'] eqn:Eb'; try solve [destruct GG'].
* pose proof (prim_vs_secmap_cf ly S Hp rd k' o' _ M Hk' Eb' Gin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kPage in *. lia.
* destruct GG' as (-> & _ & Gbase' & Gext' & _).
pose proof (secmaps_disjoint_cf ly S Hp rd k' k r' kPage r kPage M Hk' Hk Eb' Eb ltac:(rewrite ?Eb', ?Eb in Hne; rewrite ?Eb', ?Eb; exact Hne)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia. }
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amr_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
eapply own_prim_nonuser_cf; [exact M | lia | exact NB].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
eapply own_ext_cf; [exact M | right; apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req k)); split; [exact Gin | unfold in_zr, kPage in *; cbn; lia] | exact NB |].
unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_batch_cf : forall ly S Hp rd b a, ARmcfR B ly S Hp rd -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> aowned B ly S a.
Proof.
intros ly S Hp rd b a M Hb Ha. pose proof (amr_wfr _ _ _ _ _ M) as WF. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (wfr_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kUserMapSize, kFreeArrayOffset in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
eapply own_prim_nonuser_cf; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal). unfold kFreeArrayOffset in Gal.
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs S k o Hk Eb) as IK. rewrite Ec in *. rewrite CS in *. set (xk := o - region_off kBatchClass) in *.
assert (xk <> x). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in X2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_F_low_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> ly_F ly <= a < ly_F ly + kFakeFramesOff -> aowned B ly S a.
Proof.
intros ly S Hp rd a M Ha. pose proof (amr_layout _ _ _ _ _ M) as LO.
unfold kFakeFramesOff, kFakeStackSize in *.
eapply own_ext_cf; [exact M | left; apply Exists_exists; exists (ly_F ly, kFakeStackSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr, kFakeStackSize; cbn; lia] | | unfold kFakeFramesOff; lia].
intros k Hk Hst Hr. pose proof (user_in_extent_cf ly S Hp rd k a M Hk Hr) as HE. pose proof (chunk_vs_F_cf B ly S Hp rd k M Hk) as D.
unfold zdisjoint, kFakeStackSize in D. cbn [fst snd] in D. lia.
Qed.
Lemma own_rinfo_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> aowned B ly S a.
Proof.
intros ly S Hp rd a M Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
eapply own_prim_nonuser_cf; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal). unfold kFreeArrayOffset in Gal.
unfold region_base in *. rewrite !region_off_eq in * by lia.
pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 32 (2 ^ 32) ltac:(lia) ltac:(lia)). change (32 * 2 ^ 32) with (2 ^ 37) in H. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint, kPage, kPrimResvSize in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_fa_cf : forall ly S Hp rd c a, ARmcfR B ly S Hp rd -> 1 <= c <= 31 -> fa_base ly c <= a < fa_base ly c + kFreeArrayMax -> aowned B ly S a.
Proof.
intros ly S Hp rd c a M Hc Ha. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5). unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *.
assert (E32 : region_base ly c = ly_space ly + region_off c) by reflexivity.
eapply own_prim_nonuser_cf; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal). unfold kFreeArrayOffset in Gal.
destruct (Z.eq_dec (prim_class o) c) as [Ec|Hne].
+ rewrite Ec in *. unfold region_base in *. lia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base in *. rewrite !region_off_eq in * by lia.
destruct (Z.lt_ge_cases (prim_class o) c).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (c + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_shadow_cf : forall ly S Hp rd lo len a, ARmcfR B ly S Hp rd ->
In (lo, len) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]) -> lo mod 8 = 0 ->
zdisjoint (lo, len) (ly_F ly, kFakeStackSize) ->
shadow_addr lo <= a < shadow_addr lo + (len + 7) / 8 -> aowned B ly S a.
Proof.
intros ly S Hp rd lo len a M Hin Hlo D Ha.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges_cf B ly S Hp rd M) _ Hin) as (K1 & K2 & K3). cbn [fst snd] in K1, K2, K3.
split.
- right. right. right. right. apply Exists_exists. exists (lo, len). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. exact Ha.
- eapply nc_shadow_cf; [exact M | exact Hlo | exact K1 | exact K3 | exact D | exact Ha].
Qed.
Lemma own_shadow_prim_cf : forall ly S Hp rd g, ARmcfR B ly S Hp rd -> ly_prim ly <= g < ly_prim ly + kPrimResvSize -> aowned B ly S (shadow_addr g).
Proof.
intros ly S Hp rd g M Hg. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (lo_high _ LO) as [H1 H2].
pose proof (lo_prim_al _ LO) as PA. unfold page_aligned in PA.
assert (P8 : ly_prim ly mod 8 = 0). { apply Z.mod_divide; [lia|]. apply Z.mod_divide in PA as [q Hq]; [|lia]. exists (q * 512). lia. }
eapply (own_shadow_cf ly S Hp rd (ly_prim ly) kPrimResvSize); [exact M | | exact P8 | |].
- apply in_app_iff. left. unfold static_extents, owned_extents. cbn. tauto.
- eapply (pairwise_In zdisjoint (static_extents ly) _ _ [_] _); [unfold static_extents, owned_extents; reflexivity | exact (lo_disj _ LO) | left; reflexivity | cbn; tauto].
- apply shadow_addr_in; [exact P8 | unfold kHighMemBeg in H1; lia | exact Hg].
Qed.
Lemma own_shadow_sec_cf : forall ly S Hp rd m len g, ARmcfR B ly S Hp rd -> In (m, len) (sec_extents ly S) -> m <= g < m + len -> aowned B ly S (shadow_addr g).
Proof.
intros ly S Hp rd m len g M Hin Hg. pose proof (amr_placed _ _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) PL _ Hin) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3. unfold page_aligned in PA.
assert (P8 : m mod 8 = 0). { apply Z.mod_divide; [lia|]. apply Z.mod_divide in PA as [q Hq]; [|lia]. exists (q * 512). lia. }
eapply (own_shadow_cf ly S Hp rd m len); [exact M | | exact P8 | |].
- apply in_app_iff. right. apply in_app_iff. left. exact Hin.
- eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly S) (static_extents ly)); [reflexivity | exact PD | exact Hin | unfold static_extents, owned_extents; cbn; tauto].
- apply shadow_addr_in; [exact P8 | unfold kHighMemBeg in I1; lia | exact Hg].
Qed.
Lemma own_shadow_zero_cf : forall ly S Hp rd r i, ARmcfR B ly S Hp rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 -> aowned B ly S (shadow_addr (fst r) + i).
Proof.
intros ly S Hp rd [lo len] i M Hin Hi. cbn [fst snd] in *. pose proof (amr_layout _ _ _ _ _ M) as LO.
assert (P8 : lo mod 8 = 0 /\ 0 <= lo /\ zdisjoint (lo, len) (ly_F ly, kFakeStackSize)).
{ unfold zero_shadow_ranges in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5.
splits.
+ apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [q Hq]; [|lia]. exists (q * 512). lia.
+ unfold kHighMemBeg in T7. lia.
+ apply zdisjoint_sym. eapply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _]); [unfold static_extents; reflexivity | exact (lo_disj _ LO) | unfold owned_extents; cbn; tauto | left; reflexivity].
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amr_syms _ _ _ _ _ M)) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) (lo, len) ltac:(apply in_app_iff; right; exact Hin)) as [I1 I2]. cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO)
ltac:(unfold owned_extents; cbn; tauto) (or_intror (or_introl eq_refl))) as DF.
splits; [exact Z3 | exact Z1 |]. unfold zdisjoint in *. cbn [fst snd] in *. lia. }
destruct P8 as (P8 & P0 & D).
eapply (own_shadow_cf ly S Hp rd lo len); [exact M | apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin | exact P8 | exact D |].
assert (len / 8 <= (len + 7) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma own_shadow_static_cf : forall ly S Hp rd r a, ARmcfR B ly S Hp rd -> In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> aowned B ly S a.
Proof.
intros ly S Hp rd r a M Hin Ha. pose proof (proj1 (Forall_forall _ _) (aso_static _ (amr_syms _ _ _ _ _ M)) r Hin) as (T1 & T2 & T3).
split.
- right. right. right. right. apply Exists_exists. exists r. split; [rewrite !in_app_iff; tauto | unfold in_zr; cbn [fst snd]; exact Ha].
-
pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hin)) as [R1 R2].
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO)
ltac:(unfold owned_extents; cbn; tauto) (or_intror (or_introl eq_refl))) as DF.
eapply (nc_shadow_cf ly S Hp rd a (fst (ly_img ly)) (snd (ly_img ly)) M).
+ rewrite I0. reflexivity.
+ rewrite I0. unfold kImgLo. lia.
+ unfold kImgLo, kImgEnd, kHighMemEnd in *. lia.
+ apply zdisjoint_sym. exact DF.
+ unfold shadow_addr, SHADOW_OFF in *. cbn [fst snd] in *.
pose proof (Z.div_le_mono (fst (ly_img ly)) (fst r) 8 ltac:(lia) ltac:(lia)).
assert ((fst r) / 8 + (snd r + 7) / 8 <= fst (ly_img ly) / 8 + (snd (ly_img ly) + 7) / 8); [|lia].
unfold page_aligned in I3. rewrite I0 in *. unfold kImgLo in *.
apply Z.mod_divide in I3 as [q Hq]; [|lia].
assert (X : (snd (ly_img ly) + 7) / 8 = q * 512) by (rewrite Hq; replace (q * 4096 + 7) with (7 + (q * 512) * 8) by lia; rewrite Z.div_add, Z.div_small by lia; lia).
rewrite X. change (65536 / 8) with 8192.
assert ((fst r) / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8).
{ apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (fst r) 8 ltac:(lia)). pose proof (Z.mul_div_le (snd r + 7) 8 ltac:(lia)). lia. }
assert ((fst r + snd r + 7) / 8 <= (65536 + q * 4096 + 7) / 8) by (apply Z.div_le_mono; lia).
replace ((65536 + q * 4096 + 7) / 8) with (8192 + q * 512) in * by (symmetry; replace (65536 + q * 4096 + 7) with (7 + (8192 + q * 512) * 8) by lia; rewrite Z.div_add, Z.div_small by lia; lia).
lia.
Qed.
Ltac fcons := apply Forall_cons; [cbn; lia|].
Lemma region_cells_owned_cf : forall ly S Hp rd c, ARmcfR B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_owned B ly S) (region_cells S c).
Proof.
intros ly S Hp rd c M Hc. apply (Forall_cbo_of_range B ly S _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; eapply own_rinfo_cf; [exact M | exact Ha]|].
unfold region_cells, kRegionInfoOff. repeat fcons. apply Forall_nil.
Qed.
Lemma cache_cells_owned_cf : forall ly S Hp rd c, ARmcfR B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_owned B ly S) (cache_cells S c).
Proof.
intros ly S Hp rd c M Hc.
assert (OR : owned_range B ly S (ly_T ly) kThreadObjSize).
{ intros a Ha. eapply (own_core_cf ly S Hp rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cbo_of_range B ly S _ (ly_T ly) kThreadObjSize OR).
pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons. apply Forall_nil.
Qed.
Lemma chunk_cells_owned_cf : forall ly S Hp rd k, ARmcfR B ly S Hp rd -> In k (st_chunks S) -> Forall (cell_bytes_owned B ly S) (chunk_cells k).
Proof.
intros ly S Hp rd k M Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : owned_range B ly S (ck_base B ly k) (ck_rz k)).
{ intros a Ha. eapply own_meta_cf; [exact M | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cbo_of_range B ly S _ _ _ OR).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
- repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
Qed.
Lemma area_owned_range_cf : forall ly S Hp rd r, ARmcfR B ly S Hp rd -> In r (asyms_areas B) -> owned_range B ly S (fst r) (snd r).
Proof. intros ly S Hp rd r M Hr a Ha. eapply own_area_cf; eassumption. Qed.
Lemma inst_owned_range_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> owned_range B ly S (as_inst B) 3632.
Proof. intros ly S Hp rd M. apply (area_owned_range_cf ly S Hp rd (as_inst B, 3632) M). cbn. tauto. Qed.
Lemma sec_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (sec_cells S).
Proof.
intros ly S Hp rd M. pose proof (wfr_secondary _ _ _ _ _ (amr_wfr _ _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells.
apply Forall_cons; [eapply cbo_of_range; [exact (inst_owned_range_cf ly S Hp rd M) | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact (inst_owned_range_cf ly S Hp rd M) | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact (inst_owned_range_cf ly S Hp rd M) | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply cbo_of_range; [intros a Ha; eapply (own_core_cf ly S Hp rd (ly_Q ly, kPtrArrayResv)); [exact M | unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
assert (OR : owned_range B ly S (ly_sec ly r) kPage).
{ intros a Ha. eapply own_meta_cf; [exact M | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
unfold kPage in OR.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_owned_cf : forall ly S Hp rd l, ARmcfR B ly S Hp rd -> incl l (all_batches S) -> Forall (cell_bytes_owned B ly S) (batch_cells l).
Proof.
intros ly S Hp rd l M. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfr_quarantine _ _ _ _ _ (amr_wfr _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : owned_range B ly S (ly_space ly + b_self b) kBatchBytes) by (intros a Ha; eapply own_batch_cf; [exact M | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (quar_cells S).
Proof.
intros ly S Hp rd M.
assert (ORT : owned_range B ly S (ly_T ly) kThreadObjSize).
{ intros a Ha. eapply (own_core_cf ly S Hp rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha]. }
pose proof (inst_owned_range_cf ly S Hp rd M) as ORI. unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply cbo_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply cbo_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
eapply batch_cells_owned_cf; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply cbo_of_range; [exact ORI | cbn; lia | cbn; lia]|]).
eapply batch_cells_owned_cf; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
Lemma fs_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (fs_cells S).
Proof.
intros ly S Hp rd M. assert (OR : owned_range B ly S (ly_F ly) kFakeFramesOff) by (intros a Ha; eapply own_F_low_cf; eassumption).
unfold kFakeFramesOff in OR. unfold fs_cells.
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia].
Qed.
Lemma depot_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (depot_cells ly S).
Proof.
intros ly S Hp rd M.
pose proof (area_owned_range_cf ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32) M ltac:(cbn; tauto)) as ORD.
pose proof (area_owned_range_cf ly S Hp rd (as_store B, 32) M ltac:(cbn; tauto)) as ORS. cbn [fst snd] in ORD, ORS.
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply cbo_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORS | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma ialloc_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (ialloc_cells B S).
Proof.
intros ly S Hp rd M. pose proof (aso_ialloc _ (amr_syms _ _ _ _ _ M)) as [I1 I2].
pose proof (area_owned_range_cf ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) M ltac:(cbn; tauto)) as ORA.
pose proof (area_owned_range_cf ly S Hp rd (as_ialloc_flag B, 2) M ltac:(cbn; tauto)) as ORF. cbn [fst snd] in ORA, ORF.
unfold ialloc_cells.
apply Forall_cons; [eapply cbo_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) thread_cells.
Proof.
intros ly S Hp rd M. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply cbo_of_range; [intros a Ha; eapply (own_core_cf ly S Hp rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma acells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (acells_cf B ly S).
Proof.
intros ly S Hp rd M. unfold acells_cf.
apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split;
[|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]]]]].
- apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. eapply incl_Forall; [apply region_cells_cf_incl|]. eapply region_cells_owned_cf; [exact M | lia].
- apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. eapply cache_cells_owned_cf; [exact M | lia].
- apply Forall_flat_map'. intros k Hk. eapply chunk_cells_owned_cf; eassumption.
- eapply sec_cells_owned_cf; exact M.
- eapply quar_cells_owned_cf; exact M.
- eapply fs_cells_owned_cf; exact M.
- eapply depot_cells_owned_cf; exact M.
- eapply ialloc_cells_owned_cf; exact M.
- eapply thread_cells_owned_cf; exact M.
Qed.
Lemma const_cells_owned_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_owned B ly S) (as_const B ly).
Proof.
intros ly S Hp rd M. eapply Forall_impl; [|exact (amr_const_owned _ _ _ _ _ M)]. intros c Hc k Hk.
destruct (Hc k Hk) as [O|[O|O]].
- eapply own_static_cf; [exact M | exact O].
- apply Exists_exists in O as (e & He & Hin). eapply own_core_cf; [exact M | exact He | exact Hin].
- apply Exists_exists in O as (r & Hr & Hin). eapply own_shadow_static_cf; [exact M | exact Hr | exact Hin].
Qed.
Lemma ashadow_owned_cf : forall ly S Hp rd g v, ARmcfR B ly S Hp rd -> ashadow B ly S g = Some v -> aowned B ly S (shadow_addr g).
Proof.
intros ly S Hp rd g v M H. unfold ashadow in H.
destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
destruct (extent_zone_cf ly S Hp rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ eapply own_shadow_prim_cf; [exact M | lia].
+ eapply own_shadow_sec_cf; [exact M | exact Hin | unfold kPage in *; lia].
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c (amr_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S c (amr_wfr _ _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *.
eapply own_shadow_prim_cf; [exact M|]. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
+ eapply own_shadow_sec_cf; [exact M | exact Hin | exact Hg].
Qed.
Lemma al_img_env_cf : forall ly S md, layout_ok ly -> ALedger_cf segs ly S md ->
forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd.
Proof.
intros ly S md LO L sg Hsg. pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img _ LO) as (J0 & J1 & J2 & J3).
unfold kImgLo, kImgEnd in *. lia.
Qed.
Lemma client_band_vis_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> in_band_rw a -> aclient_byte B ly S a -> rd a <> None.
Proof.
intros ly S Hp rd a M Ha [(k & Hk & Hst & Hr)|(fp & Hcp & [Hr|Hr])].
- exfalso. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & _ & G8 & _). rewrite G4 in Hr.
ceil; unfold in_app, ASAN_CEIL, ck_n, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
- exfalso. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as H1. cbn [fst snd] in H1.
pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfr_fakestack _ _ _ _ _ (amr_wfr _ _ _ _ _ M))) fp Hcp) as [Hc Hpos]. cbn [fst snd] in Hc, Hpos.
pose proof (frame_off_bounds (fst fp) (snd fp) Hc Hpos) as FB. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
ceil; unfold in_app, ASAN_CEIL, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kFakeFramesOff, kFakeStackSize in *. lia.
- destruct fp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (proj1 (Forall_forall _ _) (amr_client _ _ _ _ _ M) (ASh (AF (fs_frame_off cid pos)), fs_frame_bytes cid / 8)
ltac:(unfold aclient; rewrite !in_app_iff; right; right; apply in_map_iff; exists (cid, pos); auto)) as V.
specialize (V (a - shadow_addr (frame_addr ly cid pos)) ltac:(cbn [snd]; lia)). cbn [fst aeval] in V. unfold frame_addr in V |- *.
replace (shadow_addr (ly_F ly + fs_frame_off cid pos) + (a - shadow_addr (ly_F ly + fs_frame_off cid pos))) with a in V by lia. exact V.
Qed.
Lemma ahs_pres_transfer_cf : forall ly S Hp S' H mem mem',
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
ARmcfR B ly S Hp (aview segs H mem) -> ahs_pres B ly S H mem ->
(forall a, aview segs H mem a <> None -> aview segs H mem' a <> None) ->
(forall a, in_band_rw a -> H (w64 a) = true -> mem (w64 a) <> None -> mem' (w64 a) <> None) ->
(forall a, in_band_rw a -> aclient_byte B ly S' a -> aclient_byte B ly S a) ->
ahs_pres B ly S' H mem'.
Proof.
intros ly S Hp S' H mem mem' IMG M HA VIS HK CL a Ha NC HV.
destruct (H (w64 a)) eqn:Hh.
-
assert (NCS : ~ aclient_byte B ly S a).
{ intros C. apply (client_band_vis_cf ly S Hp _ a M Ha C). apply aview_band_hidden; assumption. }
exact (HK a Ha Hh (HA a Ha NCS (or_introl Hh))).
-
destruct (aview segs H mem a) as [v|] eqn:AV.
+ apply (proj1 (aview_band segs H mem' a IMG Ha Hh)). apply VIS. rewrite AV. discriminate.
+ assert (NCS : ~ aclient_byte B ly S a) by (intros C; exact (client_band_vis_cf ly S Hp _ a M Ha C AV)).
exfalso. apply (proj2 (aview_band segs H mem a IMG Ha Hh)); [|exact AV].
apply (HA a Ha NCS). destruct HV as [Hv|Hv]; [exfalso; change (YG0n.w64 a) with (w64 a) in Hv; rewrite Hv in Hh; discriminate | right; exact Hv].
Qed.
Lemma hfree_shadow_owned_cf : forall ly S Hp rd g, ARmcfR B ly S Hp rd -> g mod 8 = 0 -> in_app g 8 ->
hfree ly S g -> aowned B ly S (shadow_addr g).
Proof.
intros ly S Hp rd g M Hg HA HF. pose proof HA as [H0 HLH]. split.
- right. right. right. right. apply Exists_exists.
destruct HLH as [HL | [HH1 HH2]].
+ exists lm_zone. split; [rewrite !in_app_iff; right; right; right; right; right; left; reflexivity|].
unfold in_zr, lm_zone. cbn [fst snd]. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kLowMemEnd in *.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. subst g. rewrite Z.div_mul by lia.
change (0 / 8) with 0. change ((2147450880 + 7) / 8) with 268431360. lia.
+ exists hm_zone. split; [rewrite !in_app_iff; right; right; right; right; left; reflexivity|].
unfold in_zr, hm_zone. cbn [fst snd]. ceil; unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. subst g. rewrite Z.div_mul by lia.
change (17594333495296 / 8) with 2199291686912. change ((140737488355328 - 17594333495296 + 7) / 8) with 15392894357504. lia.
- eapply (nc_shadow_cf ly S Hp rd _ g 8 M Hg); [lia | ceil; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg in *; lia | |].
+ unfold hfree in HF. pose proof (proj1 (Forall_forall _ _) HF (ly_F ly, kFakeStackSize)
ltac:(rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as X.
cbn [fst snd] in X. unfold zdisjoint. cbn [fst snd]. lia.
+ change ((8 + 7) / 8) with 1. lia.
Qed.
Lemma hfree_off_extent_cf : forall ly S Hp rd k g, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
g mod 8 = 0 -> hfree ly S g -> g + 8 <= ck_base B ly k \/ ck_base B ly k + ck_extent k <= g.
Proof.
intros ly S Hp rd k g M Hk Hg HF. unfold hfree in HF.
destruct (extent_zone_cf ly S Hp rd k M Hk) as [[P1 P2] | (m & len & Hin & E1 & E2)].
- pose proof (proj1 (Forall_forall _ _) HF (ly_prim ly, kPrimResvSize)
ltac:(rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as X.
cbn [fst snd] in X. lia.
- pose proof (proj1 (Forall_forall _ _) HF (m, len) ltac:(rewrite !in_app_iff; right; right; exact Hin)) as X. cbn [fst snd] in X. unfold kPage in *. lia.
Qed.
Lemma hfree_shadow_off_range_cf : forall ly S Hp rd k lo len g, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k <= lo -> lo + len <= ck_base B ly k + ck_extent k -> lo mod 8 = 0 -> 0 <= len ->
g mod 8 = 0 -> hfree ly S g ->
~ (shadow_addr lo <= shadow_addr g < shadow_addr lo + (len + 7) / 8).
Proof.
intros ly S Hp rd k lo len g M Hk H1 H2 Hlo Hlen Hg HF [R1 R2].
pose proof (hfree_off_extent_cf ly S Hp rd k g M Hk Hg HF) as X.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. apply Z.mod_divide in Hlo as [ql Hql]; [|lia]. subst g lo.
unfold shadow_addr, SHADOW_OFF in R1, R2. rewrite !Z.div_mul in R1, R2 by lia.
pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)) as M1. pose proof (Z.div_pos (len + 7) 8 ltac:(lia) ltac:(lia)) as M2.
assert (M3 : len <= 8 * ((len + 7) / 8)) by (pose proof (Z.div_mod (len + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)); lia).
destruct X as [X|X]; [nia|].
assert (q - ql < (len + 7) / 8) by lia. assert (len <= 8 * (q - ql)) by lia.
assert ((len + 7) / 8 <= q - ql) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma ahs_transfer_cf : forall ly S Hp S' H mem mem',
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
ARmcfR B ly S Hp (aview segs H mem) -> ahs B ly S H mem ->
(forall a, aview segs H mem a <> None -> aview segs H mem' a <> None) ->
(forall a, in_band_rw a -> H (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
(forall a, in_band_rw a -> aclient_byte B ly S' a -> aclient_byte B ly S a) ->
sec_extents ly S' = sec_extents ly S ->
(forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> H (w64 (shadow_addr g)) = false ->
aview segs H mem' (shadow_addr g) = aview segs H mem (shadow_addr g)) ->
ahs B ly S' H mem'.
Proof.
intros ly S Hp S' H mem mem' IMG M [HA HZ] VIS HK CL SE AG. split.
- apply (ahs_pres_transfer_cf ly S Hp S' H mem mem' IMG M HA VIS); [|exact CL]. intros a Ha Hh Hm. rewrite (HK a Ha Hh). exact Hm.
- exact (ahz_transfer segs ly S S' H mem mem' IMG HZ SE HK AG).
Qed.
Theorem AR_frame_law_ok_cf : AR_frame_law_cf segs B.
Proof.
intros ly S Hp W mem md mem' md' (M & L & BUD & MW & HS) AGR VIS Hvm Hlz He HK.
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
assert (AG : forall a, aowned B ly S a -> rd' a = rd a).
{ intros a Ha. apply AGR; [|exact Ha]. pose proof (AR_owned_low_law_ok_cf segs B ly S Hp W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha).
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR. lia. }
split; [|split; [eapply YG0qcf.ALedger_same_cf; eassumption | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer_cf ly S Hp S (w_H W) mem mem' (al_img_env_cf ly S md (amr_layout _ _ _ _ _ M) L) M HS VIS HK ltac:(intros a _ C; exact C) eq_refl
ltac:(intros g Hg HA HF _; apply AG; eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HF]))]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor; try assumption.
(* field round 2's two cells: the exhausted byte is in the owned RegionInfo record, the buffer's object is owned
   static (amr_cells_owned's rows); field round 3's two cells are owned static (amr_pf_owned); the frame law's
   agreement covers them all. *)
all: try (first
  [ (apply (YGcfInstBase.exh_cell_cf_frame B ly ly S S rd rd' Xexh); [intros c; reflexivity|];
     intros c Hc; destruct Xown as [EXO _]; unfold YGcfImgRows.EXH_OFF_t in EXO;
     change (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off))
       with (ly_space ly + (kRegionInfoOff + 128 * c + cf_exh_off));
     apply AG; eapply own_rinfo_cf; [exact M0|]; rewrite EXO; unfold kRegionInfoOff; lia)
  | (apply (YGcfInstBase.errb_cells_cf_frame B ly ly S S rd rd' Xerrb); try reflexivity;
     [intros a Ha; apply AG; eapply own_static_cf; [exact M0 | exact (proj1 (proj2 Xown) a Ha)] | exact VIS])
  | (apply (YG0qcf.pf_cells_frame_cf B ly rd rd'); [|exact Xpf];
     intros a Ha; apply AG; eapply own_static_cf; [exact M0 | exact (proj1 (proj1 Xpfo a Ha))]) ]).
- eapply Forall_cell_holds_agree; [exact AG | eapply const_cells_owned_cf; exact M0 | assumption].
- eapply Forall_cell_holds_agree; [exact AG | eapply acells_owned_cf; exact M0 | assumption].
-
intros c i v Hc Hi Hv k Hk. rewrite AG; [exact (Xfa c i v Hc Hi Hv k Hk)|].
pose proof (wfr_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
eapply own_fa_cf; [exact M0 | exact Hc | lia].
-
intros cid pos Hc Hpos. rewrite AG; [exact (Xflags cid pos Hc Hpos)|].
pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr, kFakeFlagsOff in *. eapply own_F_low_cf; [exact M0 | lia].
-
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. rewrite AG; [exact (H2 k Hk)|].
eapply (own_area_cf ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ unfold depot_ids. pose proof (depot_len_bound _ _ Xuni (wfr_depot _ _ _ _ _ Xwf)) as DL. unfold DEPOT_MAX in DL. lia. }
assert (OR : forall k, 0 <= k < 16 -> aowned B ly S (ly_NB ly + 16 * id + k)).
{ intros k Hk. eapply (own_core_cf ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
split; intros k Hk; rewrite AG; auto; [apply OR; lia|]. replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. apply OR. lia.
-
intros g v Hg Hv0. rewrite AG by (eapply ashadow_owned_cf; [exact M0 | exact Hv0]).
exact (Xshadow g v Hg Hv0).
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. fold (shadow_addr (fst r)).
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)). rewrite AG; [exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi)|].
eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi].
- eapply Forall_range_vis_keep; [exact VIS | assumption].
- eapply Forall_range_vis_keep; [exact VIS | assumption].
- eapply Forall_range_vis_keep; [exact VIS | assumption].
-
apply Forall_forall. intros r Hr i Hi. rewrite AG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
pose proof (aso_ialloc _ Xsyms) as [I1 I2].
eapply (own_area_cf ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
Qed.
End s.
End j.

(* ------------------------------------------------------------------------------------------------------------ *)
(* YG0tcf.v:40-487 over ARcfR: the cells' footprint (fp_zones and the *_in_cf / *_nf_cf family), the zero-shadow
   range facts and the shadow-address zone facts.  YG0tcf's three LAWS (astack_free / astack_malloc / head frame,
   :478 on) are NOT ported: they rest on WfP_cf-level model lemmas (YG05cf.stack_free_ok_cf) that a cut, which has
   only WfR_cf, does not carry, and the drain's walks do not use them. *)
#[local] Ltac ceil ::= let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section u.
Variable segs : list Segment.
Variable B : asyms.
Local Abbreviation cell_bytes_nf := (YG0t.cell_bytes_nf B).
Local Abbreviation cnf_of_range := (YG0t.cnf_of_range B).
Local Abbreviation Forall_cnf_of_range := (YG0t.Forall_cnf_of_range B).
Local Abbreviation Forall_cell_holds_agree_nf := (YG0t.Forall_cell_holds_agree_nf B).
Local Abbreviation ahs_transfer_grow := (YG0t.ahs_transfer_grow segs B).
Lemma nf_sec_cf : forall ly S Hp rd e a, ARmcfR B ly S Hp rd -> In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly S Hp rd e a M He Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. eapply nf_of_disjoint; [exact LO | | |exact Ha].
- exact (pairwise_In zdisjoint _ e (ly_F ly, kFakeStackSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)).
- pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ M)) _ He) as (_ & [I0 I1] & _). lia.
Qed.
Lemma nf_img_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> in_zr a (ly_img ly) -> nf ly a.
Proof.
intros ly S Hp rd a M Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). unfold in_zr in Ha.
eapply (nf_static_ext ly (ly_img ly)); [exact LO | unfold static_extents; apply in_app_iff; right; right; left; reflexivity | | exact Ha].
intros E. pose proof (f_equal snd E) as E2. cbn in E2. unfold kImgLo, kImgEnd, kFakeStackSize in *. lia.
Qed.
Lemma nf_core_cf : forall ly S Hp rd e a, ARmcfR B ly S Hp rd -> In e (core_extents ly) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly S Hp rd e a M He Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. eapply nf_static_ext; [exact LO | | | exact Ha].
- unfold core_extents in He. unfold static_extents, owned_extents. cbn in He |- *. intuition.
- intros ->. unfold core_extents in He. cbn in He.
destruct He as [E|[E|[E|[E|[E|[E|[]]]]]]]; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPtrArrayResv, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kFakeStackSize in E2; lia.
Qed.
Lemma nf_F_low_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> ly_F ly + 88 <= a < ly_F ly + kFakeFlagsOff -> nf ly a.
Proof.
intros ly S Hp rd a M Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. destruct (F_app ly LO) as (F0 & FZ & _). unfold nf. split; [right; lia |].
apply (nf2_app ly a LO). unfold kFakeFlagsOff, kFakeStackSize in *. lia.
Qed.
Lemma nf_shadow_static_cf : forall ly S Hp rd r a, ARmcfR B ly S Hp rd -> In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> nf ly a.
Proof.
intros ly S Hp rd r a M Hr Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. apply (nf_shadow_hull ly a LO).
pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amr_syms _ _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
unfold shadow_addr in *.
pose proof (Z.div_le_mono (fst (ly_img ly)) (fst r) 8 ltac:(lia) ltac:(lia)).
unfold page_aligned in I3. apply Z.mod_divide in I3 as [q Hq]; [|lia]. rewrite I0 in *. unfold kImgLo in *. change (65536 / 8) with 8192 in *.
assert (E2 : snd (ly_img ly) / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_div_mult; lia).
pose proof (Z_div_mod_eq_full (fst r) 8) as DM1. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MB1.
pose proof (Z_div_mod_eq_full (snd r + 7) 8) as DM2. pose proof (Z.mod_pos_bound (snd r + 7) 8 ltac:(lia)) as MB2.
rewrite E2. lia.
Qed.

(* ----------------------------------------------------------------------------
   The cells' footprint, parametrised over the address predicate P that every byte a cell reads
   satisfies. cgif's YG0t.v:19-337 fixes P := nf ly (the bytes outside the fake stack and its
   shadow); the heap-head frame law below takes P := not chunk_shadow_cf (not the shadow byte of a
   chunk granule). fp_zones lists the address zones the cells live in; each _in_cf lemma is cgif's
   _nf proof with each nf point fact replaced by a zone, and cgif's _nf_cf names are the instances
   at P := nf ly. *)
Definition cell_bytes_in (P : Z -> Prop) (ly : alayout) (c : acell) : Prop :=
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> P (aeval B ly (c_at c) + k).
Record fp_zones (P : Z -> Prop) (ly : alayout) (S : astate) : Prop := {
fz_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> P a;
fz_core : forall e a, In e (core_extents ly) -> fst e <= a < fst e + snd e -> P a;
fz_img : forall a, in_zr a (ly_img ly) -> P a;
fz_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> P a;
fz_F_low : forall a, ly_F ly + 88 <= a < ly_F ly + kFakeFlagsOff -> P a;
fz_shadow_static : forall r a, In r (as_owned_static B) -> shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> P a
}.
Lemma fp_zones_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones (nf ly) ly S.
Proof.
intros ly S Hp rd M. pose proof (amr_layout _ _ _ _ _ M) as LO. constructor.
- intros a Ha. exact (nf_prim ly a LO Ha).
- intros e a He Ha. exact (nf_core_cf ly S Hp rd e a M He Ha).
- intros a Ha. exact (nf_img_cf ly S Hp rd a M Ha).
- intros e a He Ha. exact (nf_sec_cf ly S Hp rd e a M He Ha).
- intros a Ha. exact (nf_F_low_cf ly S Hp rd a M Ha).
- intros r a Hr Ha. exact (nf_shadow_static_cf ly S Hp rd r a M Hr Ha).
Qed.
Lemma cbi_of_range : forall P ly c lo len, (forall a, lo <= a < lo + len -> P a) ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_bytes_in P ly c.
Proof. intros P ly c lo len OR H1 H2 k Hk. apply OR. lia. Qed.
Lemma Forall_cbi_of_range : forall P ly l lo len, (forall a, lo <= a < lo + len -> P a) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l -> Forall (cell_bytes_in P ly) l.
Proof. intros P ly l lo len OR H. eapply Forall_impl; [|exact H]. intros c [H1 H2]. eapply cbi_of_range; eauto. Qed.
Lemma Forall_cell_holds_agree_in : forall P ly S rd rd' l,
(forall a, aowned B ly S a -> P a -> rd' a = rd a) -> Forall (cell_bytes_owned B ly S) l -> Forall (cell_bytes_in P ly) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros P ly S rd rd' l AG OW NF H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros k Hk.
apply AG; [exact (proj1 (Forall_forall _ _) OW c Hc k Hk) | exact (proj1 (Forall_forall _ _) NF c Hc k Hk)].
Qed.
Lemma static_in_cf : forall P ly S Hp rd a, ARmcfR B ly S Hp rd -> fp_zones P ly S -> Exists (in_zr a) (as_owned_static B) -> P a.
Proof.
intros P ly S Hp rd a M FZ H. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [S1 S2].
apply (fz_img _ _ _ FZ). unfold in_zr. lia.
Qed.
Lemma area_in_cf : forall P ly S Hp rd r a, ARmcfR B ly S Hp rd -> fp_zones P ly S -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> P a.
Proof.
intros P ly S Hp rd r a M FZ Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amr_syms _ _ _ _ _ M)) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [X1 X2]). eapply static_in_cf; [exact M | exact FZ |]. apply Exists_exists. exists r'. split; [exact Hr'|]. unfold in_zr. lia.
Qed.
Lemma rinfo_in_cf : forall P ly S Hp rd a, ARmcfR B ly S Hp rd -> fp_zones P ly S -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> P a.
Proof.
intros P ly S Hp rd a M FZ Ha. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
apply (fz_prim _ _ _ FZ). lia.
Qed.
Lemma meta_in_cf : forall P ly S Hp rd k a, ARmcfR B ly S Hp rd -> fp_zones P ly S -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> P a.
Proof.
intros P ly S Hp rd k a M FZ Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amr_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
apply (fz_prim _ _ _ FZ). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
apply (fz_sec _ _ _ FZ (ly_sec ly r, sec_map_size (ck_req k)) a Gin). cbn [fst snd]. unfold kPage in *. lia.
Qed.
Lemma batch_in_cf : forall P ly S Hp rd b a, ARmcfR B ly S Hp rd -> fp_zones P ly S -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> P a.
Proof.
intros P ly S Hp rd b a M FZ Hb Ha. pose proof (amr_wfr _ _ _ _ _ M) as WF. pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (wfr_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kFreeArrayOffset in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
apply (fz_prim _ _ _ FZ). lia.
Qed.
Ltac fcons' := apply Forall_cons; [cbn; lia|].
Lemma region_cells_in_cf : forall P ly S Hp rd c, ARmcfR B ly S Hp rd -> fp_zones P ly S -> 1 <= c <= 31 -> Forall (cell_bytes_in P ly) (region_cells S c).
Proof.
intros P ly S Hp rd c M FZ Hc. apply (Forall_cbi_of_range P ly _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; eapply rinfo_in_cf; [exact M | exact FZ | exact Ha]|].
unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma cache_cells_in_cf : forall P ly S Hp rd c, ARmcfR B ly S Hp rd -> fp_zones P ly S -> 1 <= c <= 31 -> Forall (cell_bytes_in P ly) (cache_cells S c).
Proof.
intros P ly S Hp rd c M FZ Hc.
assert (OR : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> P a).
{ intros a Ha. apply (fz_core _ _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cbi_of_range P ly _ (ly_T ly) kThreadObjSize OR).
pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons'. apply Forall_nil.
Qed.
Lemma chunk_cells_in_cf : forall P ly S Hp rd k, ARmcfR B ly S Hp rd -> fp_zones P ly S -> In k (st_chunks S) -> Forall (cell_bytes_in P ly) (chunk_cells k).
Proof.
intros P ly S Hp rd k M FZ Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : forall a, ck_base B ly k <= a < ck_base B ly k + ck_rz k -> P a).
{ intros a Ha. eapply meta_in_cf; [exact M | exact FZ | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cbi_of_range P ly _ _ _ OR).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
- repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
Qed.
Lemma sec_cells_in_cf : forall P ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (sec_cells S).
Proof.
intros P ly S Hp rd M FZ. pose proof (wfr_secondary _ _ _ _ _ (amr_wfr _ _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_inst B, 3632) a M FZ ltac:(cbn; tauto) Ha)).
unfold sec_cells.
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply cbi_of_range; [intros a Ha; apply (fz_core _ _ _ FZ (ly_Q ly, kPtrArrayResv)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
assert (OR : forall a, ly_sec ly r <= a < ly_sec ly r + kPage -> P a).
{ intros a Ha. eapply meta_in_cf; [exact M | exact FZ | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
unfold kPage in OR.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_in_cf : forall P ly S Hp rd l, ARmcfR B ly S Hp rd -> fp_zones P ly S -> incl l (all_batches S) -> Forall (cell_bytes_in P ly) (batch_cells l).
Proof.
intros P ly S Hp rd l M FZ. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfr_quarantine _ _ _ _ _ (amr_wfr _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> P a)
by (intros a Ha; eapply batch_in_cf; [exact M | exact FZ | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_in_cf : forall P ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (quar_cells S).
Proof.
intros P ly S Hp rd M FZ.
assert (ORT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> P a).
{ intros a Ha. apply (fz_core _ _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_inst B, 3632) a M FZ ltac:(cbn; tauto) Ha)).
unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply cbi_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
eapply batch_cells_in_cf; [exact M | exact FZ | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|]).
eapply batch_cells_in_cf; [exact M | exact FZ | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
Lemma fs_hdr_in_cf : forall P ly S, fp_zones P ly S -> Forall (cell_bytes_in P ly) fs_hdr.
Proof.
intros P ly S FZ. assert (OR : forall a, ly_F ly + 88 <= a < ly_F ly + 88 + (kFakeFlagsOff - 88) -> P a) by (intros a Ha; apply (fz_F_low _ _ _ FZ); lia).
unfold kFakeFlagsOff in OR. unfold fs_hdr.
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma depot_cells_in_cf : forall P ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (depot_cells ly S).
Proof.
intros P ly S Hp rd M FZ.
assert (ORD : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32) a M FZ ltac:(cbn; tauto) Ha)).
assert (ORS : forall a, as_store B <= a < as_store B + 32 -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_store B, 32) a M FZ ltac:(cbn; tauto) Ha)).
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply cbi_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORS | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma ialloc_cells_in_cf : forall P ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (ialloc_cells B S).
Proof.
intros P ly S Hp rd M FZ. pose proof (aso_ialloc _ (amr_syms _ _ _ _ _ M)) as [I1 I2].
assert (ORA : forall a, as_ialloc_lo B <= a < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B) -> P a)
by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) a M FZ ltac:(cbn; tauto) Ha)).
assert (ORF : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> P a)
by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_ialloc_flag B, 2) a M FZ ltac:(cbn; tauto) Ha)).
unfold ialloc_cells.
apply Forall_cons; [eapply cbi_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_in_cf : forall P ly S, fp_zones P ly S -> Forall (cell_bytes_in P ly) thread_cells.
Proof.
intros P ly S FZ. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply cbi_of_range; [intros a Ha; apply (fz_core _ _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma const_cells_in_cf : forall P ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (as_const B ly).
Proof.
intros P ly S Hp rd M FZ. eapply Forall_impl; [|exact (amr_const_owned _ _ _ _ _ M)]. intros c Hc k Hk.
destruct (Hc k Hk) as [O|[O|O]].
- eapply static_in_cf; [exact M | exact FZ | exact O].
- apply Exists_exists in O as (e & He & Hin). exact (fz_core _ _ _ FZ e _ He Hin).
- apply Exists_exists in O as (r & Hr & Hin). exact (fz_shadow_static _ _ _ FZ r _ Hr Hin).
Qed.
(* Every cell of acells_cf, given P on the frame-hint words [F, F + 88) too. *)
Lemma acells_in_cf : forall P ly S Hp rd, ARmcfR B ly S Hp rd -> fp_zones P ly S ->
(forall a, ly_F ly <= a < ly_F ly + 88 -> P a) -> Forall (cell_bytes_in P ly) (acells_cf B ly S).
Proof.
intros P ly S Hp rd M FZ HF. unfold acells_cf. rewrite (fs_cells_split S).
assert (RCF : forall c, In c (zseq 1 31) -> Forall (cell_bytes_in P ly) (region_cells_cf S c)).
{ intros c Hc. apply Forall_forall. intros x Hx.
apply (proj1 (Forall_forall _ _) (region_cells_in_cf P ly S Hp rd c M FZ ltac:(pose proof (zseq_In' 1 31 c Hc); lia))).
eapply region_cells_cf_incl. exact Hx. }
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ RCF)|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_in_cf P ly S Hp rd c M FZ ltac:(pose proof (zseq_In' 1 31 c Hc); lia)))|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_in_cf P ly S Hp rd k M FZ Hk))|].
apply Forall_app; split; [exact (sec_cells_in_cf P ly S Hp rd M FZ)|].
apply Forall_app; split; [exact (quar_cells_in_cf P ly S Hp rd M FZ)|].
apply Forall_app; split.
{ apply Forall_app; split; [exact (fs_hdr_in_cf P ly S FZ)|]. unfold fs_hints. apply Forall_forall. intros c Hc.
apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
eapply cbi_of_range; [exact (fun a Ha => HF a Ha) | cbn; lia | cbn [c_at c_w z8 c8 aeval aoff fst snd]; cbn; lia]. }
apply Forall_app; split; [exact (depot_cells_in_cf P ly S Hp rd M FZ)|].
apply Forall_app; split; [exact (ialloc_cells_in_cf P ly S Hp rd M FZ)|].
exact (thread_cells_in_cf P ly S FZ).
Qed.
(* cgif's YG0t.v nf family: the instances at P := nf ly. *)
Lemma nf_static_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> Exists (in_zr a) (as_owned_static B) -> nf ly a.
Proof. intros ly S Hp rd a M. exact (static_in_cf (nf ly) ly S Hp rd a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_area_cf : forall ly S Hp rd r a, ARmcfR B ly S Hp rd -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> nf ly a.
Proof. intros ly S Hp rd r a M. exact (area_in_cf (nf ly) ly S Hp rd r a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_rinfo_cf : forall ly S Hp rd a, ARmcfR B ly S Hp rd -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> nf ly a.
Proof. intros ly S Hp rd a M. exact (rinfo_in_cf (nf ly) ly S Hp rd a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_meta_cf : forall ly S Hp rd k a, ARmcfR B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> nf ly a.
Proof. intros ly S Hp rd k a M. exact (meta_in_cf (nf ly) ly S Hp rd k a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_batch_cf : forall ly S Hp rd b a, ARmcfR B ly S Hp rd -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> nf ly a.
Proof. intros ly S Hp rd b a M. exact (batch_in_cf (nf ly) ly S Hp rd b a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma region_cells_nf_cf : forall ly S Hp rd c, ARmcfR B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_nf ly) (region_cells S c).
Proof. intros ly S Hp rd c M. exact (region_cells_in_cf (nf ly) ly S Hp rd c M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma cache_cells_nf_cf : forall ly S Hp rd c, ARmcfR B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_nf ly) (cache_cells S c).
Proof. intros ly S Hp rd c M. exact (cache_cells_in_cf (nf ly) ly S Hp rd c M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma chunk_cells_nf_cf : forall ly S Hp rd k, ARmcfR B ly S Hp rd -> In k (st_chunks S) -> Forall (cell_bytes_nf ly) (chunk_cells k).
Proof. intros ly S Hp rd k M. exact (chunk_cells_in_cf (nf ly) ly S Hp rd k M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma area_nf_range_cf : forall ly S Hp rd r, ARmcfR B ly S Hp rd -> In r (asyms_areas B) -> nf_range ly (fst r) (snd r).
Proof. intros ly S Hp rd r M Hr a Ha. eapply nf_area_cf; eassumption. Qed.
Lemma inst_nf_range_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> nf_range ly (as_inst B) 3632.
Proof. intros ly S Hp rd M. apply (area_nf_range_cf ly S Hp rd (as_inst B, 3632) M). cbn. tauto. Qed.
Lemma sec_cells_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) (sec_cells S).
Proof. intros ly S Hp rd M. exact (sec_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma batch_cells_nf_cf : forall ly S Hp rd l, ARmcfR B ly S Hp rd -> incl l (all_batches S) -> Forall (cell_bytes_nf ly) (batch_cells l).
Proof. intros ly S Hp rd l M. exact (batch_cells_in_cf (nf ly) ly S Hp rd l M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma quar_cells_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) (quar_cells S).
Proof. intros ly S Hp rd M. exact (quar_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma fs_hdr_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) fs_hdr.
Proof. intros ly S Hp rd M. exact (fs_hdr_in_cf (nf ly) ly S (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma depot_cells_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) (depot_cells ly S).
Proof. intros ly S Hp rd M. exact (depot_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma ialloc_cells_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) (ialloc_cells B S).
Proof. intros ly S Hp rd M. exact (ialloc_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma thread_cells_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) thread_cells.
Proof. intros ly S Hp rd M. exact (thread_cells_in_cf (nf ly) ly S (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma const_cells_nf_cf : forall ly S Hp rd, ARmcfR B ly S Hp rd -> Forall (cell_bytes_nf ly) (as_const B ly).
Proof. intros ly S Hp rd M. exact (const_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma am_cells_set_fs_cf : forall ly S Hp rd rd' f,
ARmcfR B ly S Hp rd -> (forall a, aowned B ly S a -> nf ly a -> rd' a = rd a) ->
Forall (cell_holds B ly rd') (fs_hints f) ->
Forall (cell_holds B ly rd') (acells_cf B ly (set_fs f S)).
Proof.
intros ly S Hp rd rd' f M AGN HH. pose proof (amr_cells _ _ _ _ _ M) as X. pose proof (acells_owned_cf B ly S Hp rd M) as OW.
unfold acells_cf in X, OW |- *.
change (flat_map (region_cells_cf (set_fs f S)) (zseq 1 31)) with (flat_map (region_cells_cf S) (zseq 1 31)).
change (flat_map (cache_cells (set_fs f S)) (zseq 1 31)) with (flat_map (cache_cells S) (zseq 1 31)).
change (st_chunks (set_fs f S)) with (st_chunks S). change (sec_cells (set_fs f S)) with (sec_cells S).
change (quar_cells (set_fs f S)) with (quar_cells S). change (depot_cells ly (set_fs f S)) with (depot_cells ly S).
change (ialloc_cells B (set_fs f S)) with (ialloc_cells B S).
rewrite (fs_cells_split (set_fs f S)). change (st_fs (set_fs f S)) with f. rewrite (fs_cells_split S) in X, OW.
apply Forall_app in X as [XR X]. apply Forall_app in X as [XC X]. apply Forall_app in X as [XK X]. apply Forall_app in X as [XS X].
apply Forall_app in X as [XQ X]. apply Forall_app in X as [XF X]. apply Forall_app in X as [XD X]. apply Forall_app in X as [XI XT].
apply Forall_app in XF as [XFH _].
apply Forall_app in OW as [OWR OW]. apply Forall_app in OW as [OWC OW]. apply Forall_app in OW as [OWK OW]. apply Forall_app in OW as [OWS OW].
apply Forall_app in OW as [OWQ OW]. apply Forall_app in OW as [OWF OW]. apply Forall_app in OW as [OWD OW]. apply Forall_app in OW as [OWI OWT].
apply Forall_app in OWF as [OWFH _].
assert (RCF : forall c, In c (zseq 1 31) -> Forall (cell_bytes_nf ly) (region_cells_cf S c)).
{ intros c Hc. apply Forall_forall. intros x Hx.
apply (proj1 (Forall_forall _ _) (region_cells_nf_cf ly S Hp rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia))).
eapply region_cells_cf_incl. exact Hx. }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWR (Forall_flat_map'' _ _ _ RCF) XR). }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWC (Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_nf_cf ly S Hp rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia))) XC). }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWK (Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_nf_cf ly S Hp rd k M Hk)) XK). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWS (sec_cells_nf_cf ly S Hp rd M) XS). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWQ (quar_cells_nf_cf ly S Hp rd M) XQ). }
apply Forall_app; split.
{ apply Forall_app; split; [exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWFH (fs_hdr_nf_cf ly S Hp rd M) XFH) | exact HH]. }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWD (depot_cells_nf_cf ly S Hp rd M) XD). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWI (ialloc_cells_nf_cf ly S Hp rd M) XI). }
exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWT (thread_cells_nf_cf ly S Hp rd M) XT).
Qed.
Lemma zshadow_range_facts_cf : forall ly S Hp rd r, ARmcfR B ly S Hp rd -> In r (zero_shadow_ranges B ly) ->
fst r mod 8 = 0 /\ 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kHighMemEnd /\ zdisjoint r (ly_F ly, kFakeStackSize).
Proof.
intros ly S Hp rd [lo len] M Hin. cbn [fst snd]. pose proof (amr_layout _ _ _ _ _ M) as LO.
unfold zero_shadow_ranges in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5.
splits.
+ apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [q Hq]; [|lia]. exists (q * 512). lia.
+ unfold kHighMemBeg in T7. lia.
+ lia.
+ lia.
+ apply zdisjoint_sym. eapply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _]); [unfold static_extents; reflexivity | exact (lo_disj _ LO) | unfold owned_extents; cbn; tauto | left; reflexivity].
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amr_syms _ _ _ _ _ M)) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) (lo, len) ltac:(apply in_app_iff; right; exact Hin)) as [R1 R2]. cbn [fst snd] in R1, R2.
pose proof (hull_below_F ly LO) as HF.
splits; [exact Z3 | exact Z1 | exact Z2 | unfold kLowMemEnd, kHighMemEnd in *; lia |]. unfold zdisjoint. cbn [fst snd]. left. lia.
Qed.
Lemma zshadow_low_cf : forall ly S Hp rd r i, ARmcfR B ly S Hp rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
SHADOW_OFF <= shadow_addr (fst r) + i < kHighMemBeg.
Proof.
intros ly S Hp rd r i M Hr Hi. destruct (zshadow_range_facts_cf ly S Hp rd r M Hr) as (A1 & A2 & A3 & A4 & A5).
assert (DM : snd r / 8 <= (snd r + 7) / 8) by (apply Z.div_le_mono; lia).
pose proof (shadow_range_below (fst r) (snd r) A2 A3 A4). pose proof (proj1 (shadow_addr_bounds (fst r) A2)). lia.
Qed.
Lemma zshadow_not_frame_shadow_cf : forall ly S Hp rd r i cid pos, ARmcfR B ly S Hp rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ in_zr (shadow_addr (fst r) + i) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S Hp rd r i cid pos M Hr Hi Hc HpQ IN. unfold in_zr in IN. cbn [fst snd] in IN.
destruct (zshadow_range_facts_cf ly S Hp rd r M Hr) as (A1 & A2 & A3 & A4 & D). unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (frame_off_bounds cid pos Hc HpQ) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. unfold frame_addr, shadow_addr in *.
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. apply Z.mod_divide in B3 as [qo Hqo]; [|lia]. apply Z.mod_divide in B5 as [qb Hqb]; [|lia].
apply Z.mod_divide in A1 as [qr Hqr]; [|lia].
assert (E1 : (ly_F ly + fs_frame_off cid pos) / 8 = qf * 512 + qo * 8) by (rewrite Hqf, Hqo; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (E2 : fs_frame_bytes cid / 8 = qb * 8) by (rewrite Hqb; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (E3 : fst r / 8 = qr) by (rewrite Hqr; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
rewrite E1, E2, E3 in IN. pose proof (Z.div_le_upper_bound (snd r) 8 (snd r) ltac:(lia) ltac:(lia)) as DU.
assert (DL : 8 * (snd r / 8) <= snd r) by (apply Z.mul_div_le; lia).
clear - IN D B1 B2 B6 Hqf Hqo Hqb Hqr B4 Hc Hi DL. unfold kFakeFramesOff in *. nia.
Qed.
Lemma ashadow_app_cf : forall ly S Hp rd g v, ARmcfR B ly S Hp rd -> ashadow B ly S g = Some v -> 4096 <= g /\ g + 7 <= kHighMemEnd.
Proof.
intros ly S Hp rd g v M H. pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_high _ LO) as [P1 P2].
unfold ashadow in H. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg]. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & _).
assert (ck_extent k mod 8 = 0 /\ ck_base B ly k mod 8 = 0) as [E1 E2].
{ pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & G3 & _ & _ & _ & G7 & _ & GG). split; [|apply Z.mod_divide in G3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult].
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & -> & _). pose proof (class_ok (prim_class o) ltac:(lia)) as (_ & K2 & _).
apply Z.mod_divide in K2 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult.
- destruct GG as (_ & Gp & _ & -> & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (_ & _ & _ & _ & SM & _).
apply Z.mod_divide in SM as [q Hq]; [|unfold kPage; lia]. rewrite Hq. unfold kPage. replace (q * 4096 - 4096) with ((q * 512 - 512) * 8) by lia. apply Z_mod_mult. }
apply Z.mod_divide in E1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in E2 as [q2 Hq2]; [|lia]. destruct G1 as [G0 _].
ceil; unfold ASAN_CEIL, kHighMemEnd in *. split; [lia|]. clear - Hg Hq1 Hq2 G2 CR0. nia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (wrc_mapped_al _ _ _ _ _ _ CL) as A4.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S c (amr_wfr _ _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin, MB. unfold region_base in *.
apply Z.mod_divide in R3 as [q3 Hq3]; [|lia]. apply Z.mod_divide in A4 as [q4 Hq4]; [|lia].
ceil; unfold ASAN_CEIL, kHighMemEnd, kHighMemBeg, kPrimResvSize in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | nia]).
+ pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ M)) _ Hin) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
ceil; unfold YG0f.page_aligned, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg in *.
apply Z.mod_divide in PA as [q Hq]; [|lia]. split; [lia | clear - Hg Hq I2 I3 CR0; nia].
Qed.
Lemma ashadow_low_cf : forall ly S Hp rd g v, ARmcfR B ly S Hp rd -> ashadow B ly S g = Some v -> SHADOW_OFF <= shadow_addr g < kHighMemBeg.
Proof.
intros ly S Hp rd g v M H. destruct (ashadow_app_cf ly S Hp rd g v M H) as [Ga Gb].
destruct (shadow_addr_bounds g ltac:(lia)) as [X Y]. split; [exact X | exact (Y Gb)].
Qed.
End u.
End T.

End RL.
