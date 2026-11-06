(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstBase.v, sha256 c317bf863497bfe13bb096f196c1a83fa5d0cc48d1ee3cd9ab9f5d401a05cde9 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree (lane W's AllocG / DeallocG / DMspec / DMiface / ImgBaseDG / DGif0, the F1 core's
   YGcfRehidePost / YGcfRecStep, and the per-image cf files of this carry) name lib/B; a sentence is split at a directory
   change, the module order kept.
*)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The generic cf INSTANCE layer, base file (lane M).

   TWO relations, one text for every unit that has the cf model.
   - [ARX_cf] := IOK inst /\ ARcf, the WALK's relation.  The Deallocate interfaces (DIface) are stated at it.  It
     carries NO conjunct that a reachable post can break: not qtight (Deallocate's post-Enqueue / pre-Drain state is
     over kQuarantineCacheMax, DGif0.v:319-333, DMspec.v:92-93), and not the three ROOM_cf conjuncts (each is spent
     by some call: one more live secondary, the errbuf map, a batch-class map, YG03cf.v:439-445).  mroom_cf and the
     free-array headroom are not conjuncts either: both follow from ARcf's Wf_cf and qloose
     (YG08cf.mroom_cf_of_live; abudget_room_cf).
   - [ARXq_cf] := ARX_cf /\ qtight, the CALL-SITE relation.  The Allocate interfaces (AIface / AIfaceK / AIfaceM /
     AIfaceS / AIfaceSE) are stated at it, because a malloc does not drain, so the leaf's lpost := qtight needs qtight
     at the pre-state, and rpre_cfr carries none (YGcfRmodel.v:66-67).  The free contract is lifted to it at the call
     site (pre: drop qtight; post: qtight is the leaf's lpost).

   ROOM_cf is the CALLER's obligation, as it already is in the proved compose (rpre := rpre_cfr = universe_ok /\ Wf_cf
   /\ ROOM_cf, YGcfRmodel.v:66-67; YGcfMallocComposeE.v:96; acall_pre_cf, YG0dcf.v:227-247): YGcfRoomPre.v:7-11 says its
   three conjuncts "come from the PROGRAM, through the input, and no allocator invariant bounds them".  Against what
   ARX_cf gives (Wf_cf), each has only a non-strict form, and the residue is what a caller supplies at every call:
     sec_arr < cf_sec_live_max    vs wfc_sec_live  (<=, YG01cf.v)    residue: room for ONE more live secondary;
     ERRB_ROOM                     vs wsc_lens      (<= cf_nob)       residue: 2 ^ 12 + kPage of errbuf headroom;
     batch_room_cf                 vs wrc_mapped_bound (<= kFreeArrayOffset)  residue: one kUserMapSize of batch maps.

   The instance object enters as the parameter [IOK]: preset takes [IOK := fun i => i = as_inst B]; a unit whose
   const cells are instance-relative (reply) takes its own, and no file of the layer names an instance address.
   Image-free: image constants come from CfImg (YGcfNames.v), the segment list is ImgBase's [im_segs], and the unit's
   own walk enters through the WalkSig records.  The meter is not a parameter here and never forces success.

   EVENT-FREE: no st_nev, EV_A, EV_MAX, EV_BIG, mtr_ok, aregime or the non-cf abudget appears in this file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK0j YK15 YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08cf YGcfNilInit YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomStep YGcfXsMapped ReallocP.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Section b.
Variable B : asyms.
(* the unit's instance object, as a predicate on the walk's [inst]: preset takes (fun i => i = as_inst B) *)
Variable IOK : Z -> Prop.

(* ================================================================================================================ *)
(* 1. The walk's relation.  Its third conjunct, xs_mapped_cf (YGcfXs.v:196: the errbuf extent is one of the
   model's maps), is what a secondary grant needs to keep ARmcf's amc_xs_placed: the new extent is disjoint from the
   errbuf only if the errbuf is mapped (YGcfXs.xs_fresh_of_grant, YGcfXs.v:227).  Without it AIfaceS.ifs_post_grant
   is false: errbuf unmapped in md0, the grant overlapping it, every premise true and the post false.  Preset's
   ARXs_A carries the same conjunct (a Theorem Labs lane F2, lib/A/AIfaceSA.v at ccb2bc98b40).  It holds at every reachable
   state: none at the start (no errbuf), free never creates or resizes the errbuf, and malloc's class-full path maps
   the capacity entry xs_cf names; YGcfXsMapped.v's keep lemmas re-establish it at each post. *)
(* The two machine cells (the per-class exhausted byte and the error-message buffer's object: exh_cell_cf,
   errb_cells_cf, errb_data_cf) and the image row errb_obj_owned_t are YG0ncf.v's (field round 2, Main 2026-10-30):
   the cells are ARmcf's fields amc_exh_cell / amc_errb_cells, so ARX_cf no longer states them.  errb_cells_cf's last
   two conjuncts (ErrbCap's size <= cap and cap a whole number of pages) hold at init (errb_szcap_init) and every
   model step keeps them (errb_size_le_cap_keep, section 1b). *)
Definition ARX_cf : ARXh_t im_segs :=
fun (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (mem : word -> option byte) (md : Model) =>
  IOK inst /\ YG0ncf.ARcf im_segs B ly S Hp W mem md /\ xs_mapped_cf ly S md.

(* The projections.  Ask for one rather than unfolding ARX_cf: the conjunct list is the layer's to change. *)
Lemma ARX_cf_iok : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md -> IOK inst.
Proof. intros Hp inst ly S W mem md H. exact (proj1 H). Qed.

Lemma ARX_cf_ARcf : ARX_ARcf im_segs B ARX_cf.
Proof. intros Hp inst ly S W mem md H. exact (proj1 (proj2 H)). Qed.

Lemma ARX_cf_xs : ARX_xs im_segs ARX_cf.
Proof.
intros Hp inst ly S W mem md H.
exact (YG0ncf.xs_placed_of_ARcf im_segs B ly S Hp W mem md (ARX_cf_ARcf Hp inst ly S W mem md H)).
Qed.

Lemma ARX_cf_wf : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md -> Wf_cf (as_universe B) S.
Proof.
intros Hp inst ly S W mem md H. destruct (ARX_cf_ARcf Hp inst ly S W mem md H) as (M & _).
exact (amc_wf _ _ _ _ _ M).
Qed.

(* The room the quarantine does not touch, wherever the quarantine is loose. *)
Lemma ARX_cf_mroom : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md -> qloose S -> cf_hull_ok S -> mroom_cf S.
Proof.
intros Hp inst ly S W mem md H QL.
exact (mroom_cf_of_live (as_universe B) 0 0 0 S (ARX_cf_wf Hp inst ly S W mem md H) QL).
Qed.

Lemma ARX_cf_xsm : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md -> xs_mapped_cf ly S md.
Proof. intros Hp inst ly S W mem md H. exact (proj2 (proj2 H)). Qed.

Lemma ARX_cf_exh : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md ->
  exh_cell_cf B ly S (aview im_segs (w_H W) mem).
Proof. intros Hp inst ly S W mem md H. exact (ARcf_exh_cell im_segs B ly S Hp W mem md (ARX_cf_ARcf Hp inst ly S W mem md H)). Qed.

Lemma ARX_cf_errb : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md ->
  errb_cells_cf B ly S (aview im_segs (w_H W) mem).
Proof. intros Hp inst ly S W mem md H. exact (ARcf_errb_cells im_segs B ly S Hp W mem md (ARX_cf_ARcf Hp inst ly S W mem md H)). Qed.

(* The layout facts the SYM cells of Tfib_const read (Main, 2026-10-30; oom_const_t and CONST_APART were refuted at
   reply's image A for want of them: ReplyImg_oomconst.v @ 0e400063292, ReplyImg_constapart.v @ 507bcceac8e).
   MEASURED over Tfib_const_sym (YF0m.v:20-26): its cells sit at AT 0..72, AC 8 / 152, ATsd 0, AD 24, ATp and AInst.
   ATp / AInst are fixed by B.  AT / AC / AD are inside the owned extents (ly_T, kThreadObjSize = 4096),
   (ly_C, 256), (ly_D, 4096) (the widest reaches +80, +160, +32), which layout_ok's lo_disj keeps pairwise apart from
   the primary reserve and from ly_img (static_extents, YG0f.v:295-300, :322); amc_static_img puts the owned static
   inside ly_img, so no such cell is an owned-static byte.  ATsd is pinned to the image's slot by amc_tsd.  So the
   predicate is exactly ARmcf's amc_layout, amc_tsd and amc_static_img, and no other conjunct. *)
Definition ly_img_ok (ly : alayout) : Prop :=
  layout_ok ly /\ ly_tsd ly = as_tsd B /\
  Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B).

Lemma ly_img_ok_of_ARmcf : forall ly S Hp (rd : reader), ARmcf B ly S Hp rd -> ly_img_ok ly.
Proof.
intros ly S Hp rd M.
exact (conj (amc_layout _ _ _ _ _ M) (conj (amc_tsd _ _ _ _ _ M) (amc_static_img _ _ _ _ _ M))).
Qed.

Lemma ly_img_ok_of_ARX_cf : forall Hp inst ly S W mem md, ARX_cf Hp inst ly S W mem md -> ly_img_ok ly.
Proof.
intros Hp inst ly S W mem md H. destruct (ARX_cf_ARcf Hp inst ly S W mem md H) as (M & _).
exact (ly_img_ok_of_ARmcf ly S Hp _ M).
Qed.

(* The keeps: an allocator step that leaves the exhausted bits, the buffer's model values and the cells' bytes alone
   keeps the two conjuncts (the xs_mapped_cf pattern).  The steps that change them are exactly errb_append_cf /
   errb_map_cf / errb_retire / errb_set_size and set_exh_cf / clear_exh_cf; their walks re-establish the cells. *)
Lemma exh_cell_cf_frame : forall ly ly' S S' (rd rd' : reader),
  exh_cell_cf B ly S rd ->
  (forall c, exh_mem_cf S' c = exh_mem_cf S c) ->
  (forall c, 1 <= c <= 31 ->
     rd' (aeval B ly' (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off)) =
     rd (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off))) ->
  exh_cell_cf B ly' S' rd'.
Proof.
intros ly ly' S S' rd rd' [H1 H2] E F. split.
- intros c Hc. rewrite (E c). specialize (H1 c Hc). unfold cell_holds in *. cbn [c_at c_w c_val z1 c1] in *.
  intros k Hk. destruct k as [|k]; [|exfalso; YM03.lf_lia_orig].
  specialize (H1 0%nat Hk). cbn [Z.of_nat] in *. rewrite Z.add_0_r in *. rewrite (F c Hc). exact H1.
- rewrite (E kBatchClass). exact H2.
Qed.

Lemma errb_cells_cf_frame : forall ly ly' S S' (rd rd' : reader),
  errb_cells_cf B ly S rd ->
  errb_mapped_cf S' = errb_mapped_cf S -> errb_data_cf ly' S' = errb_data_cf ly S ->
  errb_cap_cf S' = errb_cap_cf S -> errb_size_cf S' = errb_size_cf S ->
  (forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> rd' a = rd a) ->
  (forall a, rd a <> None -> rd' a <> None) ->
  errb_cells_cf B ly' S' rd'.
Proof.
intros ly ly' S S' rd rd' (P & M & D & C & SZ & V & LE & MD) EM ED EC EZ F VIS.
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
split; [intros a Ha; exact (VIS a (V a Ha))|]. split; [exact LE | exact MD].
Qed.

(* ================================================================================================================ *)
(* 1b. The buffer's shape, a model invariant: size <= capacity, and the capacity a whole number of pages.  The machine
   reads both cells: with size > cap and len = 0 Append skips the map that the model asks (YG00cf.v:141-142); with
   cap < size + len Realloc copies `size` bytes from a buffer readable only up to cap.  With cap a page multiple, an
   append that remaps (size + len > cap) gets the next page multiple, so the new cap >= old cap + kPage >= old size +
   kPage: the class-full arm's second append (at most 67 bytes after the first's 33) cannot remap again.
   The keep: every capacity entry is round_up _ kPage (errb_map_cf), an append sets the size to a value it has just
   tested against the capacity, and no other step changes the size or the capacity entries.  errb_retire alone
   breaks it (cap 0, size unchanged), but only errb_map_cf calls it, and the shape is kept at errb_map_cf's callers'
   exits.  The list facts reuse YGcfRoomStep's first_sz and YGcfXsMapped's cfxm_capeq; TkSecLink's draft (size <= cap
   only, unpushed) gave the forms of errb_set_size_post / errb_map_post and the `snd` / `filter` workarounds below:
   in this file's imports `filter` is stdpp's (so List.filter) and `cbn` does not reduce `snd (a, b)` (so change). *)
Definition errb_szcap_cf (S : astate) : Prop := errb_size_cf S <= errb_cap_cf S /\ errb_cap_cf S mod kPage = 0.

Ltac ec_red :=
repeat match goal with
| H : context [Datatypes.snd (?a, ?b)] |- _ => change (Datatypes.snd (a, b)) with b in H
| H : context [Datatypes.fst (?a, ?b)] |- _ => change (Datatypes.fst (a, b)) with a in H
| |- context [Datatypes.snd (?a, ?b)] => change (Datatypes.snd (a, b)) with b
| |- context [Datatypes.fst (?a, ?b)] => change (Datatypes.fst (a, b)) with a
end.

Lemma errb_cells_cf_szcap : forall ly S rd, errb_cells_cf B ly S rd -> errb_szcap_cf S.
Proof. intros ly S rd (_ & _ & _ & _ & _ & _ & LE & MD). exact (conj LE MD). Qed.

Lemma errb_szcap_init : errb_szcap_cf init_state.
Proof.
unfold errb_szcap_cf. replace (errb_size_cf init_state) with 0 by reflexivity.
replace (errb_cap_cf init_state) with 0 by reflexivity. split; [YM03.lf_lia_orig | reflexivity].
Qed.

Lemma errb_szcap_secs : forall s s', st_secs s' = st_secs s -> errb_szcap_cf s -> errb_szcap_cf s'.
Proof. intros s s' E H. unfold errb_szcap_cf, errb_size_cf, errb_cap_cf, errb_e in *. rewrite E. exact H. Qed.

Lemma errb_filter_app_noncap : forall l sm, is_errb_cap sm = false ->
  List.filter is_errb_cap (l ++ [sm]) = List.filter is_errb_cap l.
Proof.
intros l sm Hc. rewrite List.filter_app.
replace (List.filter is_errb_cap [sm]) with (@nil secmap) by (cbn [List.filter]; rewrite Hc; reflexivity).
apply app_nil_r.
Qed.

(* A secondary's entry (sec_alloc) is neither a capacity nor a size entry: needed_size n > 0. *)
Lemma errb_szcap_app : forall s s' sm, errb_szcap_cf s -> st_secs s' = st_secs s ++ [sm] ->
  is_errb_cap sm = false -> is_errb_sz sm = false -> errb_szcap_cf s'.
Proof.
intros s s' sm H E Hc Hs.
assert (EZ : errb_size_cf s' = errb_size_cf s).
{ rewrite !YGcfRoomStep.errb_size_first, E. exact (YGcfRoomStep.first_sz_app_nsz _ _ Hs). }
assert (EC : errb_cap_cf s' = errb_cap_cf s).
{ unfold errb_cap_cf, errb_e. rewrite E, (errb_filter_app_noncap _ _ Hc). reflexivity. }
unfold errb_szcap_cf. rewrite EZ, EC. exact H.
Qed.

Lemma errb_sec_entry_nonsz : forall m n b, is_errb_sz (mkSec m (needed_size n) b) = false.
Proof.
intros m n b. unfold is_errb_sz. change (sm_size (mkSec m (needed_size n) b)) with (needed_size n).
apply Z.eqb_neq. pose proof (YGcfXsMapped.cfxm_needed_size_pos n). unfold ERRB_SZ_TAG. YM03.lf_lia_orig.
Qed.

(* The free path's frame (YGcfXs.cfx_fr): pointwise the same sm_len and sm_size, so the same size and capacity. *)
Lemma errb_first_sz_f2 : forall l l', Forall2 cfx_same_sm l l' -> YGcfRoomStep.first_sz l' = YGcfRoomStep.first_sz l.
Proof.
intros l l' H. induction H as [|x x' t t' [El Es] Ht IH]; [reflexivity|].
change (YGcfRoomStep.first_sz (x' :: t')) with (if is_errb_sz x' then sm_len x' else YGcfRoomStep.first_sz t').
change (YGcfRoomStep.first_sz (x :: t)) with (if is_errb_sz x then sm_len x else YGcfRoomStep.first_sz t).
unfold is_errb_sz. rewrite Es, El, IH. reflexivity.
Qed.

Lemma errb_szcap_f2 : forall s s', Forall2 cfx_same_sm (st_secs s) (st_secs s') -> errb_szcap_cf s -> errb_szcap_cf s'.
Proof.
intros s s' HS H.
assert (EZ : errb_size_cf s' = errb_size_cf s) by (rewrite !YGcfRoomStep.errb_size_first; exact (errb_first_sz_f2 _ _ HS)).
assert (EC : errb_cap_cf s' = errb_cap_cf s).
{ unfold errb_cap_cf, errb_e. rewrite (cfx_last_len_f2 _ _ (mkSec 0 ERRB_CAP_TAG false) (cfx_filter_f2 _ _ HS)).
  reflexivity. }
unfold errb_szcap_cf. rewrite EZ, EC. exact H.
Qed.

Lemma errb_cap_round_mod : forall x, Z.max 0 (round_up x kPage) mod kPage = 0.
Proof.
intros x. destruct (Z.max_spec 0 (round_up x kPage)) as [[_ E] | [_ E]]; rewrite E; [|reflexivity].
exact (proj2 (round_up_ge x kPage ltac:(unfold kPage; YM03.lf_lia_orig))).
Qed.

(* The buffer steps, exactly. *)
Lemma errb_set_size_post : forall ns s, cfx_ipost (errb_set_size ns s)
  (fun r => errb_size_cf (Datatypes.snd r) = ns /\ errb_cap_cf (Datatypes.snd r) = errb_cap_cf s).
Proof.
intros ns s. unfold errb_set_size, YG00.modify. cbv beta iota delta [cfx_ipost]. ec_red.
split; [apply YGcfRoomStep.errb_size_set|].
unfold errb_cap_cf, errb_e. destruct (find_sz (st_secs s) 0) as [i|] eqn:E.
- change (st_secs (set_secs (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)) s))
    with (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)).
  assert (F : Forall2 YGcfXsMapped.cfxm_capeq (st_secs s) (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false))).
  { apply YGcfXsMapped.cfxm_capeq_lupd; [reflexivity|]. intros sm Hsm.
    destruct (YGcfXsMapped.cfxm_find_sz _ _ _ E) as [_ (sm' & Hn & Hs)]. rewrite Nat.sub_0_r in Hn.
    rewrite Hn in Hsm. injection Hsm as <-. unfold is_errb_sz in Hs. unfold is_errb_cap.
    apply Z.eqb_eq in Hs. rewrite Hs. reflexivity. }
  rewrite (YGcfXsMapped.cfxm_capeq_filter _ _ F). reflexivity.
- change (st_secs (set_secs (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]) s)) with (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]).
  rewrite errb_filter_app_noncap by reflexivity. reflexivity.
Qed.

(* A remap re-tags every capacity entry dead and appends the new one: the size entry is untouched. *)
Lemma errb_remap_post : forall s s' ncap, st_secs s' = List.map cfx_retire (st_secs s) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  errb_size_cf s' = errb_size_cf s /\ errb_cap_cf s' = Z.max 0 ncap.
Proof.
intros s s' ncap E. split.
- rewrite !YGcfRoomStep.errb_size_first, E.
  transitivity (YGcfRoomStep.first_sz (List.map cfx_retire (st_secs s))).
  + apply YGcfRoomStep.first_sz_app_nsz. reflexivity.
  + apply YGcfRoomStep.first_sz_retire.
- unfold errb_cap_cf, errb_e. rewrite E, List.filter_app, cfx_filter_retired. reflexivity.
Qed.

Lemma errb_map_post : forall want s, cfx_ipost (errb_map_cf want s)
  (fun r => errb_size_cf (Datatypes.snd r) = errb_size_cf s /\
            errb_cap_cf (Datatypes.snd r) = Z.max 0 (round_up want kPage)).
Proof.
intros want s. unfold errb_map_cf, errb_retire, YG00.tick, YG00.modify, YG00.askz, YG00.bind, YG00.spin.
cbv beta iota zeta delta [ibind cfx_ipost]. intros z. destruct (z =? 0); cbv beta iota zeta delta [ibind cfx_ipost];
[exact I|]. apply errb_remap_post. reflexivity.
Qed.

(* An append ends with size <= cap from ANY start state; the page conjunct needs the start's. *)
Lemma errb_szcap_append : forall len s, errb_cap_cf s mod kPage = 0 ->
  cfx_ipost (errb_append_cf len s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof.
intros len s Hm. pose proof (fun x => proj1 (proj1 (round_up_ge x kPage ltac:(unfold kPage; YM03.lf_lia_orig)))) as RU.
unfold errb_append_cf, YG00.get, YG00.bind. cbv beta iota zeta delta [ibind].
destruct (negb (errb_mapped_cf s)).
- apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (errb_map_post ERRB_INIT s)].
  intros [u1 s1] [_ C1]. ec_red. cbv beta iota zeta delta [ibind].
  apply cfx_ipost_ibind.
  destruct (errb_cap_cf s1 <? len) eqn:LT.
  + eapply cfx_ipost_mono; [|exact (errb_map_post len s1)].
    intros [u2 s2] [_ C2]. ec_red. cbv beta iota zeta.
    eapply cfx_ipost_mono; [|exact (errb_set_size_post len s2)].
    intros [u3 s3] [S3 C3]. ec_red. unfold errb_szcap_cf. rewrite S3, C3, C2.
    split; [specialize (RU len); YM03.lf_lia_orig | apply errb_cap_round_mod].
  + unfold YG00.ret. cbv beta iota zeta delta [cfx_ipost].
    eapply cfx_ipost_mono; [|exact (errb_set_size_post len s1)].
    intros [u3 s3] [S3 C3]. ec_red. unfold errb_szcap_cf. rewrite S3, C3. apply Z.ltb_ge in LT.
    split; [exact LT | rewrite C1; apply errb_cap_round_mod].
- apply cfx_ipost_ibind.
  destruct (errb_cap_cf s <? errb_size_cf s + len) eqn:LT.
  + eapply cfx_ipost_mono; [|exact (errb_map_post (errb_size_cf s + len) s)].
    intros [u2 s2] [_ C2]. ec_red. cbv beta iota zeta.
    eapply cfx_ipost_mono; [|exact (errb_set_size_post (errb_size_cf s + len) s2)].
    intros [u3 s3] [S3 C3]. ec_red. unfold errb_szcap_cf. rewrite S3, C3, C2.
    split; [specialize (RU (errb_size_cf s + len)); YM03.lf_lia_orig | apply errb_cap_round_mod].
  + unfold YG00.ret. cbv beta iota zeta delta [cfx_ipost].
    eapply cfx_ipost_mono; [|exact (errb_set_size_post (errb_size_cf s + len) s)].
    intros [u3 s3] [S3 C3]. ec_red. unfold errb_szcap_cf. rewrite S3, C3. apply Z.ltb_ge in LT.
    split; [exact LT | exact Hm].
Qed.

(* The walk over every other allocator step: a step that leaves st_secs alone keeps the shape (errb_szcap_secs);
   sec_alloc appends a secondary's entry (errb_szcap_app); the buffer steps by the lemmas above. *)
Create HintDb ecdb.

Ltac ec_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed, YG00.tick,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin,
set_exh_cf, clear_exh_cf in *).

Ltac ec_cbn := cbn [ibind cfx_ipost] in *.

Ltac ec_close :=
match goal with H : errb_szcap_cf ?a |- errb_szcap_cf ?c =>
  first [ exact (errb_szcap_secs a c eq_refl H)
        | (eapply (errb_szcap_app a c); [exact H | reflexivity | apply YGcfXsMapped.sec_entry_noncap
                                        | apply errb_sec_entry_nonsz]) ]
end.

#[local] Hint Extern 1 (errb_szcap_cf _) => ec_close : ecdb.

Ltac ec_hint :=
match goal with
| |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind;
  eapply cfx_ipost_mono with (P := fun r => errb_szcap_cf (Datatypes.snd r)); [| solve [eauto with ecdb]];
  let x := fresh "x" in let sx := fresh "sx" in let Hx := fresh "Hx" in
  intros [x sx] Hx; cbv beta in Hx; change (Datatypes.snd (x, sx)) with sx in Hx
| |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono with (P := fun r => errb_szcap_cf (Datatypes.snd r)); [| solve [eauto with ecdb]];
  let x := fresh "x" in let sx := fresh "sx" in let Hx := fresh "Hx" in
  intros [x sx] Hx; cbv beta in Hx; change (Datatypes.snd (x, sx)) with sx in Hx
end.

Ltac ec_step :=
first
[ progress ec_cbn
| progress ec_red
| ec_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| ec_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| ec_close ].

Lemma ec_of_same {A : Type} : forall (t : itree astate (A * astate)) s, errb_szcap_cf s ->
  cfx_ipost t (fun r => cfx_same s (Datatypes.snd r)) -> cfx_ipost t (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof.
intros t s H1 H2. eapply cfx_ipost_mono; [|exact H2]. intros [x sx] [E1 _].
exact (errb_szcap_secs s sx E1 H1).
Qed.

Lemma ec_ensure : forall c need sof s, errb_szcap_cf s ->
  cfx_ipost (ensure_free_array c need sof s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c need sof s H. exact (ec_of_same _ s H (cfx_same_ensure c need sof s)). Qed.
#[local] Hint Resolve ec_ensure : ecdb.

Lemma ec_mmu : forall c need s, errb_szcap_cf s ->
  cfx_ipost (map_more_user c need s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c need s H. exact (ec_of_same _ s H (cfx_same_mmu c need s)). Qed.
#[local] Hint Resolve ec_mmu : ecdb.

Lemma ec_populate : forall c need s, errb_szcap_cf s ->
  cfx_ipost (populate c need s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c need s H. exact (ec_of_same _ s H (cfx_same_populate c need s)). Qed.
#[local] Hint Resolve ec_populate : ecdb.

Lemma ec_depot_put : forall tr s, errb_szcap_cf s ->
  cfx_ipost (depot_put tr s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros tr s H. exact (ec_of_same _ s H (cfx_same_depot_put tr s)). Qed.
#[local] Hint Resolve ec_depot_put : ecdb.

Lemma ec_errb_append : forall len s, errb_szcap_cf s ->
  cfx_ipost (errb_append_cf len s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros len s H. exact (errb_szcap_append len s (proj2 H)). Qed.
#[local] Hint Resolve ec_errb_append : ecdb.

Lemma ec_errb_report : forall c s, errb_szcap_cf s ->
  cfx_ipost (errb_report_cf c s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c s H. unfold errb_report_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_errb_report : ecdb.

Lemma ec_mmu_cf : forall c need s, errb_szcap_cf s ->
  cfx_ipost (map_more_user_cf c need s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c need s H. unfold map_more_user_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_mmu_cf : ecdb.

Lemma ec_populate_cf : forall c need s, errb_szcap_cf s ->
  cfx_ipost (populate_cf c need s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c need s H. unfold populate_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_populate_cf : ecdb.

Lemma ec_gfa_cf : forall c n s, errb_szcap_cf s ->
  cfx_ipost (get_from_allocator_cf c n s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c n s H. unfold get_from_allocator_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_gfa_cf : ecdb.

Lemma ec_refill_cf : forall c s, errb_szcap_cf s ->
  cfx_ipost (refill_if_empty_cf c s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c s H. unfold refill_if_empty_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_refill_cf : ecdb.

Lemma ec_cache_alloc_cf : forall c s, errb_szcap_cf s ->
  cfx_ipost (cache_alloc_cf c s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros c s H. unfold cache_alloc_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_cache_alloc_cf : ecdb.

Lemma ec_sec_alloc : forall n s, errb_szcap_cf s ->
  cfx_ipost (sec_alloc n s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros n s H. unfold sec_alloc. repeat ec_step. Qed.
#[local] Hint Resolve ec_sec_alloc : ecdb.

Lemma ec_malloc_cf : forall n tr s, errb_szcap_cf s ->
  cfx_ipost (malloc_cf n tr s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof. intros n tr s H. unfold malloc_cf. repeat ec_step. Qed.
#[local] Hint Resolve ec_malloc_cf : ecdb.

Lemma ec_free_cf : forall p tr s, errb_szcap_cf s ->
  cfx_ipost (free_cf p tr s) (fun r => errb_szcap_cf (Datatypes.snd r)).
Proof.
intros p tr s H. eapply cfx_ipost_mono; [|exact (cfx_fr_free_cf p tr s)]. intros [x sx] [HS _].
exact (errb_szcap_f2 s sx HS H).
Qed.
#[local] Hint Resolve ec_free_cf : ecdb.

(* THE KEEP: on every returning path of every allocator step of the cf model, from a state of the right shape
   (YGcfXs.cfx_ipost_apath turns each into a fact about a path). *)
Theorem errb_size_le_cap_keep : forall S, errb_szcap_cf S ->
  (forall len, cfx_ipost (errb_append_cf len S) (fun r => errb_szcap_cf (Datatypes.snd r))) /\
  (forall c, cfx_ipost (errb_report_cf c S) (fun r => errb_szcap_cf (Datatypes.snd r))) /\
  (forall n tr, cfx_ipost (malloc_cf n tr S) (fun r => errb_szcap_cf (Datatypes.snd r))) /\
  (forall p tr, cfx_ipost (free_cf p tr S) (fun r => errb_szcap_cf (Datatypes.snd r))) /\
  (forall p n tr, cfx_ipost (ReallocP.realloc_tree_with malloc_cf free_cf p n tr S)
     (fun r => errb_szcap_cf (Datatypes.snd r))) /\
  (forall n tr, cfx_ipost (ReallocP.realloc_null_tree_with malloc_cf free_cf n tr S)
     (fun r => errb_szcap_cf (Datatypes.snd r))).
Proof.
intros S H.
split; [intros len; exact (ec_errb_append len S H)|]. split; [intros c; exact (ec_errb_report c S H)|].
split; [intros n tr; exact (ec_malloc_cf n tr S H)|]. split; [intros p tr; exact (ec_free_cf p tr S H)|].
split; [intros p n tr; unfold ReallocP.realloc_tree_with; repeat ec_step|].
intros n tr. unfold ReallocP.realloc_null_tree_with. repeat ec_step.
Qed.

(* ================================================================================================================ *)
(* 2. The call-site relation.                                                                                       *)
Definition ARXq_cf : ARXh_t im_segs :=
fun (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (mem : word -> option byte) (md : Model) =>
  ARX_cf Hp inst ly S W mem md /\ qtight S.

Lemma ARXq_cf_intro : forall Hp inst ly S W mem md,
  ARX_cf Hp inst ly S W mem md -> qtight S -> ARXq_cf Hp inst ly S W mem md.
Proof. intros Hp inst ly S W mem md H Q. exact (conj H Q). Qed.

Lemma ARXq_cf_ARX : forall Hp inst ly S W mem md, ARXq_cf Hp inst ly S W mem md -> ARX_cf Hp inst ly S W mem md.
Proof. intros Hp inst ly S W mem md H. exact (proj1 H). Qed.

Lemma ARXq_cf_qtight : forall Hp inst ly S W mem md, ARXq_cf Hp inst ly S W mem md -> qtight S.
Proof. intros Hp inst ly S W mem md H. exact (proj2 H). Qed.

Lemma ARXq_cf_iok : forall Hp inst ly S W mem md, ARXq_cf Hp inst ly S W mem md -> IOK inst.
Proof. intros Hp inst ly S W mem md H. exact (ARX_cf_iok Hp inst ly S W mem md (proj1 H)). Qed.

Lemma ARXq_cf_ARcf : ARX_ARcf im_segs B ARXq_cf.
Proof. intros Hp inst ly S W mem md H. exact (ARX_cf_ARcf Hp inst ly S W mem md (proj1 H)). Qed.

Lemma ARXq_cf_xs : ARX_xs im_segs ARXq_cf.
Proof. intros Hp inst ly S W mem md H. exact (ARX_cf_xs Hp inst ly S W mem md (proj1 H)). Qed.

Lemma ARXq_cf_xsm : forall Hp inst ly S W mem md, ARXq_cf Hp inst ly S W mem md -> xs_mapped_cf ly S md.
Proof. intros Hp inst ly S W mem md H. exact (ARX_cf_xsm Hp inst ly S W mem md (proj1 H)). Qed.

(* qmeter_cf = qtight /\ mroom_cf: qtight from the relation, mroom_cf from Wf_cf and qtight's qloose. *)
(* The unit's hull premise cf_hull_ok S is the driver's per-call admission (the run meter at the state). *)
Lemma ARXq_cf_qm : forall Hp inst ly S W mem md, ARXq_cf Hp inst ly S W mem md -> cf_hull_ok S -> qmeter_cf S.
Proof.
intros Hp inst ly S W mem md H HO.
pose proof (ARXq_cf_qtight Hp inst ly S W mem md H) as Q.
exact (conj Q (ARX_cf_mroom Hp inst ly S W mem md (proj1 H) (qtight_qloose S Q) HO)).
Qed.

(* ================================================================================================================ *)
(* 3. Satisfiability at a start state.                                                                              *)
(* Generic: wherever ARcf holds, the errbuf (if any) is mapped and the instance object is the unit's, both relations
   hold (the call-site one with qtight).  A unit instantiates it at its own start state (preset below; reply's at
   A/AD26.v:215 is lane W's). *)
Lemma ARX_cf_start : forall Hp inst ly S W mem md,
  IOK inst -> YG0ncf.ARcf im_segs B ly S Hp W mem md -> xs_mapped_cf ly S md ->
  ARX_cf Hp inst ly S W mem md.
Proof. intros Hp inst ly S W mem md I A X. exact (conj I (conj A X)). Qed.

Lemma ARXq_cf_start : forall Hp inst ly S W mem md,
  IOK inst -> YG0ncf.ARcf im_segs B ly S Hp W mem md -> xs_mapped_cf ly S md -> qtight S ->
  ARXq_cf Hp inst ly S W mem md.
Proof. intros Hp inst ly S W mem md I A X Q. exact (conj (conj I (conj A X)) Q). Qed.

(* At the start state there is no errbuf: xs_cf is empty, so it is mapped vacuously. *)
Lemma xs_mapped_cf_init : forall ly md, xs_mapped_cf ly init_state md.
Proof. intros ly md e He. unfold xs_cf in He. cbn in He. destruct He. Qed.

(* At the start state no class is exhausted and the buffer is unmapped and empty, so the two cells say only that
   the cells are zero: a START-UP fact of each unit (the start-up row behind start_cells_cf, YG0ncf.v). *)
Lemma exh_cell_cf_init : forall ly rd,
  (forall c, 1 <= c <= 31 -> cell_holds B ly rd (z1 (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) 0)) ->
  exh_cell_cf B ly init_state rd.
Proof.
intros ly rd H.
assert (E : forall c, exh_mem_cf init_state c = false).
{ intros c. unfold exh_mem_cf. replace (reg init_state c) with region0; [reflexivity|].
  unfold reg, znth. cbn [st_regions init_state]. symmetry. apply nth_repeat. }
split.
- intros c Hc. rewrite (E c). exact (H c Hc).
- exact (E kBatchClass).
Qed.

Lemma errb_cells_cf_init : forall ly rd,
  cell_holds B ly rd (z8 (ANum cf_errbuf_obj) 0) -> cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 16)) 0) ->
  cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 32)) 0) -> cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 40)) 0) ->
  cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 48)) 0) ->
  errb_cells_cf B ly init_state rd.
Proof.
intros ly rd P M D C SZ. unfold errb_cells_cf, errb_data_cf, errb_mapped_cf, errb_cap_cf, errb_size_cf, errb_e.
cbn. split; [exact P|]. split; [exact M|]. split; [exact D|]. split; [exact C|]. split; [exact SZ|].
split; [intros a Ha; exfalso; YM03.lf_lia_orig | exact errb_szcap_init].
Qed.

(* Preset's start state: the conversion at init (YGcfNilInit.ARcf_nil_init) gives ARcf at the empty ghost set, and
   init_state is tight and has no secondary at all. The other premises are the conversion's: the start witnesses
   of the two cells (start_cells_cf) and of Printf's two image cells (start_pf_cf, field round 3), ALedger_cf's
   alc_lazy_in_maps at md (from the process's first model, YGcfLazyMaps.lazy_in_maps_init_cf, and its keep lemmas
   over start-up's maps) and the unit's image rows. *)
Lemma ARXq_cf_nil_init : forall inst ly (W : world im_segs) mem md,
  IOK inst -> AR im_segs B ly init_state W mem md -> AI im_segs (w_H W) (w_A W) md ->
  start_cells_cf im_segs B ly init_state W mem -> start_pf_cf im_segs B ly W mem ->
  (forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
     YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
  EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
  exists W', wle W W' /\ AI im_segs (w_H W') (w_A W') md /\ ARXq_cf [] inst ly init_state W' mem md.
Proof.
intros inst ly W mem md I A HAI CELLS PFC LM HO HPO.
destruct (ARcf_nil_init im_segs B ly W mem md A HAI LM CELLS PFC HO HPO) as (W' & L & HAI' & HC).
exists W'. split; [exact L|]. split; [exact HAI'|].
exact (ARXq_cf_start [] inst ly init_state W' mem md I HC (xs_mapped_cf_init ly md) qtight_init).
Qed.

(* ================================================================================================================ *)
(* 4. The unit's choices, named.                                                                                     *)
(* The trace premise: ONE definition.  It is the P'' form, `admits (as_universe B) tr S` (YG01.v: a fixed trace, a
   trace already in the depot, or a wild trace with room in the depot), as the kit's realizes_cf statements state it
   (YG0dcf.v); [cf_tr_ok] is the frame-generic U of AllocG / MemnormT, [cf_trace_ok] the call-trace form.  Every lane
   text states the trace premise through these two names, never inline. *)
Definition cf_tr_ok (tr : list Z) (S : astate) : Prop := admits (as_universe B) tr S.
Definition cf_trace_ok (ly : alayout) (pc0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) (S : astate) : Prop :=
  cf_tr_ok (call_trace ly pc0 regs ch) S.

(* The instance object a unit may pass as IOK: the binary's own allocator object.  The Deallocate drain views
   (di_rview_cf / di_requar_*_cf, lanes F2a / F2b) read the instance's cells through `inst = as_inst B`, so a weaker
   IOK makes them unprovable.  Every unit instance supplies IOK_ok (preset: IOK := fun i => i = as_inst B, by
   reflexivity; reply: its instance object, the same equation). *)
Definition IOK_ok : Prop := forall i, IOK i -> i = as_inst B.

(* ================================================================================================================ *)
(* 5. The fixed arguments of the cf instance, in the form YGcfMallocComposeE.v:93-109 states its Props.              *)
Definition U_cf : list Z -> astate -> Prop := cf_tr_ok.
Definition AOX_cf : alayout -> astate -> Z -> Prop := AOXm_cf B.
Definition rpre_cf : astate -> Z -> Prop := YGcfRmodel.rpre_cfr B.
Definition lpost_cf : astate -> Prop := qtight.
Definition oomb_cf : Z := as_oom_byte B.
Definition al_cf : Z := 8.
Definition atp_cf : Z := 1.

End b.
End a.
