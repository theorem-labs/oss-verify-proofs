(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-depkeep-B of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for the cf layer at
   plugin-hostd/fuzz_reply). The B twin of a Theorem Labs lane's lib/A/ReplyImg_depkeep.v (a working branch
   7c7e587ea49), mirrored line for line: same helper names, same Section c form, same premises.
   rule 24: no function proved (kind: image row; the constant cells and the depot's cells against the kept zones, at
   reply's image B, fuzz_reply.asan-ubsan).

   The row is the cf layer's image premise dep_keep_img B KEEP (lane F1, YGcfInstDepot.v:154 at a working branch
   a8ad57cefdc; the table text is CF-UNIT-HYPS-F1.md (sha256 d0647c7f8142; internal record) row 7), at its two zone pairs:
   - Allocate:   KEEP := fun ly a => ag_dzone ly a \/ ag_czone ly a                    ([dep_keep_a_B]);
   - Deallocate: KEEP := fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)   ([dep_keep_d_B]).
   cgif's discharge is YGcfInstF1Wcgif.v:96 dep_keep_a_cgif / :109 dep_keep_d_cgif.  Reply does not carry the layer's
   YGcfInstDepot.v yet, so each theorem states dep_keep_img's body, KEEP applied, at reply B's instances (ImgBase.AImg at
   AImg_reply, B/AGif2reply.v:24; ImgBaseAG.AGImg at AGImg_reply, B/AGif0reply.v:117; ImgBaseDG.DImg at DImg_reply,
   B/DGif0reply.v:31), and a consumer closes the layer's row by `exact` once the layer is on reply.
   ONE PREMISE DIFFERS from the layer head: dep_keep_img's depot premise is `depot_fits (as_universe B) (st_depot S)`
   (YG01.v:260, the P'' depot model).  Reply's model has no depot_fits, so the premise here is the row-7 text,
   `NoDup (st_depot S) -> incl (st_depot S) (as_universe B)`, the form reply B's YFix.depot_ids_bound (B/YFix.v:356)
   reads.  When reply takes P'', the only line that changes is the depot_ids bound ([depot_ids_bound] below).

   The proofs are cgif's AGix Section c (const_cells_zone, CZONE_range, DZONE_range, cell_holds_agree, aview_agree,
   depot_ids_bound, depot_mem_ok_agree; cgif lib/AGix.v:53-141 at a8ad57cefdc; const_kept's loop is inline in the two
   theorems, as in dep_keep_d_cgif) and CLdepotcgif.const_noizone with its helpers (cgif lib/CLdepotcgif.v:43-112 at
   a8ad57cefdc), re-run at reply's image B: reply has no AGix.v and no CLdepotcgif.v.  Each table check is
   a vm_compute on reply B's own constant tables (Tfib_const_abs / Tfib_const_shadow / Tfib_const, B/YF0m.v); reply B's
   constant-cell zone CZONE is AGif0reply.CZONE (B/AGif0reply.v:64, image to 0x5fc000 and high shadow cells up to
   0x800b7800); the depot zone is AGis.DZONE (B/AGis.v:231) = DGgi.DZONE (B/DGgi.v:515); the internal allocator's zone
   is DGgi.IZONE (B/DGgi.v:517), at TFIB_IAL_LO / TFIB_IAL_HI / TFIB_IAL_FLAG = 0xa7840 / 0x128870 / 0x1360c8
   (B/YF0m.v:18-19). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply AGif0reply DGif0reply.
(* Used qualified: their names (DZONE, IZONE, the class fields) would clash with each other. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGis DGgi CLdepot ImgBaseAG ImgBaseDG.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H;
  pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END,
  kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The table checks (by vm_compute on reply's tables).                                                              *)

(* AGix.abs_cell_ok at reply B's CZONE bounds: an image-absolute cell lies in [0x10000, 0x5fc000) or in the high
   shadow window [0x7fff8000, 0x800b7800) (B/AGif0reply.v:64; the same bounds as B/YFix.v's abs_cell_ok). *)
Definition abs_cell_ok (c : acell) : bool :=
match c_at c with
| ANum a => (0x10000 <=? a) && ((a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x5fc000) ||
            ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x800b7800)))
| _ => false
end.
Lemma abs_cells_ok : forallb abs_cell_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

(* CLdepotcgif.noial / const_noial: a cell's bytes miss [TFIB_IAL_LO, TFIB_IAL_HI) and [TFIB_IAL_FLAG, + 4); the
   thread, context and D objects are checked by offset and placed off the image by the layout ([zoneTCD]). *)
Definition noial (a w : Z) : bool :=
(a + w <=? TFIB_IAL_LO) || ((TFIB_IAL_HI <=? a) && (a + w <=? TFIB_IAL_FLAG)) || (TFIB_IAL_FLAG + 4 <=? a).
Definition const_noial (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => noial a w
| ATsd k => noial (TFIB_TSD + k) w
| ATp k => noial (TFIB_TP + k) w
| AInst k => noial (TFIB_INST + k) w
| AT k => (0 <=? k) && (k + w <=? 80)
| AC k => (0 <=? k) && (k + w <=? 256)
| AD k => (0 <=? k) && (k + w <=? 4096)
| _ => false
end.
Lemma Tfib_const_noial : forall ly, forallb const_noial (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma noial_ok : forall a w i, noial a w = true -> 0 <= i < w ->
~ (TFIB_IAL_LO <= a + i < TFIB_IAL_HI \/ TFIB_IAL_FLAG <= a + i < TFIB_IAL_FLAG + 4).
Proof.
intros a w i K Hi. unfold noial in K.
apply Bool.orb_true_iff in K. destruct K as [K|K].
- apply Bool.orb_true_iff in K. destruct K as [K|K].
  + apply Z.leb_le in K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
  + apply Bool.andb_true_iff in K. destruct K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
- apply Z.leb_le in K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
Qed.
(* The thread object, the context object and the D page are off the image (CLdepotcgif.zoneTCD). *)
Lemma zoneTCD : forall ly, layout_ok ly -> img_cover ly ->
zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
intros ly LY IMG.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (AGis.Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (AGis.Forall_nth' _ _ 6 _ HA eq_refl) as IC.
pose proof (AGis.Forall_nth' _ _ 7 _ HA eq_refl) as ID.
cbn beta in IT, IC, ID. cbn [fst snd] in IT, IC, ID.
split; [exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT
  (AGis.pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl))|].
split; [exact (zone3_intro ly (ly_C ly) 256 IMG ltac:(lia) IC (AGis.pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl))|].
exact (zone3_intro ly (ly_D ly) 4096 IMG ltac:(lia) ID (AGis.pairwise_ij _ _ 7 1 _ _ HD eq_refl eq_refl)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The constant cells and the depot at one layout (cgif's AGix Section c at reply's image).                        *)
(* Every lemma of Section c is abstracted over all of its variables, in their declaration order (as cgif's AGix). *)
Local Set Default Proof Using "All".
Section c.
Variables (B : asyms) (ly : alayout).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.

Lemma const_cells_zone : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
CZONE ly (aeval B ly (c_at c) + k).
Proof.
intros c k Hin Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. unfold CZONE.
  pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk;
      rewrite ?ETP, ?EIN, ?HTSD; unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, kStackSpan in *; zlia |]
  | False => destruct Hin
  end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_ok c Hin) as Hc. unfold abs_cell_ok in Hc.
  destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval].
  apply andb_prop in Hc as [Hz Hc]. apply Z.leb_le in Hz.
  apply Bool.orb_prop in Hc. unfold CZONE. destruct Hc as [Hc|Hc]; [apply Z.leb_le in Hc; zlia|].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. zlia.
Qed.

Lemma CZONE_range : forall a, CZONE ly a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof (lo_app ly LY) as HA. pose proof ASAN_CEIL_range as [CR _].
pose proof (AGis.Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (AGis.Forall_nth' _ _ 6 _ HA eq_refl) as IC.
pose proof (AGis.Forall_nth' _ _ 7 _ HA eq_refl) as ID.
cbn beta in IT, IC, ID. cbn [fst snd] in IT, IC, ID.
unfold in_app, CZONE, TFIB_TSD, kThreadObjSize, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma DZONE_range : forall a, AGis.DZONE ly a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof (@AGis.blocks_facts _ ly LY IMG) as (NBhi & SBhi & _). unfold AGis.DZONE in Ha.
clear - Ha NBhi SBhi. ceil. unfold zone3, kNodesBlockSize, kStoreBlockSize in *. zlia.
Qed.

Lemma cell_holds_agree : forall (rd rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by zlia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
  rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by zlia. rewrite Z.add_0_r. exact Hb.
Qed.

Lemma aview_agree : forall (W : world tfibsegs) (mem mem' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a.
Proof using. intros W mem mem' a Ha He. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) mem mem' a He). reflexivity. Qed.

(* Reply B's depot bound (YFix.depot_ids_bound, B/YFix.v:356): the depot's traces are distinct members of the
   universe, so it holds at most 4097 of them. *)
(* P'': when reply takes the layer's depot model, this premise pair is `depot_fits (as_universe B) (st_depot S')`
   (YG01.v:260) and the bound comes from depot_len_bound, as in cgif's AGix.depot_ids_bound. *)
Lemma depot_ids_bound : forall S', List.NoDup (st_depot S') -> incl (st_depot S') (as_universe B) -> depot_ids S' <= 4097.
Proof.
intros S' ND INC. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). zlia.
Qed.

Lemma depot_mem_ok_agree : forall S' (rd rd' : reader), depot_ids S' <= 4098 ->
(forall a, AGis.DZONE ly a -> rd' a = rd a) -> CLdepot.depot_mem_ok B ly S' rd -> CLdepot.depot_mem_ok B ly S' rd'.
Proof.
intros S' rd rd' HID He (D1' & D2 & D3). pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + d_map1 + 8) \/ (TFIB_STORE <= a < TFIB_STORE + 32) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. apply He. unfold AGis.DZONE, TFIB_DEPOT, TFIB_STORE, d_map1 in *. zlia. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (cell_holds_agree rd); [| exact (proj1 (Forall_forall _ _) D1' c Hc)].
  intros k Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk; rewrite ?ED, ?ES;
    unfold d_nuniq, d_map1, s_total, s_block0 in *; zlia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
  + intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|].
    rewrite ED. unfold d_tab_words, d_map1 in *. zlia.
  + intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
    * intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. unfold kNodesBlockSize. zlia.
    * intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. unfold kNodesBlockSize. zlia.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
  cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; rewrite ?ED, ?ES;
    unfold d_nuniq, d_map1 in *; zlia.
Qed.

(* CLdepotcgif.const_noizone at reply: no constant cell's byte is in the internal allocator's zone. *)
Lemma const_noizone : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
~ DGgi.IZONE (aeval B ly (c_at c) + k).
Proof.
intros c k Hin Hk.
rewrite (ts_const B TS ly) in Hin.
pose proof (proj1 (forallb_forall _ _) (Tfib_const_noial ly) c Hin) as K. unfold const_noial in K.
destruct (zoneTCD ly LY IMG) as (ZT & ZC & ZD).
unfold zone3, zone3cases in ZT, ZC, ZD.
unfold DGgi.IZONE.
destruct (c_at c) eqn:Ea; cbn [aeval]; try discriminate K.
- exact (noial_ok _ _ k K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg,
  kThreadObjSize in *. lia.
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
- rewrite HTSD. exact (noial_ok _ _ k K Hk).
- rewrite (ts_inst B TS). exact (noial_ok _ _ k K Hk).
- rewrite (ts_tp B TS). exact (noial_ok _ _ k K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The row: dep_keep_img B KEEP (YGcfInstDepot.v:154), its body at reply's instances, at the two zone pairs.       *)

(* Allocate (YGcfInstF1Wcgif.v:96 dep_keep_a_cgif's twin): KEEP := ag_dzone \/ ag_czone, i.e. AGis.DZONE \/
   AGif0reply.CZONE at AGImg_reply. *)
Theorem dep_keep_a_B : forall B, @im_syms AImg_reply B ->
forall ly S (W : world (@im_segs AImg_reply)) (mem0 mem : word -> option byte),
layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B ->
(* P'': depot_fits (as_universe B) (st_depot S), YG01.v:260, replaces the next two premises. *)
List.NoDup (st_depot S) -> incl (st_depot S) (as_universe B) ->
Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem0) ->
(forall x : word, ImgBaseAG.ag_dzone ly (bv_unsigned x) \/ ImgBaseAG.ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem).
Proof.
intros B TS ly S W mem0 mem LY IMG TSD ND INC CST DEP MEQ. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply Forall_forall. intros c Hc.
  apply (cell_holds_agree B ly TS LY IMG HTSD (aview tfibsegs (w_H W) mem0)); [| exact (proj1 (Forall_forall _ _) CST c Hc)].
  intros k Hk. pose proof (const_cells_zone B ly TS LY IMG HTSD c k Hc Hk) as Z1.
  pose proof (CZONE_range B ly TS LY IMG HTSD _ Z1) as R.
  apply (aview_agree W mem0 mem _ R). apply MEQ. rewrite unsigned_lit_small by exact R. right. exact Z1.
- apply (depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (depot_ids_bound B ly TS LY IMG HTSD S ND INC). lia.
  + intros a Ha. pose proof (DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.

(* Deallocate (YGcfInstF1Wcgif.v:109 dep_keep_d_cgif's twin): KEEP := dg_dzone \/ (dg_czone /\ ~ dg_izone), i.e.
   DGgi.DZONE \/ (AGif0reply.CZONE /\ ~ DGgi.IZONE) at DImg_reply. *)
Theorem dep_keep_d_B : forall B, @im_syms AImg_reply B ->
forall ly S (W : world (@im_segs AImg_reply)) (mem0 mem : word -> option byte),
layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B ->
(* P'': depot_fits (as_universe B) (st_depot S), YG01.v:260, replaces the next two premises. *)
List.NoDup (st_depot S) -> incl (st_depot S) (as_universe B) ->
Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem0) ->
(forall x : word, ImgBaseDG.dg_dzone ly (bv_unsigned x) \/
  (ImgBaseDG.dg_czone ly (bv_unsigned x) /\ ~ ImgBaseDG.dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem).
Proof.
intros B TS ly S W mem0 mem LY IMG TSD ND INC CST DEP MEQ. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply Forall_forall. intros c Hc.
  apply (cell_holds_agree B ly TS LY IMG HTSD (aview tfibsegs (w_H W) mem0)); [| exact (proj1 (Forall_forall _ _) CST c Hc)].
  intros k Hk. pose proof (const_cells_zone B ly TS LY IMG HTSD c k Hc Hk) as Z1.
  pose proof (CZONE_range B ly TS LY IMG HTSD _ Z1) as R.
  apply (aview_agree W mem0 mem _ R). apply MEQ. rewrite unsigned_lit_small by exact R. right.
  split; [exact Z1 | exact (const_noizone B ly TS LY IMG HTSD c k Hc Hk)].
- apply (depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (depot_ids_bound B ly TS LY IMG HTSD S ND INC). lia.
  + intros a Ha. pose proof (DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.

End d.
