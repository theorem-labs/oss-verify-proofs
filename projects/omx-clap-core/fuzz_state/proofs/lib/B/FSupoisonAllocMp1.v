(* Region conditions of the malloc PRIMARY walk under ARU: threads lib/A/AF0w.v's released walk (AFij.v, AFik.v, AFil.v, AFim.v, AFin.v) and the glue it calls (AFhy.v, AFis.v, AFiy.v, AFjc.v, AFiz.v, AFj0.v, AFje.v, AFix.v, AFjb.v, AFj1.v, AFjf.v, AFj2.v, AFjg.v) over lib/A/FSupoison.v, FSupoisonU.v and the kit FSupoisonAllocR.v. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: image-B port (fuzz_state.asan-ubsan, sha256 5ac5ce0954f87e2d) of lib/A/FSupoisonAllocMp1.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), the kit is lib/B/FSupoisonAllocR / Rf / Rt, every statement is over B's tfibsegs (lib/B/YB1v.v); the image's shadow bounds TFIB_IMG_LO / 8 and TFIB_IMG_END / 8 are computed from lib/B/YF0x.v's names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK04 YP0m YP09 YP0l YI04 YA0i YA0n YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* Constants kept from the A template are image-independent sizes: 256 (the context map) and 4096 (the D page). *)
(* A value by name, evaluated to its literal. *)
Local Notation "'zlit' x" := ltac:(let v := eval vm_compute in (x : Z) in exact v) (at level 10, x at level 0, only parsing).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module AllocR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Region lemmas (to move to FSupoisonAllocR.v at integration)                                                        *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section r.
Variable B : asyms.

(* A byte below the shadow is never user-poisoned (UP's bytes are shadow bytes of live blocks). *)
Lemma offU_lit : forall ly S UP W mem md a, FSP.ARU tfibsegs B ly S UP W mem md ->
  0 <= a < SHADOW_OFF -> AllocR.offU UP a.
Proof. intros ly S UP W mem md a H Ha. apply (AllocR.offU_low B ly S UP W mem md a H). exact Ha. Qed.

(* Nor is a byte at or above the high application memory. *)
Lemma offU_hi : forall ly S UP W mem md a, FSP.ARU tfibsegs B ly S UP W mem md ->
  kHighMemBeg <= a < 2 ^ 64 -> AllocR.offU UP a.
Proof. intros ly S UP W mem md a H Ha. apply (AllocR.offU_high B ly S UP W mem md a H). exact Ha. Qed.

(* Every byte of one of the layout's owned extents (the primary reservation, Q, T, F, NB, SB, C, D) is application
   memory (layout_ok's lo_app), hence off UP. *)
Lemma offU_owned : forall ly S UP W mem md e a, FSP.ARU tfibsegs B ly S UP W mem md ->
  In e (owned_extents ly) -> fst e <= a < fst e + snd e -> AllocR.offU UP a.
Proof.
intros ly S UP W mem md e a H He Ha.
pose proof (am_layout B ly S _ (FSP.ARU_ARm tfibsegs B ly S UP W mem md H)) as LO.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) e He) as [A1 A2].
pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
apply (AllocR.offU_app B ly S UP W mem md a H);
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *; lia.
Qed.

(* No live block meets the loaded image: a block sits in a primary class region (above kHighMemBeg) or in a
   secondary extent, and the secondary extents are disjoint from ly_img, which covers the image. *)
Lemma no_block_in_img : forall ly S UP W mem md g, FSP.ARU tfibsegs B ly S UP W mem md ->
  TFIB_IMG_LO <= g -> g < TFIB_IMG_END ->
  forall p n0, In (p, n0) (ablocks B ly S) -> ~ (p <= g < p + req_size n0).
Proof.
intros ly S UP W mem md g H G1 G2 p n0 Hb Hin.
pose proof (FSP.ARU_AR tfibsegs B ly S UP W mem md H) as HAR.
pose proof (FSP.ARU_ARm tfibsegs B ly S UP W mem md H) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END in *.
destruct (AllocR.ablock_in_user B ly S _ p n0 M Hb) as [(c & Hc & R1 & R2 & R3) | (e & He & E1 & E2)].
- pose proof (region_in_prim ly c LO ltac:(lia)) as (_ & _ & _ & P4 & _).
  unfold kHighMemBeg in P4. lia.
- pose proof (proj2 (am_placed B ly S _ M)) as PD.
  pose proof (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
    ltac:(unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* Hence a shadow byte of the image is off UP: UP's bytes are shadow bytes of live blocks only. *)
Lemma offU_sh_img : forall ly S UP W mem md a, FSP.ARU tfibsegs B ly S UP W mem md ->
  SHADOW_OFF + TFIB_IMG_LO / 8 <= a -> a < SHADOW_OFF + TFIB_IMG_END / 8 -> AllocR.offU UP a.
Proof.
intros ly S UP W mem md a A1 A2 A3.
change (TFIB_IMG_LO / 8) with (zlit (TFIB_IMG_LO / 8)) in A2. change (TFIB_IMG_END / 8) with (zlit (TFIB_IMG_END / 8)) in A3.
assert (EQ : shadow_addr (8 * (a - SHADOW_OFF)) = a).
{ unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. unfold SHADOW_OFF in *. lia. }
rewrite <- EQ.
apply (AllocR.offU_shadow_nonlive B ly S UP W mem md (8 * (a - SHADOW_OFF)) A1);
  [unfold SHADOW_OFF in *; lia|].
apply (no_block_in_img ly S UP W mem md (8 * (a - SHADOW_OFF)) A1);
  unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image's constant cells (YF0m.v Tfib_const): where they sit, and that their bytes are off UP.                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* A literal byte range of the image, or a shadow byte range of the image. Port-from: lib/B/YFev.v:393 low_okd. *)
Definition cimgb (a w : Z) : bool :=
  ((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) ||
  ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).

(* Where every constant cell sits. Port-from: lib/B/YFev.v:396 const_loc_okd (the o_quar clause dropped: this
   file only needs the cell's location, not its disjointness from the quarantine window). *)
Definition const_locb (c : acell) : bool :=
  let w := Z.max 1 (Z.of_nat (c_w c)) in
  match c_at c with
  | ANum a => cimgb a w
  | AT o => (0 <=? o) && (o + w <=? kThreadObjSize)
  | AC o => (0 <=? o) && (o + w <=? 256)
  | AD o => (0 <=? o) && (o + w <=? 4096)
  | ATsd o => cimgb (TFIB_TSD + o) w
  | ATp o => cimgb (TFIB_TP + o) w
  | AInst o => cimgb (TFIB_INST + o) w
  | _ => false
  end.

Lemma Tfib_const_locb : forall ly, forallb const_locb (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Lemma offU_cimgb : forall ly S UP W mem md a w k, FSP.ARU tfibsegs B ly S UP W mem md ->
  cimgb a w = true -> 0 <= k < w -> AllocR.offU UP (a + k).
Proof.
intros ly S UP W mem md a w k H Ka Hk.
apply Bool.orb_prop in Ka as [Ka|Ka]; apply andb_prop in Ka as [K1 K2];
  apply Z.leb_le in K1; apply Z.leb_le in K2.
- apply (offU_lit ly S UP W mem md (a + k) H). unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. lia.
- apply (offU_sh_img ly S UP W mem md (a + k) H);
    change (TFIB_IMG_LO / 8) with (zlit (TFIB_IMG_LO / 8)) in *; change (TFIB_IMG_END / 8) with (zlit (TFIB_IMG_END / 8)) in *; lia.
Qed.

(* Every byte of every constant cell is off UP. *)
Lemma const_offU : forall ly S UP W mem md c k, TfibSyms B -> FSP.ARU tfibsegs B ly S UP W mem md ->
  ly_tsd ly = TFIB_TSD -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  AllocR.offU UP (aeval B ly (c_at c) + k).
Proof.
intros ly S UP W mem md c k TS H HTSD Hc Hk.
rewrite (ts_const B TS ly) in Hc.
pose proof (proj1 (forallb_forall _ _) (Tfib_const_locb ly) c Hc) as K. unfold const_locb in K.
destruct (c_at c) as [z|z|z|z|z|z|z|z|r z|z|z|z|z|z|z|z|z|z|e] eqn:EC; try discriminate K; cbn [aeval].
- exact (offU_cimgb ly S UP W mem md z _ k H K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  apply (offU_owned ly S UP W mem md (ly_T ly, kThreadObjSize) (ly_T ly + z + k) H
    ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. lia.
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  apply (offU_owned ly S UP W mem md (ly_C ly, 256) (ly_C ly + z + k) H
    ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. lia.
- rewrite HTSD. exact (offU_cimgb ly S UP W mem md (TFIB_TSD + z) _ k H K Hk).
- rewrite (ts_inst B TS). exact (offU_cimgb ly S UP W mem md (TFIB_INST + z) _ k H K Hk).
- rewrite (ts_tp B TS). exact (offU_cimgb ly S UP W mem md (TFIB_TP + z) _ k H K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  apply (offU_owned ly S UP W mem md (ly_D ly, 4096) (ly_D ly + z + k) H
    ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Moving cells and depot facts between two readings of memory.                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* Port-from: lib/B/YFix.v:334 cell_holds_agree, restated free of that file's section. *)
Lemma cell_holds_agree' : forall ly (rd rd' : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros ly rd rd' c E HC. unfold cell_holds in *. cbv zeta in *.
destruct (c_val c) as [e|mask vv].
- intros k Hk. rewrite (E (Z.of_nat k) ltac:(lia)). exact (HC k Hk).
- destruct HC as (b & Hb & Hm). pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
  exists b. split; [rewrite E0; exact Hb | exact Hm].
Qed.

Lemma cells_agree_list : forall ly (rd rd' : reader) (l : list acell),
  (forall c k, In c l -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
     rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
  Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros ly rd rd' l E F. rewrite Forall_forall in F |- *. intros c Hc.
exact (cell_holds_agree' ly rd rd' c (fun k Hk => E c k Hc Hk) (F c Hc)).
Qed.

(* The constant cells hold of the REAL memory of a run that kept them, given AR of the unpoisoned reading. *)
Lemma const_cells_real : forall ly S UP W mem md (m : word -> option byte),
  TfibSyms B -> FSP.ARU tfibsegs B ly S UP W mem md -> ly_tsd ly = TFIB_TSD ->
  (forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
     m (Z_to_bv 64 (aeval B ly (c_at c) + k)) = mem (Z_to_bv 64 (aeval B ly (c_at c) + k))) ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) m)) (as_const B ly).
Proof.
intros ly S UP W mem md m TS H HTSD MEQ.
apply (cells_agree_list ly (aview tfibsegs (w_H W) (FSP.unpoison UP mem)));
  [|exact (am_const B ly S _ (FSP.ARU_ARm tfibsegs B ly S UP W mem md H))].
intros c k Hc Hk.
rewrite (AllocR.aview_unpoison (w_H W) UP mem _ (const_offU ly S UP W mem md c k TS H HTSD Hc Hk)).
apply FSP.aview_at. exact (MEQ c k Hc Hk).
Qed.
End r.
End k.
