(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/CLdepotcgif.v (cold/c-asan-realloc-c5 ced28ed2383, file sha256 12a504bff9a6) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* cgif_file's instance of the generic depot sub-interface (CLdepot.DepotSub), and the two depot fields it
   discharges: AGif0n.if_depot (Allocate's call, QuarantineChunk's twin on the hit path) and DGif0.di_depot
   (Deallocate's call).  Both come from the released machine-level contract YFl0.tfib_depot_spec; this file adds
   no walk.

   The two shapes differ only in the zone the caller keeps as at the relation's memory: Allocate keeps the depot
   zone and the constant cells, Deallocate keeps the depot zone and the constant cells outside the internal
   allocator's zone (its walk has already written there).  For the second shape the constant cells must be shown
   to avoid that zone: [const_noizone], from the same boolean check on [Tfib_const] that YFfy.const_loc_ok uses,
   plus the layout's zone3 facts for the thread, context and TSD objects. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGis AGix AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGgi.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The constant cells avoid the internal allocator's zone.                                                          *)

(* The cell's bytes miss [TFIB_IAL_LO, TFIB_IAL_HI) and [TFIB_IAL_FLAG, TFIB_IAL_FLAG + 4). *)
Definition noial (a w : Z) : bool :=
(a + w <=? TFIB_IAL_LO) || ((TFIB_IAL_HI <=? a) && (a + w <=? TFIB_IAL_FLAG)) || (TFIB_IAL_FLAG + 4 <=? a).
(* Per cell: the image-absolute cells are checked by [noial]; the thread, context and D objects are checked by
   their offset, and placed by the layout (zoneTCD below). *)
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

(* The thread object, the context object and the D page are off the image (DGgi.LYB / LYBD's script). *)
Lemma zoneTCD : forall ly, layout_ok ly -> img_cover ly ->
zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
intros ly LY IMG.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth' _ _ 6 _ HA eq_refl) as IC.
pose proof (Forall_nth' _ _ 7 _ HA eq_refl) as ID.
cbn beta in IT, IC, ID. cbn [fst snd] in IT, IC, ID.
split; [exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT
  (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl))|].
split; [exact (zone3_intro ly (ly_C ly) 256 IMG ltac:(lia) IC (pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl))|].
exact (zone3_intro ly (ly_D ly) 4096 IMG ltac:(lia) ID (pairwise_ij _ _ 7 1 _ _ HD eq_refl eq_refl)).
Qed.

Lemma const_noizone : forall (B : asyms), TfibSyms B -> forall ly, layout_ok ly -> img_cover ly ->
ly_tsd ly = TFIB_TSD ->
forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
~ DGgi.IZONE (aeval B ly (c_at c) + k).
Proof.
intros B TS ly LY IMG HTSD c k Hin Hk.
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

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The sub-interface for cgif_file.                                                                                 *)
Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* The trace premise of the cgif instances (C5: a predicate over the trace and the state). *)
Definition Ucgif (tr : list Z) (_ : astate) : Prop := In tr (as_universe B).
(* Allocate's zone pair (AGif0n.if_depot) and Deallocate's (DGif0.di_depot). *)
Definition KEEPa (ly : alayout) (a : Z) : Prop := AGis.DZONE ly a \/ CZONE ly a.
Definition KEEPd (ly : alayout) (a : Z) : Prop := DGgi.DZONE ly a \/ (CZONE ly a /\ ~ DGgi.IZONE a).

(* The relation's layout facts, shared by the fields. *)
Lemma arx_facts : forall inst ly S W mem md, ARX_cgif B inst ly S W mem md ->
layout_ok ly /\ img_cover ly /\ ly_tsd ly = TFIB_TSD /\ ARm B ly S (aview tfibsegs (w_H W) mem).
Proof.
intros inst ly S W mem md [_ HAR]. pose proof (proj1 HAR) as HARm.
pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
split; [exact LY|]. split; [exact IMG|].
split; [rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS) | exact HARm].
Qed.

(* The depot's memory facts transfer from the relation's memory to any memory that keeps the depot zone. *)
Lemma dep_keep : forall inst ly S W mem0 md0 (mem : word -> option byte),
ARX_cgif B inst ly S W mem0 md0 ->
(forall a, AGis.DZONE ly a -> mem (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)) ->
CLdepot.depot_mem_ok B ly S (aview tfibsegs (w_H W) mem).
Proof.
intros inst ly S W mem0 md0 mem HARX MEQ.
destruct (arx_facts inst ly S W mem0 md0 HARX) as (LY & IMG & HTSD & HARm).
apply (AGix.depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
- pose proof (AGix.depot_ids_bound B ly TS LY IMG HTSD S (wf_depot _ _ _ _ _ (am_wf _ _ _ _ HARm))). lia.
- intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
  exact (AGix.aview_agree W mem0 mem a Ra (MEQ a Ha)).
- exact (AGix.depot_at0 B ly TS LY IMG HTSD S W mem0 HARm).
Qed.

(* Allocate's sub-interface. *)
Theorem sub_a : CLdepot.DepotSub tfibsegs img_cover B (ARX_cgif B) Ucgif AGis.DZONE KEEPa.
Proof.
constructor.
- intros inst ly S W mem md HARX. destruct (arx_facts inst ly S W mem md HARX) as (LY & IMG & _ & HARm).
  split; [exact LY|]. split; [exact IMG | exact (am_wf _ _ _ _ HARm)].
- intros inst ly S W mem md tr HARX HU. destruct (arx_facts inst ly S W mem md HARX) as (_ & _ & _ & HARm). exact (admits_fix _ _ S (am_universe _ _ _ _ HARm) HU).
- intros inst ly S W mem0 md0 mem HARX MEQ.
  destruct (arx_facts inst ly S W mem0 md0 HARX) as (LY & IMG & HTSD & HARm).
  split.
  + apply (AGix.const_kept B ly TS LY IMG HTSD W mem0 mem); [exact (am_const B ly S _ HARm)|].
    intros x Hx. apply MEQ. right. exact Hx.
  + apply (dep_keep inst ly S W mem0 md0 mem HARX).
    intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
- intros inst ly S W mem md a HARX FP.
  destruct (arx_facts inst ly S W mem md HARX) as (LY & IMG & HTSD & _).
  exact (AGix.footprint_DZONE B ly TS LY IMG HTSD a FP).
Qed.

(* Deallocate's sub-interface: the constant cells are kept only outside the internal allocator's zone. *)
Theorem sub_d : CLdepot.DepotSub tfibsegs img_cover B (ARX_cgif B) Ucgif DGgi.DZONE KEEPd.
Proof.
constructor.
- intros inst ly S W mem md HARX. destruct (arx_facts inst ly S W mem md HARX) as (LY & IMG & _ & HARm).
  split; [exact LY|]. split; [exact IMG | exact (am_wf _ _ _ _ HARm)].
- intros inst ly S W mem md tr HARX HU. destruct (arx_facts inst ly S W mem md HARX) as (_ & _ & _ & HARm). exact (admits_fix _ _ S (am_universe _ _ _ _ HARm) HU).
- intros inst ly S W mem0 md0 mem HARX MEQ.
  destruct (arx_facts inst ly S W mem0 md0 HARX) as (LY & IMG & HTSD & HARm).
  split.
  + apply Forall_forall. intros c Hc.
    apply (AGix.cell_holds_agree B ly TS LY IMG HTSD (aview tfibsegs (w_H W) mem0));
      [| exact (proj1 (Forall_forall _ _) (am_const B ly S _ HARm) c Hc)].
    intros k Hk.
    pose proof (AGix.const_cells_zone B ly TS LY IMG HTSD c k Hc Hk) as Z1.
    pose proof (AGix.CZONE_range B ly TS LY IMG HTSD _ Z1) as R.
    apply (AGix.aview_agree W mem0 mem _ R).
    apply MEQ. rewrite unsigned_lit_small by exact R. right.
    split; [exact Z1 | exact (const_noizone B TS ly LY IMG HTSD c k Hc Hk)].
  + apply (dep_keep inst ly S W mem0 md0 mem HARX).
    intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
- intros inst ly S W mem md a HARX FP.
  destruct (arx_facts inst ly S W mem md HARX) as (LY & IMG & HTSD & _).
  exact (AGix.footprint_DZONE B ly TS LY IMG HTSD a FP).
Qed.

(* The released contract is the generic one at cgif_file's image. *)
Lemma spec_x_of_tfib : tfib_depot_spec B ->
CLdepot.depot_spec_x tfibsegs A_StackDepotPut TFIB_TP img_cover B.
Proof.
intros H. unfold CLdepot.depot_spec_x. intros W ly S regs mem md buf tr. cbv zeta. intros LY IC WF IN.
exact (H W ly S regs mem md buf tr LY IC WF IN).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The two interface fields.                                                                                        *)

(* AGif0n.AIface's [if_depot] at ARX_cgif, with the depot post [CLdepot.dpost_x tfibsegs B]. *)
Theorem if_depot_cgif : tfib_depot_spec B ->
forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX_cgif B inst ly S W mem0 md0 -> Ucgif tr S ->
(forall x : word, DZONE ly (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ DZONE ly (bv_unsigned x) -> mem' x = mem x) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  CLdepot.dpost_x tfibsegs B inst ly S W tr z mem').
Proof.
intros HD1.
exact (CLdepot.depot_field_ok tfibsegs A_StackDepotPut TFIB_TP img_cover B (ARX_cgif B) Ucgif
  AGis.DZONE KEEPa sub_a (spec_x_of_tfib HD1)).
Qed.

(* DGif0.DIface's [di_depot] at ARX_cgif, with the same depot post. *)
Theorem di_depot_cgif : tfib_depot_spec B ->
forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX_cgif B inst ly S W mem0 md0 -> Ucgif tr S ->
(forall x : word, DGgi.DZONE ly (bv_unsigned x) \/ (CZONE ly (bv_unsigned x) /\ ~ DGgi.IZONE (bv_unsigned x)) ->
  mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ DGgi.DZONE ly (bv_unsigned x) -> mem' x = mem x) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  CLdepot.dpost_x tfibsegs B inst ly S W tr z mem').
Proof.
intros HD1.
exact (CLdepot.depot_field_ok tfibsegs A_StackDepotPut TFIB_TP img_cover B (ARX_cgif B) Ucgif
  DGgi.DZONE KEEPd sub_d (spec_x_of_tfib HD1)).
Qed.

(* The answer the depot post carries (AGif0n.if_dpost_aok / DGif0.di_dpost_aok). *)
Theorem dpost_aok_cgif : forall inst ly S W tr z m,
CLdepot.dpost_x tfibsegs B inst ly S W tr z m -> aok S (KDepot tr) z.
Proof. intros inst ly S W tr z m H. exact (proj1 H). Qed.
End b.
End a.
