(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (lane F1 of the generic cf instance layer; integrator ReallocPrimary).
   SATISFIABILITY WITNESSES at preset's REAL image A (A', the #102 pin fuzz_preset.asan
   1be0f53d96cb), for the image and contract hypotheses of the cf layer's errno / depot / enqueue files, taken by path into
   lib/Reusable (YGcfInstErrno / YGcfInstDepot / YGcfInstEnq, copies of lane F1's files, provenance line in each).  The twin of c5's
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstF1Wcgif.v at image A, from preset's own proved files only:
   - [errno_img_cf_A]: YGcfInstErrno.ErrnoImgCf from A/ErrnoApartA.v's nine lemmas (at AImg_A / AGImg_A / DImg_A);
   - [errno_seg_A] / [errno_nstatic_A]: errno's bytes are segment bytes (AB13.tfib_rw_rom) and lie in no owned static
     range (AF0m.Tfib_owned_static): the two UNIT IMAGE obligations of YGcfInstErrno.v at image A';
   - [IMG_COVER_A]: the kit's image premise YGcfDIface.IMG_COVER (AF0x.img_cover_of_ledger's script over ALedger_cf);
   - [noial_A] .. [const_noizone_A]: the constant cells avoid the internal allocator's zone (CLdepotcgif.v:43-111's
     script at image A; preset has no CLdepotcgif);
   - [dep_fp_a_A] / [dep_fp_d_A] / [dep_keep_a_A] / [dep_keep_d_A]: YGcfInstDepot's image premises (A/AGix.v's
     footprint_DZONE / const_kept / depot_mem_ok_agree / cell_holds_agree);
   - [depot_spec_a_A] / [depot_spec_d_A]: the released depot contract at A (A/AFem.v:1523 tfib_depot_ok);
   - [if_depot_cf_at_A] / [di_depot_cf_at_A] / [de_depot_cf_at_A]: YGcfInstDepot's three fields at image A with every
     image hypothesis discharged, for any walk relation that gives ARcf at A's segments.
   Image B' has no depot contract (no AU/AFl0, AU/AFem): its instance is OPEN.  The S-Props (ErrnoApartS) have no
   preset file: no F1 top uses them.  rule 24: no function proved (kind: instance discharge at preset's image from
   preset's proved lemmas). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGis AGix AGImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgi AFgn AB13 AFem ErrnoApartA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot ErrnoG YGcfDIface YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstErrno YGcfInstDepot.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. errno.                                                                                                        *)
Theorem errno_img_cf_A : ErrnoImgCf.
Proof.
constructor.
- exact ErrnoApartA.errno_in_img_cgif.
- exact ErrnoApartA.errno_unhidden_cgif.
- exact ErrnoApartA.errno_apart_dzone_ag_cgif.
- exact ErrnoApartA.errno_apart_shadow_ag_cgif.
- exact ErrnoApartA.errno_apart_inst_ag_cgif.
- exact ErrnoApartA.errno_apart_dzone_d_cgif.
- exact ErrnoApartA.errno_apart_izone_cgif.
- exact ErrnoApartA.errno_apart_zone3_d_cgif.
- exact ErrnoApartA.errno_apart_inst_d_cgif.
Qed.

(* AF0x.img_cover_of_ledger's script (AF0x.v:58-65) over ALedger_cf. *)
Theorem IMG_COVER_A : YGcfDIface.IMG_COVER.
Proof.
intros ly S md L. change (AF0x.img_cover ly). split.
- destruct (alc_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
  cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (alc_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
  cbn in H. unfold TFIB_IMG_END. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The constant cells avoid the internal allocator's zone (CLdepotcgif.v:43-111 at image A).                     *)
Definition noial_A (a w : Z) : bool :=
(a + w <=? TFIB_IAL_LO) || ((TFIB_IAL_HI <=? a) && (a + w <=? TFIB_IAL_FLAG)) || (TFIB_IAL_FLAG + 4 <=? a).
Definition const_noial_A (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => noial_A a w
| ATsd k => noial_A (TFIB_TSD + k) w
| ATp k => noial_A (TFIB_TP + k) w
| AInst k => noial_A (TFIB_INST + k) w
| AT k => (0 <=? k) && (k + w <=? 80)
| AC k => (0 <=? k) && (k + w <=? 256)
| AD k => (0 <=? k) && (k + w <=? 4096)
| _ => false
end.
Lemma Tfib_const_noial_A : forall ly, forallb const_noial_A (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma noial_ok_A : forall a w i, noial_A a w = true -> 0 <= i < w ->
~ (TFIB_IAL_LO <= a + i < TFIB_IAL_HI \/ TFIB_IAL_FLAG <= a + i < TFIB_IAL_FLAG + 4).
Proof.
intros a w i K Hi. unfold noial_A in K.
apply Bool.orb_true_iff in K. destruct K as [K|K].
- apply Bool.orb_true_iff in K. destruct K as [K|K].
  + apply Z.leb_le in K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
  + apply Bool.andb_true_iff in K. destruct K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
- apply Z.leb_le in K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
Qed.

Lemma zoneTCD_A : forall ly, layout_ok ly -> AF0x.img_cover ly ->
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

Lemma const_noizone_A : forall (B : asyms), TfibSyms B -> forall ly, layout_ok ly -> AF0x.img_cover ly ->
ly_tsd ly = TFIB_TSD ->
forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
~ AFgn.IZONE (aeval B ly (c_at c) + k).
Proof.
intros B TS ly LY IMG HTSD c k Hin Hk.
rewrite (ts_const B TS ly) in Hin.
pose proof (proj1 (forallb_forall _ _) (Tfib_const_noial_A ly) c Hin) as K. unfold const_noial_A in K.
destruct (zoneTCD_A ly LY IMG) as (ZT & ZC & ZD).
unfold zone3, zone3cases in ZT, ZC, ZD.
unfold AFgn.IZONE.
destruct (c_at c) eqn:Ea; cbn [aeval]; try discriminate K.
- exact (noial_ok_A _ _ k K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg,
  kThreadObjSize in *. lia.
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
- rewrite HTSD. exact (noial_ok_A _ _ k K Hk).
- rewrite (ts_inst B TS). exact (noial_ok_A _ _ k K Hk).
- rewrite (ts_tp B TS). exact (noial_ok_A _ _ k K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* errno's 4 bytes are bytes of A''s segment table (AB13.tfib_rw_rom: every byte of [0xa1000, 0x600000)). *)
Theorem errno_seg_A : errno_seg_t B.
Proof.
intros a Ha. rewrite (ts_errno B TS) in Ha. change im_segs with tfibsegs.
apply AB13.tfib_rw_rom. unfold TFIB_ERRNO in Ha. lia.
Qed.

(* errno is in no owned static range of A (AF0m.Tfib_owned_static). *)
Theorem errno_nstatic_A : errno_nstatic_t B.
Proof.
intros a Ha O. rewrite (ts_errno B TS) in Ha.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The depot's image premises at A (A/AGix.v) and the released contract (A/AFem.v).                              *)
Theorem dep_fp_a_A : dep_fp_img B ag_dzone.
Proof.
intros ly a LY IMG TSD FP.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
exact (AGix.footprint_DZONE B ly TS LY IMG HTSD a FP).
Qed.

Theorem dep_fp_d_A : dep_fp_img B dg_dzone.
Proof.
intros ly a LY IMG TSD FP.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
exact (AGix.footprint_DZONE B ly TS LY IMG HTSD a FP).
Qed.

Theorem dep_keep_a_A : dep_keep_img B (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof.
intros ly S W mem0 mem LY IMG TSD HDF CST DEP MEQ.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply (AGix.const_kept B ly TS LY IMG HTSD W mem0 mem CST). intros x Hx. apply MEQ. right. exact Hx.
- apply (AGix.depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (AGix.depot_ids_bound B ly TS LY IMG HTSD S HDF). lia.
  + intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (AGix.aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.

Theorem dep_keep_d_A : dep_keep_img B (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)).
Proof.
intros ly S W mem0 mem LY IMG TSD HDF CST DEP MEQ.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply Forall_forall. intros c Hc.
  apply (AGix.cell_holds_agree B ly TS LY IMG HTSD (aview tfibsegs (w_H W) mem0));
    [| exact (proj1 (Forall_forall _ _) CST c Hc)].
  intros k Hk.
  pose proof (AGix.const_cells_zone B ly TS LY IMG HTSD c k Hc Hk) as Z1.
  pose proof (AGix.CZONE_range B ly TS LY IMG HTSD _ Z1) as R.
  apply (AGix.aview_agree W mem0 mem _ R).
  apply MEQ. rewrite unsigned_lit_small by exact R. right.
  split; [exact Z1 | exact (const_noizone_A B TS ly LY IMG HTSD c k Hc Hk)].
- apply (AGix.depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (AGix.depot_ids_bound B ly TS LY IMG HTSD S HDF). lia.
  + intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (AGix.aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.

(* The released depot contract at A (A/AFem.v:1523), at Allocate's and Deallocate's entry pcs. *)
Theorem depot_spec_a_A : (forall t, as_dhash B t = tfib_dhash t) ->
CLdepot.depot_spec_x im_segs ag_depot_put im_tp im_img_cover B.
Proof. intros HDH. exact (AFem.tfib_depot_ok B TS HDH). Qed.

Theorem depot_spec_d_A : (forall t, as_dhash B t = tfib_dhash t) ->
CLdepot.depot_spec_x im_segs dg_depot im_tp im_img_cover B.
Proof. intros HDH. exact (AFem.tfib_depot_ok B TS HDH). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. YGcfInstDepot's fields at image A, every image hypothesis discharged, for any walk relation over ARcf.        *)
Section h.
Variable Hp : list Z.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Hypothesis HAR : forall inst ly S W mem md, ARX inst ly S W mem md -> ARcf im_segs B ly S Hp W mem md.
Hypothesis HDH : forall t, as_dhash B t = tfib_dhash t.

Theorem if_depot_cf_at_A :
CLdepot.depot_field im_segs ag_depot_put im_tp B ARX (YGcfInstBase.cf_tr_ok B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof. exact (if_depot_cf B Hp ARX HAR IMG_COVER_A dep_keep_a_A dep_fp_a_A (depot_spec_a_A HDH)). Qed.

Theorem di_depot_cf_at_A :
CLdepot.depot_field im_segs dg_depot im_tp B ARX (YGcfInstBase.cf_tr_ok B) dg_dzone
  (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)).
Proof. exact (di_depot_cf B Hp ARX HAR IMG_COVER_A dep_keep_d_A dep_fp_d_A (depot_spec_d_A HDH)). Qed.

Theorem de_depot_cf_at_A :
ErrnoG.de_depot_t B (YGcfInstBase.cf_tr_ok B) ARX (dpost_cf B).
Proof.
exact (de_depot_cf B Hp ARX HAR TS errno_img_cf_A IMG_COVER_A dep_keep_d_A dep_fp_d_A (depot_spec_d_A HDH)).
Qed.
End h.
End b.
End a.
