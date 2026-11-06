(* fuzz_state image A: the CLOSING of lib/A/FSReallocAG.v's Section g at the relocated allocator chain, so that
   FSupoisonRealloc.FS_AREALLOC_AU (the single premise of lib/A/FSClose.v's tops, route 1) rests on no hypothesis of
   fuzz_state's own but the two ARU callee lifts below (a Theorem Labs lane, 2026-10-29; restated by a Theorem Labs lane).

   rule 24: no function proved (kind: statement composition / instantiation; every walk is proved elsewhere).

   THE TWO SECTION HYPOTHESES.  H_refill_U and H_difR_U are FSReallocAG.v Section g's H_refill_U (FSReallocAG.v:287-288)
   and H_difR_U (:290-292) at the instance values below (im_segs := tfibsegs, rtree := refill_tree, dpostD := CLdepot.dpost_x
   tfibsegs, dbody := drain_body, L24 := 16385, QB := qloose, DRq := DGif1.DRq_cgif), for every B with TfibSyms B.  Their
   proofs (the ARU twins of AGif1m.refill_cgif and DIfaceRcgif.diface_r_cgif, from a Theorem Labs lane's FSupoisonAllocRt /
   FSupoisonAllocF* walks) are not written yet; they close these two hypotheses when they land.

   WHAT IS SUPPLIED, in FSReallocAG.v Section g's declaration order (the arguments of fs_arealloc_AU_closed):
     IM0        AGif2cgif.AImg_cgif      (then IMA = img_at tfibsegs AImg_cgif = AImg_cgif by conversion)
     AG IMS DI  AGif0cgif.AGImg_cgif, AGif4cgif.AImgS_cgif, DGif0cgif.DImg_cgif
     the 5 generic Allocate / Deallocate theorems:
       H_prim_if  AGtopcgif.aalloc_prim_realizes_if   H_missg  AGim0.alloc_missg_cf   H_missk  AGin0.alloc_missk_cf
       H_sec      AGio.alloc_sec                      H_dtop   DGtop.adealloc_realizes_raw_g
     the 9 record parameters (what the instances fix):
       dpostA AGif1.dpost_cgif   mtagA 3 (label 202260)   stagA 12 (label 449860)   rtree AFl1.refill_tree
       dpostD CLdepot.dpost_x tfibsegs   dbody AFeu.drain_body   L24 16385   QB qloose   DRq DGif1.DRq_cgif
     the 5 instance records:
       H_if AGif1.iface_cgif     H_ifk AGif1k.iface_cgif_k   H_ifm AGif1m.iface_cgif_m   H_ifs AGif5.ifaceS_cgif
       H_dif  DGif1.diface_cgif at L24 := 16385 with its six drain-side premises discharged as DGtopcgifC.v:31-41 does
              (DGif1d.di_drain_cgif, DGif1dI.di_requar_x/r/e_cgif, DGif1dI.di_rchunk_cgif, DGif1dI.di_cdealloc_cgif)
     B TS HDH   the generic theorem's own premises
     H_refill_U H_difR_U   this file's two Section hypotheses, at B and TS
     the 12 image premises, each at the instances above:
       HAI  inst_low ag_inst_ok           [fs_inst_ok_low]: FSupoisonARX.inst_low_window 0xa1578 0xa5760
       HAIk ag_inst_ok TFIB_INST          [fs_inst_ok_TFIB]: 0xa48d8 in AGif0cgif.inst_ok's window
       HAZ  zones_free .. ag_dzone ag_czone   [fs_zones_free_A]: FSupoisonARX.fs_zones_free at AGis.DZONE's and
                                          AGif0cgif.CZONE's literal bounds (0x179e08 0x5ca590; 0x10000 0x5fd000 0x7fff8000
                                          0x800b4000)
       HIL  img_low                       FSReallocAG.fs_img_low_vals
       HSHB ims_shb = SHADOW_OFF          eq_refl (AImgS_cgif.ims_shb := AGjm.SHBv = 0x7fff8000)
       HSZ  zones_free .. ims_dzone (CZS ly TFIB_INST)   [fs_zones_free_S]: FSReallocAG.fs_zones_free_CZS at AGjm.DZONE's
                                          bounds and AImgS_cgif's image-end / shadow-window literals
       HZ3  zone3_app                     FSReallocAG.fs_zone3_app
       HWF  wframe_up ims_wframe          FSupoisonARXmS.wframe_up_AGif0n
       HDI  inst_low dg_inst_ok           [fs_inst_ok_low] (DImg_cgif.dg_inst_ok := AGif0cgif.inst_ok)
       HDZ  zones_free .. dg_dzone (dg_czone \ dg_izone)   [fs_zones_free_DG]: [fs_zones_free_A], monotone in the CZONE
                                          argument
       HIZ  izone_low                     [fs_izone_low]: DGgi.IZONE's literals (0xa9140, 0x12a170, 0x1379c8) below
                                          SHADOW_OFF
       HIAL ial_local                     [fs_ial_local]: DGgi.IAL_POST reads only DGgi.IZONE cells
   The generic theorem is [fs_arealloc_AU_at_cgif] (forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
   FS_AREALLOC_AU tfibsegs B (as_universe B)); [fs_arealloc_AU_TfibB] is its corollary at AD2l.TfibB (TfibB_syms,
   the depot hash by eq_refl).

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
ImgBase ImgBaseAG ImgBaseAGS ImgBaseDG AllocG DeallocG AGif0n DIfaceR DMiface DMspec AGif4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YF0p CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m AF0x AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif AGif0cgif AGif4cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
AGtopcgif AGim0 AGin0 AGio DGtop AGif1 AGif1k AGif1m AGif5 DGif1 DGif1d DGif1dI DGgi AFeu AD2l
FSupoisonARX FSupoisonARXm FSupoisonARXmA FSupoisonARXmD FSupoisonARXmS FSupoisonRealloc FSRealloc_rmodel
FSReallocAGg FSReallocAG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonRealloc.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the two ARU callee lifts: FSReallocAG.v:287-288 and :290-292 at the instance values ---- *)

(* if_refill at ARU (the ARU twin of AGif1m.refill_cgif, AGif1m.v:157) *)
Hypothesis H_refill_U : forall B : asyms, TfibSyms B -> forall Up,
  FSupoisonARXmA.if_refill_t B (FSupoisonARXm.ARX_ARU tfibsegs B AF0m.TFIB_INST Up) (aowned B)
    FSRealloc_rmodel.FS_rpreA qtight refill_tree.
(* DIfaceR at ARU (the ARU twin of DIfaceRcgif.diface_r_cgif, DIfaceRcgif.v:42) *)
Hypothesis H_difR_U : forall B : asyms, TfibSyms B -> forall Up,
  DIfaceR B (FSReallocAGg.UA B) (FSupoisonARXm.ARX_ARU tfibsegs B AF0m.TFIB_INST Up)
    (FSupoisonARXm.ARX_ARU tfibsegs B AF0m.TFIB_INST Up) (aowned B) FSRealloc_rmodel.FS_rpreD qtight
    (FSupoisonARXm.fpreU tfibsegs B Up) (CLdepot.dpost_x tfibsegs B) AFeu.drain_body 16385 qloose (DGif1.DRq_cgif B).

(* ---- the image premises at the relocation's instances ---- *)

(* HAI, HDI: the instance window AGif0cgif.inst_ok = [0xa1578, 0xa5760) lies below the shadow. *)
Lemma fs_inst_ok_low : FSupoisonARXm.inst_low AGif0cgif.inst_ok.
Proof. exact (FSupoisonARX.inst_low_window 0xa1578 0xa5760 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)). Qed.

(* HAIk: fs's instance object 0xa48d8 (AF0m.v:16) is in that window. *)
Lemma fs_inst_ok_TFIB : AGif0cgif.inst_ok AF0m.TFIB_INST.
Proof. unfold AGif0cgif.inst_ok, AF0m.TFIB_INST. split; [lia | split; [lia | reflexivity]]. Qed.

(* HAZ: AGis.DZONE and AGif0cgif.CZONE are FSupoisonARX's two shapes at these literal bounds. *)
Lemma fs_zones_free_A : forall B, FSupoisonARXm.zones_free tfibsegs B (FSupoisonARX.DZONE_shape 0x179e08 0x5ca590)
  (FSupoisonARX.CZONE_shape 0x10000 0x5fd000 0x7fff8000 0x800b4000 AF0m.TFIB_TSD).
Proof.
intros B. apply FSupoisonARX.fs_zones_free; unfold AF0x.TFIB_IMG_END, SHADOW_OFF; try lia.
unfold shadow_addr, SHADOW_OFF. assert (E : 6279168 / 8 = 784896) by reflexivity. rewrite E. lia.
Qed.

(* HDZ: the same zones, the CZONE argument cut down by DGgi.IZONE. *)
Lemma fs_zones_free_DG : forall B, FSupoisonARXm.zones_free tfibsegs B (FSupoisonARX.DZONE_shape 0x179e08 0x5ca590)
  (fun ly a => FSupoisonARX.CZONE_shape 0x10000 0x5fd000 0x7fff8000 0x800b4000 AF0m.TFIB_TSD ly a /\ ~ DGgi.IZONE a).
Proof.
intros B ly S W mem md a HAR Hz. apply (fs_zones_free_A B ly S W mem md a HAR).
destruct Hz as [HD | [HC _]]; [left; exact HD | right; exact HC].
Qed.

(* HSZ: FSReallocAG.fs_zones_free_CZS at AImgS_cgif (dzone AGjm.DZONE, image end 0x5fd000, shadow window
   [0x7fff8000, 0x800b4000)) and AImg_cgif's TSD cell. *)
Lemma fs_zones_free_S : forall B, FSupoisonARXm.zones_free tfibsegs B ims_dzone (fun ly a => CZS ly AF0m.TFIB_INST a).
Proof.
intros B.
apply (@FSReallocAG.fs_zones_free_CZS rc AImg_cgif AImgS_cgif B 0x179e08 0x5ca590 AF0m.TFIB_INST).
- intros ly a H. exact H.
- lia.
- unfold SHADOW_OFF. lia.
- unfold AF0m.TFIB_INST. lia.
- unfold AF0m.TFIB_INST, SHADOW_OFF. lia.
- change (0x5fd000 <= SHADOW_OFF). unfold SHADOW_OFF. lia.
- change (0 <= 0x7fff8000). lia.
- change (0x800b4000 <= shadow_addr AF0x.TFIB_IMG_END). unfold shadow_addr, SHADOW_OFF, AF0x.TFIB_IMG_END.
  assert (E : 6279168 / 8 = 784896) by reflexivity. rewrite E. lia.
- change (0 <= AF0m.TFIB_TSD). unfold AF0m.TFIB_TSD. lia.
- change (AF0m.TFIB_TSD + 8 <= SHADOW_OFF). unfold AF0m.TFIB_TSD, SHADOW_OFF. lia.
Qed.

(* HIZ: DGgi.IZONE = [TFIB_IAL_LO, TFIB_IAL_HI) \/ [TFIB_IAL_FLAG, +4) (AF0m.v:18-19) lies below the shadow. *)
Lemma fs_izone_low : forall a, DGgi.IZONE a -> 0 <= a < SHADOW_OFF.
Proof.
intros a Ha. unfold DGgi.IZONE, AF0m.TFIB_IAL_LO, AF0m.TFIB_IAL_HI, AF0m.TFIB_IAL_FLAG in Ha. unfold SHADOW_OFF. lia.
Qed.

(* HIAL: DGgi.IAL_POST reads TFIB_IAL_FLAG, +1, TFIB_IAL_W .. +16 and [TFIB_IAL_LO, TFIB_IAL_HI): DGgi.IZONE cells. *)
Lemma fs_ial_local : forall (W : world tfibsegs) (m1 m2 : word -> option byte),
  (forall x : word, DGgi.IZONE (bv_unsigned x) -> m1 x = m2 x) -> DGgi.IAL_POST W m1 -> DGgi.IAL_POST W m2.
Proof.
intros W m1 m2 E HP.
assert (A : forall a, 0 <= a < 2 ^ 64 -> DGgi.IZONE a ->
  mbyte tfibsegs (mrestrict (w_H W) m2) a = mbyte tfibsegs (mrestrict (w_H W) m1) a).
{ intros a Ra Ha. unfold mbyte, mrestrict. rewrite (E (Z_to_bv 64 a)); [reflexivity|].
  rewrite (FSupoisonARXm.wz64 a Ra). exact Ha. }
assert (VM : forall a (w : nat) v, (forall k, 0 <= k < Z.of_nat w -> 0 <= a + k < 2 ^ 64 /\ DGgi.IZONE (a + k)) ->
  val_mem tfibsegs (mrestrict (w_H W) m1) a w v -> val_mem tfibsegs (mrestrict (w_H W) m2) a w v).
{ intros a w v Hz V k Hk. destruct (Hz (Z.of_nat k) ltac:(lia)) as [R HZ]. rewrite (A _ R HZ). exact (V k Hk). }
unfold DGgi.IAL_POST in HP |- *. cbv zeta in HP |- *.
destruct HP as (V1 & V2 & V3 & V4 & V5).
unfold DGgi.IZONE in A, VM.
unfold AF0m.TFIB_IAL_LO, AF0m.TFIB_IAL_HI, AF0m.TFIB_IAL_W, AF0m.TFIB_IAL_FLAG in *.
refine (conj _ (conj _ (conj _ (conj _ _)))).
- apply VM; [intros k Hk; lia | exact V1].
- apply VM; [intros k Hk; lia | exact V2].
- apply VM; [intros k Hk; lia | exact V3].
- apply VM; [intros k Hk; lia | exact V4].
- intros a Ha. rewrite (A a ltac:(lia) ltac:(lia)). exact (V5 a Ha).
Qed.

(* ---- fs_arealloc_AU_closed at the relocated chain ---- *)

Theorem fs_arealloc_AU_at_cgif : forall B : asyms, TfibSyms B -> (forall t, as_dhash B t = YF0p.tfib_dhash t) ->
  PR.FS_AREALLOC_AU tfibsegs B (as_universe B).
Proof.
intros B TS HDH.
exact (@FSReallocAG.fs_arealloc_AU_closed fx rc AImg_cgif AGImg_cgif AImgS_cgif DImg_cgif
  (* H_prim_if H_missg H_missk H_sec H_dtop *)
  AGtopcgif.aalloc_prim_realizes_if AGim0.alloc_missg_cf AGin0.alloc_missk_cf AGio.alloc_sec
  DGtop.adealloc_realizes_raw_g
  (* dpostA mtagA stagA rtree dpostD dbody L24 QB DRq *)
  AGif1.dpost_cgif 3 12 refill_tree
  (CLdepot.dpost_x tfibsegs) AFeu.drain_body 16385 qloose DGif1.DRq_cgif
  (* H_if H_ifk H_ifm H_ifs H_dif *)
  AGif1.iface_cgif AGif1k.iface_cgif_k AGif1m.iface_cgif_m AGif5.ifaceS_cgif
  (fun B' TS' HD' => DGif1.diface_cgif B' TS' 16385 HD' (Z.le_refl 16385)
     (DGif1d.di_drain_cgif B' TS' 16385) (DGif1dI.di_requar_x_cgif B' TS' 16385)
     (DGif1dI.di_requar_r_cgif B' TS' 16385) (DGif1dI.di_requar_e_cgif B')
     (DGif1dI.di_rchunk_cgif B' TS') (DGif1dI.di_cdealloc_cgif B' TS'))
  (* B TS HDH H_refill_U H_difR_U *)
  B TS HDH (H_refill_U B TS) (H_difR_U B TS)
  (* HAI HAIk HAZ HIL HSHB HSZ HZ3 HWF HDI HDZ HIZ HIAL *)
  fs_inst_ok_low fs_inst_ok_TFIB (fs_zones_free_A B) FSReallocAG.fs_img_low_vals eq_refl (fs_zones_free_S B)
  FSReallocAG.fs_zone3_app FSupoisonARXmS.wframe_up_AGif0n fs_inst_ok_low (fs_zones_free_DG B) fs_izone_low
  fs_ial_local).
Qed.

(* ---- the corollary at fs's symbol table AD2l.TfibB ---- *)

Corollary fs_arealloc_AU_TfibB : PR.FS_AREALLOC_AU tfibsegs AD2l.TfibB (as_universe AD2l.TfibB).
Proof. exact (fs_arealloc_AU_at_cgif AD2l.TfibB AD2l.TfibB_syms (fun t => eq_refl)). Qed.

End a.
