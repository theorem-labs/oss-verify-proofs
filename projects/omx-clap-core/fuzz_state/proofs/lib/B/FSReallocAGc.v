(* fuzz_state image B: the CLOSING of lib/B/FSReallocAG.v's Section g at the B relocation of the allocator chain:
   lib/B/FSupoisonRealloc.FS_AREALLOC_BU, and the two premises of lib/B/FSRealloc_top.fs_arealloc_BU (Allocate in ARU
   form, raw Deallocate in ARU form), on no hypothesis of fuzz_state's own (a Theorem Labs lane, 2026-10-29).  The image-B twin
   of a Theorem Labs lane's lib/A/FSReallocAGc.v and a Theorem Labs lane's lib/A/FSReallocAGfin.v.

   rule 24: no function proved (kind: statement composition / instantiation glue)

   WHAT IS SUPPLIED, in FSReallocAG.v Section g's declaration order:
     IM0        AGif2cgif.AImg_cgif      (then IMA = img_at tfibsegs AImg_cgif = AImg_cgif by conversion)
     AG IMS DI  AGif0cgif.AGImg_cgif, AGif4cgif.AImgS_cgif, DGif0cgif.DImg_cgif
     H_prim_if  AGtopcgif.aalloc_prim_realizes_if   H_missg AGim0.alloc_missg_cf   H_missk AGin0.alloc_missk_cf
     H_sec      AGio.alloc_sec                      H_dtop  DGtop.adealloc_realizes_raw_g
     dpostA mtagA stagA rtree  AGif1.dpost_cgif, 3, 12 (labels 202260, 449860), YFl1.refill_tree (what the instances fix)
     dpostD dbody L24 QB DRq   CLdepot.dpost_x tfibsegs, YFeu.drain_body, 16385, qloose, DGif1dr.DRq_cgif
                (dpostD is DGif1.diface_cgif's dpost; fs_difR_U's CLenqcgifRaw.dpost_enq_cgif is its eta-expansion,
                CLenqcgifRaw.v:51-52, so the one value serves H_dtop, H_dif and H_difR_U by conversion)
     H_if AGif1.iface_cgif     H_ifk AGif1k.iface_cgif_k   H_ifm AGif1m.iface_cgif_m   H_ifs AGif5.ifaceS_cgif
     H_dif  DGif1.diface_cgif at L24 = 16385, its six drain-side premises discharged as DGtopcgifC.v:41-47 does
            ([fs_dif_cgif])
     B TS HDH   this file's Section variables (at YD2l.TfibBU: YD2l.TfibBU_syms, eq_refl, YD2l.v:34)
     H_refill_U H_difR_U   this file's Section hypotheses, in the texts of the conclusions of lib/B
                FSupoisonARXmRf.fs_refill_U (FSupoisonARXmRf.v:98-100) and of lib/B FSupoisonARXmDR.fs_difR_U at
                L24 = 16385; after the Section they are FSupoisonARXmRf.fs_refill_U_closed (a Theorem Labs lane) and
                FSupoisonARXmDRc.fs_difR_U_closed at 16385 (a Theorem Labs lane)
     the twelve image premises, each stated with Section g's text at the instances above:
       HAI / HDI  lib/A FSupoisonARX.inst_low_window 0xa1a98 0xa5c60 (AGif0cgif.inst_ok is that window)  [fs_HAI / fs_HDI]
       HAIk       AGif0cgif.inst_ok at TFIB_INST = 0xa4dd8 (lib/B/YF0m.v:14), by lia                  [fs_HAIk]
       HAZ / HDZ  lib/B FSupoisonARX.fs_zones_free at DZONE_shape 0x17a308 0x5caa90 (AGis / DGgi DZONE) and
                  CZONE_shape 0x10000 0x5fd000 0x7fff8000 0x800b3844 TFIB_TSD (AGif0cgif.CZONE)       [fs_HAZ / fs_HDZ]
       HIL        FSReallocAG.fs_img_low_vals (lib/B)
       HSHB       eq_refl: the B AImgS_cgif's AGjm.SHBv = 0x7fff8000 = SHADOW_OFF
       HSZ        FSReallocAG.fs_zones_free_CZS (lib/B) at AGjm.DZONE = DZONE_shape 0x17a308 0x5caa90    [fs_HSZ]
       HZ3        FSReallocAG.fs_zone3_app (lib/B)
       HWF        lib/A FSupoisonARXmS.wframe_up_AGif0n
       HIZ / HIAL the B DImg_cgif's IZONE / IAL_POST (DGgi.v:518 / :153, the text of YFgi.v:484 / :560) by their
                  literals: [TFIB_IAL_LO, TFIB_IAL_HI) and [TFIB_IAL_FLAG, +4) lie below the shadow, and IAL_POST
                  reads only IZONE cells                                                               [fs_HIZ / fs_HIAL]

   WHAT IT EXPORTS.  In the Section (the two ARU lifts as hypotheses): fs_arealloc_BU_at_cgif (FS_AREALLOC_BU, from
   FSReallocAG.fs_arealloc_BU_closed) and its two halves fs_aalloc_BU_at_cgif / fs_adealloc_raw_BU_at_cgif (from
   FSReallocAG.fs_aalloc_BU / fs_adealloc_raw_BU, FSReallocAG.v:296 / :325).  After it, with both lifts applied:
   fs_arealloc_BU_closed : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
   FS_AREALLOC_BU tfibsegs B (as_universe B), and at YD2l.TfibBU fs_arealloc_BU_closed_TfibBU, fs_aalloc_BU_TfibB and
   fs_adealloc_raw_BU_TfibB (the last two have the types lib/B/FSCloseB.v's FS_ALLOCATE_RAW_B / FS_DEALLOCATE_RAW_B
   take by `type of`; FSCloseB is not Required here, it imports this file).

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
YG00 YG0a YG01 YG04 YG03 YG06 YG0k YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG AllocGtop DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
ImgBase ImgBaseAG ImgBaseAGS ImgBaseDG AGif0n AGif2 AGif4 DMspec DMiface DGif0 DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YF0p CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonARX FSupoisonARXmA FSupoisonARXmS FSupoisonARXmD.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSReallocAGg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w YF0m FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
YF0x YFl0 YFl1 YFeu YD2l DGgi FSupoisonARX FSupoisonRealloc FSReallocAG.
(* the names in H_difR_U's text (fs_difR_U's): Deallocate's premise and DIfaceRcgif's dpost *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require DeallocGcgif CLenqcgifRaw.
(* the two ARU lifts, closed: a Theorem Labs lane's refill lift and a Theorem Labs lane's DIfaceR lift *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonARXmRf FSupoisonARXmDRc.
(* the B relocation's image instances (instance search fills AImg / AGImg / AImgS / DImg with them) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif AGif0cgif AGif4cgif DGif0cgif.
(* the closed forms of the c5 statements, relocated onto B *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
AGtopcgif AGim0 AGin0 AGio DGtop AGif1 AGif1k AGif1m AGif5 DGif1 DGif1d DGif1dI DGif1dr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonRealloc.
(* lib/B's FSReallocAG and FSupoisonARX and lib/A's FSupoisonARX, named by their full paths (same short names). *)
Module BAG := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSReallocAG.
Module BARX := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonARX.
Module AARX := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonARX.

(* Allocate's and Deallocate's entry pcs on B (YB1w.v:54, :52: 0x31f64, 0x31c50), as FSReallocAG.v names them. *)
Local Abbreviation pcA := tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb.
Local Abbreviation pcD := tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The image premises of Section g, each in Section g's text, at the B relocation's instances.                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section dis. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The band end of AGif0cgif.CZONE / AImgS_cgif.ims_csh_end is below the shadow of B's image end (0x800b7a00). *)
Lemma fs_csh_end : 0x800b3844 <= shadow_addr YF0x.TFIB_IMG_END.
Proof. unfold shadow_addr, SHADOW_OFF, YF0x.TFIB_IMG_END. assert (E : 6279168 / 8 = 784896) by reflexivity. rewrite E. lia. Qed.

(* HAI: AGif0cgif.inst_ok is inst_ok_window 0xa1a98 0xa5c60. *)
Lemma fs_HAI : inst_low ag_inst_ok.
Proof. exact (AARX.inst_low_window 0xa1a98 0xa5c60 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)). Qed.

(* HAIk: B's instance TFIB_INST = 0xa4dd8 lies in that window. *)
Lemma fs_HAIk : ag_inst_ok TFIB_INST.
Proof. change (AGif0cgif.inst_ok TFIB_INST). unfold AGif0cgif.inst_ok, TFIB_INST. split; [lia | split; [lia | reflexivity]]. Qed.

(* HAZ: AGis.DZONE and AGif0cgif.CZONE are the two shapes at B's literal bounds. *)
Lemma fs_HAZ : forall B : asyms, zones_free im_segs B ag_dzone ag_czone.
Proof.
intros B.
exact (BARX.fs_zones_free B 0x17a308 0x5caa90 0x10000 0x5fd000 0x7fff8000 0x800b3844
  ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) fs_csh_end).
Qed.

(* HSZ: lib/B FSReallocAG.fs_zones_free_CZS at AImgS_cgif (AGjm.DZONE is DZONE_shape 0x17a308 0x5caa90). *)
Lemma fs_HSZ : forall B : asyms, zones_free im_segs B ims_dzone (fun ly a => CZS ly TFIB_INST a).
Proof.
intros B.
apply (BAG.fs_zones_free_CZS AImg_cgif B 0x17a308 0x5caa90 TFIB_INST).
all: try (intros ly a Hz; exact Hz).
all: vm_compute; first [reflexivity | intro HH; discriminate HH].
Qed.

(* HDI: DImg_cgif's dg_inst_ok is AGif0cgif.inst_ok too. *)
Lemma fs_HDI : inst_low dg_inst_ok.
Proof. exact (AARX.inst_low_window 0xa1a98 0xa5c60 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)). Qed.

(* HDZ: DGgi.DZONE is the depot shape; the const zone minus IZONE lies in AGif0cgif.CZONE. *)
Lemma fs_HDZ : forall B : asyms, zones_free im_segs B dg_dzone (fun ly a => dg_czone ly a /\ ~ dg_izone a).
Proof.
intros B ly S W mem md a HAR Hz.
apply (BARX.fs_zones_free B 0x17a308 0x5caa90 0x10000 0x5fd000 0x7fff8000 0x800b3844
  ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) fs_csh_end
  ly S W mem md a HAR).
destruct Hz as [Hd | [Hc _]]; [left; exact Hd | right; exact Hc].
Qed.

(* HIZ: IZONE = [TFIB_IAL_LO, TFIB_IAL_HI) \/ [TFIB_IAL_FLAG, +4) (0xa9640, 0x12a670, 0x137ec8), below the shadow. *)
Lemma fs_HIZ : FSupoisonARXmD.izone_low.
Proof.
intros a Ha. change (DGgi.IZONE a) in Ha.
unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha. unfold SHADOW_OFF. lia.
Qed.

(* HIAL: IAL_POST reads TFIB_IAL_FLAG, +1, TFIB_IAL_W .. +16 and [TFIB_IAL_LO, TFIB_IAL_HI), all IZONE cells
   (the argument of DGgi.MEQI_frame, DGgi.v:608-615). *)
Lemma fs_HIAL : FSupoisonARXmD.ial_local.
Proof.
intros W m1 m2 HEQ HP. change (DGgi.IAL_POST W m2). change (DGgi.IAL_POST W m1) in HP.
assert (LOWEQ : forall a, DGgi.IZONE a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
{ intros a Ha. symmetry. apply HEQ. change (DGgi.IZONE (bv_unsigned (Z_to_bv 64 a))).
  rewrite unsigned_lit_small; [exact Ha|].
  unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha. lia. }
destruct HP as (I1 & I2 & I3 & I4 & I5). unfold DGgi.IAL_POST.
assert (V : forall a (n : nat) v, (forall k, (k < n)%nat -> DGgi.IZONE (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict (w_H W) m1) a n v -> val_mem tfibsegs (mrestrict (w_H W) m2) a n v).
{ intros a n v Hz Hv. apply (YF0x.val_mem_frame (w_H W) m1 m2 a n v); [|exact Hv].
  intros k Hk. apply LOWEQ, Hz, Hk. }
unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *.
split; [apply V; [intros k Hk; lia | exact I1]|]. split; [apply V; [intros k Hk; lia | exact I2]|].
split; [apply V; [intros k Hk; lia | exact I3]|]. split; [apply V; [intros k Hk; lia | exact I4]|].
intros a Ha. rewrite <- (I5 a Ha). apply YF0x.mbyte_mrestrict_same. apply LOWEQ; lia.
Qed.

(* H_dif: DGif1.diface_cgif at L24 = 16385, its six drain-side premises as DGtopcgifC.v:41-47 discharges them. *)
Definition fs_dif_cgif (B : asyms) (TS : TfibSyms B) (HD1 : YFl0.tfib_depot_spec B) :=
  DGif1.diface_cgif B TS 16385 HD1 (Z.le_refl 16385)
    (DGif1d.di_drain_cgif B TS 16385) (DGif1dI.di_requar_x_cgif B TS 16385)
    (DGif1dI.di_requar_r_cgif B TS 16385) (DGif1dI.di_requar_e_cgif B)
    (DGif1dI.di_rchunk_cgif B TS) (DGif1dI.di_cdealloc_cgif B TS).
End dis.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. FSReallocAG's three theorems at the B relocation, from the two ARU callee lifts as hypotheses.                *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.

(* Section g's H_refill_U at rtree := YFl1.refill_tree, in the text of lib/B FSupoisonARXmRf.fs_refill_U's conclusion
   (FSupoisonARXmRf.v:98-100 at 432a2933d97; PENDING a Theorem Labs lane). *)
Hypothesis H_refill_U : forall Up,
  FSupoisonARXmA.if_refill_t B (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreA qtight YFl1.refill_tree.
(* Section g's H_difR_U at dbody := YFeu.drain_body, L24 := 16385, QB := qloose, DRq := DGif1dr.DRq_cgif, in the text of
   lib/B FSupoisonARXmDR.fs_difR_U's conclusion at L24 = 16385 (b42f82b55c7; PENDING a Theorem Labs lane): its UA B, FS_rpreD,
   fpreU im_segs and dpostD := CLdepot.dpost_x tfibsegs are, by conversion, the lambda, rpre_dealloc_cgif, fpreU tfibsegs
   and CLenqcgifRaw.dpost_enq_cgif written here. *)
Hypothesis H_difR_U : forall Up,
  DIfaceR B (fun tr S => tr_admit (as_universe B) S tr) (ARX_ARU tfibsegs B TFIB_INST Up) (ARX_ARU tfibsegs B TFIB_INST Up)
    (aowned B) DeallocGcgif.rpre_dealloc_cgif qtight (fpreU tfibsegs B Up) (CLenqcgifRaw.dpost_enq_cgif B)
    YFeu.drain_body 16385 qloose (DGif1dr.DRq_cgif B).

Theorem fs_arealloc_BU_at_cgif : PR.FS_AREALLOC_BU tfibsegs B (as_universe B).
Proof.
exact (@BAG.fs_arealloc_BU_closed fx rc AImg_cgif AGImg_cgif AImgS_cgif DImg_cgif
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFK TSB cf HCF MG MK =>
     AGtopcgif.aalloc_prim_realizes_if B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFK TSB cf HCF MG MK)
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM =>
     AGim0.alloc_missg_cf B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM)
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM =>
     AGin0.alloc_missk_cf B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM)
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS TSB Hn cf HCF =>
     AGio.alloc_sec B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS TSB Hn cf HCF)
  (fun B TSB U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF IR =>
     DGtop.adealloc_realizes_raw_g B TSB U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF IR)
  (fun B => AGif1.dpost_cgif B) 3 12 YFl1.refill_tree
  (fun B => CLdepot.dpost_x tfibsegs B) YFeu.drain_body 16385 qloose (fun B => DGif1dr.DRq_cgif B)
  (fun B TSB HDB => AGif1.iface_cgif B TSB HDB)
  (fun B TSB HDB => AGif1k.iface_cgif_k B TSB HDB)
  (fun B TSB HDB => AGif1m.iface_cgif_m B TSB HDB)
  (fun B cf TSB HDB => AGif5.ifaceS_cgif B cf TSB HDB)
  (fun B TSB HDB => fs_dif_cgif B TSB HDB)
  B TS HDH H_refill_U H_difR_U
  fs_HAI fs_HAIk (fs_HAZ B) BAG.fs_img_low_vals eq_refl (fs_HSZ B) BAG.fs_zone3_app
  FSupoisonARXmS.wframe_up_AGif0n fs_HDI (fs_HDZ B) fs_HIZ fs_HIAL).
Qed.

(* Its Allocate half: FSReallocAG.fs_aalloc_BU (FSReallocAG.v:296), the same arguments. *)
Theorem fs_aalloc_BU_at_cgif : forall Up,
  aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    pcA TFIB_OOM 8 1 1.
Proof.
exact (BAG.fs_aalloc_BU AImg_cgif
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFK TSB cf HCF MG MK =>
     AGtopcgif.aalloc_prim_realizes_if B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFK TSB cf HCF MG MK)
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM =>
     AGim0.alloc_missg_cf B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM)
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM =>
     AGin0.alloc_missk_cf B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TSB rtree IFM)
  (fun B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS TSB Hn cf HCF =>
     AGio.alloc_sec B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS TSB Hn cf HCF)
  (fun B => AGif1.dpost_cgif B) 3 12 YFl1.refill_tree
  (fun B TSB HDB => AGif1.iface_cgif B TSB HDB)
  (fun B TSB HDB => AGif1k.iface_cgif_k B TSB HDB)
  (fun B TSB HDB => AGif1m.iface_cgif_m B TSB HDB)
  (fun B cf TSB HDB => AGif5.ifaceS_cgif B cf TSB HDB)
  B TS HDH H_refill_U
  fs_HAI fs_HAIk (fs_HAZ B) BAG.fs_img_low_vals eq_refl (fs_HSZ B) BAG.fs_zone3_app
  FSupoisonARXmS.wframe_up_AGif0n).
Qed.

(* Its raw Deallocate half: FSReallocAG.fs_adealloc_raw_BU (FSReallocAG.v:325), the same arguments. *)
Theorem fs_adealloc_raw_BU_at_cgif : forall Up,
  adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight (FS_fpre B Up) pcD 1.
Proof.
exact (BAG.fs_adealloc_raw_BU AImg_cgif
  (fun B TSB U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF IR =>
     DGtop.adealloc_realizes_raw_g B TSB U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF IR)
  (fun B => CLdepot.dpost_x tfibsegs B) YFeu.drain_body 16385 qloose (fun B => DGif1dr.DRq_cgif B)
  (fun B TSB HDB => fs_dif_cgif B TSB HDB)
  B TS HDH H_difR_U
  fs_HDI (fs_HDZ B) fs_HIZ fs_HIAL).
Qed.
End a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Both lifts applied: FS_AREALLOC_BU on TS and HDH alone, and at lib/B/YD2l.TfibBU (TfibSyms is                 *)
(*    YD2l.TfibBU_syms, as_dhash is tfib_dhash by eq_refl, YD2l.v:34).                                             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Theorem fs_arealloc_BU_closed {fx : YK11.FPState} {rc : YM05.RunCeil} : forall B, TfibSyms B ->
  (forall t, as_dhash B t = YF0p.tfib_dhash t) -> PR.FS_AREALLOC_BU tfibsegs B (as_universe B).
Proof.
intros B TS HDH.
exact (fs_arealloc_BU_at_cgif B TS HDH (fun Up => FSupoisonARXmRf.fs_refill_U_closed B TS Up)
  (fun Up => FSupoisonARXmDRc.fs_difR_U_closed B TS 16385 (Z.le_refl 16385) Up)).
Qed.

Corollary fs_arealloc_BU_closed_TfibBU {fx : YK11.FPState} {rc : YM05.RunCeil} :
  PR.FS_AREALLOC_BU tfibsegs YD2l.TfibBU (as_universe YD2l.TfibBU).
Proof. exact (fs_arealloc_BU_closed YD2l.TfibBU YD2l.TfibBU_syms (fun t => eq_refl)). Qed.

(* lib/B/FSCloseB.v's FS_ALLOCATE_RAW_B: the first premise of FSRealloc_top.fs_arealloc_BU at TfibBU. *)
Theorem fs_aalloc_BU_TfibB {fx : YK11.FPState} {rc : YM05.RunCeil} : forall Up,
  aalloc_realizes tfibsegs YD2l.TfibBU (FS_U YD2l.TfibBU) YG00.malloc (FS_ARX YD2l.TfibBU Up) (aowned YD2l.TfibBU)
    FS_rpreA MALLOC_MAX LIVE_MAX qtight pcA TFIB_OOM 8 1 1.
Proof.
exact (fs_aalloc_BU_at_cgif YD2l.TfibBU YD2l.TfibBU_syms (fun t => eq_refl)
  (fun Up => FSupoisonARXmRf.fs_refill_U_closed YD2l.TfibBU YD2l.TfibBU_syms Up)).
Qed.

(* lib/B/FSCloseB.v's FS_DEALLOCATE_RAW_B: the second premise of FSRealloc_top.fs_arealloc_BU at TfibBU. *)
Theorem fs_adealloc_raw_BU_TfibB {fx : YK11.FPState} {rc : YM05.RunCeil} : forall Up,
  adealloc_realizes_raw tfibsegs YD2l.TfibBU (FS_U YD2l.TfibBU) YG00.free (FS_ARX YD2l.TfibBU Up)
    (aowned YD2l.TfibBU) FS_rpreD qtight (FS_fpre YD2l.TfibBU Up) pcD 1.
Proof.
exact (fs_adealloc_raw_BU_at_cgif YD2l.TfibBU YD2l.TfibBU_syms (fun t => eq_refl)
  (fun Up => FSupoisonARXmDRc.fs_difR_U_closed YD2l.TfibBU YD2l.TfibBU_syms 16385 (Z.le_refl 16385) Up)).
Qed.
