(* fuzz_state image A: the ARU-form Allocate / Deallocate contracts that lib/A/FSRealloc_top.fs_arealloc_AU takes, from
   the relocated frozen allocator chain, by instantiation glue (a Theorem Labs lane, 2026-10-29).

   rule 24: no function proved (kind: statement composition / instantiation glue).

   WHAT THIS FILE IS.  fs_arealloc_AU (lib/A/FSRealloc_top.v:137) closes FSupoisonRealloc.FS_AREALLOC_AU from two premises:
     (T1_U) forall Up, aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX
                         LIVE_MAX qtight <Allocate 0x31ef4> TFIB_OOM 8 1 1
     (T2_U) forall Up, adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight
                         (FS_fpre B Up) <Deallocate 0x31be0> 1.
   Here they are proved ([fs_aalloc_AU], [fs_adealloc_raw_AU]) and fs_arealloc_AU is applied ([fs_arealloc_AU_closed]),
   from NAMED HYPOTHESES that are exactly what a Theorem Labs lane's relocation of a Theorem Labs lane's frozen chain onto image A delivers
   (a working branch; c5 = a working branch ced28ed2383), plus the record transfers of
   lib/A/FSupoisonARXm{A,S,D}.v.  When the relocation builds, each hypothesis is closed by the relocated theorem named
   beside it (by conversion: the pcs are AB1w's symbols, the instance names AllocGcgif.ARX_cgif / rpre_cgif /
   DeallocGcgif.rpre_dealloc_cgif / fpre_cgif unfold to ARX_AR / FS_rpreA / FS_rpreD / (fun _ _ _ _ _ _ => True)).

   THE IMAGE CLASSES.  The records are stated over the classes ImgBase.AImg / ImgBaseAG.AGImg / ImgBaseAGS.AImgS /
   ImgBaseDG.DImg.  Their image-A instances are the relocation's (AGif2cgif.AImg_cgif, AGif0cgif.AGImg_cgif,
   AGif4cgif.AImgS_cgif, DGif0cgif.DImg_cgif), not yet built, so they are variables here.  Only the AImg instance's
   segment list must be image A's, definitionally (the walks' tops are over [tfibsegs], the records over [im_segs]): the
   instance is [img_at tfibsegs IM0] (lib/A/FSReallocAGg.v), whose segments are AB1v.tfibsegs and whose other fields
   are IM0's; at IM0 := AImg_cgif it is AImg_cgif by conversion (AImg_cgif := {| im_segs := tfibsegs; .. |}).

   HYPOTHESES (each with the c5 statement it is the closed form of; in the relocation the same file name in lib/A):
     (H1a) H_prim_if   AGtopcgif.aalloc_prim_realizes_if   AGtopcgif.v:28-58 (Section c: B U mt ARX AOX rpre nmax lmax
                       lpost dpost mtag stag IF IFK TS cf HCF ARM_MISSGi ARM_MISSKi), pc 0x31ef4 on A
     (H1b) H_missg     AGim0.alloc_missg_cf                AGim0.v:87-102 (Section b: .. IF TS rtree IFM), :500-503
     (H1c) H_missk     AGin0.alloc_missk_cf                AGin0.v:50-65, :421-424
     (H1d) H_sec       AGio.alloc_sec                      AGio.v:50-75 (Section f: .. IF IFS TS Hnmax cf Hcfv), :71-75
     (H2)  H_dtop      DGtop.adealloc_realizes_raw_g       DGtop.v:37-52 (Section b: B TS U ft ARX ARXr AOX rpre lpost
                       fpre dpost dbody L24 QB DRq IF), :103-105 (IR), pc 0x31be0 on A
     (H3a) H_if        AGif1.iface_cgif                    AGif1.v:245-246
     (H3k) H_ifk       AGif1k.iface_cgif_k                 AGif1k.v:162-163
     (H3m) H_ifm       AGif1m.iface_cgif_m                 AGif1m.v:496-498
     (H3s) H_ifs       AGif5.ifaceS_cgif                   AGif5.v:1147-1149
     (H3d) H_dif       DGif1.diface_cgif with its six drain-side premises discharged as DGtopcgifC.v:31-41 does
                       (DGif1d.di_drain_cgif, DGif1dI.di_requar_x/r/e_cgif, di_rchunk_cgif, di_cdealloc_cgif)
                       DGif1.v:2286-2288
       H3* are stated at U := [UA B] = tr_admit (as_universe B): the relocation's C5 port of the instances (a Theorem Labs lane,
       12:13Z); the record parameters the instances fix (dpost_cgif, 3 / 12 (labels 202260 / 449860), refill_tree, CLdepot.dpost_x,
       drain_body, 16385, qloose, DRq_cgif) are the variables dpostA, mtagA, stagA, rtree, dpostD, dbody, L24, QB, DRq.
     (H4r) H_refill_U  if_refill at ARX_ARU (FSupoisonARXmA.if_refill_t): the ARU twin of AGif1m.refill_cgif
                       (AGif1m.v:157), from a Theorem Labs lane's FSupoisonAllocRt.tfib_refill_okU
     (H4d) H_difR_U    DIfaceR at ARX_ARU: the ARU twin of DIfaceRcgif.diface_r_cgif (DIfaceRcgif.v:38-42), from
                       a Theorem Labs lane's FSupoisonAllocFeq.tfib_enqueue_nbU (dr_enqueue), FSupoisonAllocFdn / Fdr (dr_drain),
                       FSupoisonAllocFrs / Fcd (dr_rchunk, dr_cdealloc).  DIface's four callee fields at ARU are its
                       aview weakenings ([enq_of_R], [drain_of_R], [rchunk_of_R], [cdealloc_of_R]).
     TS (TfibSyms B) and HDH (forall t, as_dhash B t = tfib_dhash t): a Theorem Labs lane's top premises, carried unchanged;
     tfib_depot_spec B, which H3* take, is AFem.tfib_depot_ok B TS HDH (S0).
   IMAGE PREMISES of the transfers (each discharged at the relocation's instances; FSupoisonARXm{A,S,D}.v headers):
     HAI  inst_low ag_inst_ok            FSupoisonARX.inst_low_window lo hi (AGif0cgif.inst_ok's window)
     HAIk ag_inst_ok TFIB_INST           AGif0cgif.inst_ok TFIB_INST (0xa48d8 in the window; lia)
     HAZ  zones_free .. ag_dzone ag_czone FSupoisonARX.fs_zones_free (AGis.DZONE, AGif0cgif.CZONE literal bounds)
     HIL  img_low                        [fs_img_low_vals]: TFIB_OOM 0x12a1a0, TFIB_ERRNO 0x5dae8c (AF0m.v:19, :21)
     HSHB ims_shb = SHADOW_OFF           AGif4cgif.AImgS_cgif.ims_shb := AGjm.SHBv = 0x7fff8000
     HSZ  zones_free .. ims_dzone (CZS ly TFIB_INST)   [fs_zones_free_CZS] at AImgS_cgif's dzone / image-end /
                                         shadow-window literals (FSupoisonARXmS.zones_free_CZS at A's image end)
     HZ3  zone3_app                      [fs_zone3_app] at ims_zone3 := AF0x.zone3
     HWF  wframe_up ims_wframe           FSupoisonARXmS.wframe_up_AGif0n (ims_wframe := AGif0cgif.wframe =
                                         AGif0n.wframe by conversion)
     HDI  inst_low dg_inst_ok            as HAI (DImg_cgif.dg_inst_ok := AGif0cgif.inst_ok)
     HDZ  zones_free .. dg_dzone (dg_czone \ dg_izone)   FSupoisonARX.fs_zones_free (monotone in the CZONE argument)
     HIZ  izone_low, HIAL ial_local      DImg_cgif's IZONE / IAL_POST literals (below SHADOW_OFF; IAL_POST reads only
                                         IZONE cells)
   The record parameters inst_low (fun i => i = TFIB_INST) and nmax <= MALLOC_MAX are proved here (fs_inst_low,
   Z.le_refl).

   The image-free glue is lib/A/FSReallocAGg.v (shared with lib/B/FSReallocAG.v): the U bridge (the records sit at
   tr_admit (as_universe B), fs_arealloc_AU's premises at FS_U B; alloc_pre / dealloc_pre carry 1 <= length tr <= 30),
   the prim + sec split of aalloc_realizes, DIface's callee fields from DIfaceR, img_at.

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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonARXmA FSupoisonARXmS FSupoisonARXmD.
(* the image-free glue: the U bridge, the prim + sec split, DIface's callee fields from DIfaceR, img_at *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSReallocAGg.
(* fs's image A: segments, symbols, instance constants; the instance values and the composed realloc contract *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w AF0m FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x AFl0 AFem FSupoisonARX FSupoisonRealloc FSRealloc_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module PR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonRealloc.

(* Allocate's and Deallocate's entry pcs on A (AB1w.v:54, :52: 0x31ef4, 0x31be0). *)
Local Abbreviation pcA := tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb.
Local Abbreviation pcD := tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Image-A discharges of three transfer premises, from S0 facts.                                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section dis. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* img_low at A's data cells (AF0m.v:19, :21): img_low at the relocation's AImg_cgif unfolds to this. *)
Lemma fs_img_low_vals : 0 <= TFIB_OOM < SHADOW_OFF /\ 0 <= TFIB_ERRNO /\ TFIB_ERRNO + 4 <= SHADOW_OFF.
Proof. unfold TFIB_OOM, TFIB_ERRNO, SHADOW_OFF. lia. Qed.

(* zone3_app at the relocation's AImgS_cgif (ims_zone3 := AF0x.zone3) unfolds to this. *)
Lemma fs_zone3_app : forall x sz, AF0x.zone3 x sz ->
  4096 <= x /\ x + sz <= ASAN_CEIL /\ (x + sz <= kLowShadowBeg \/ kHighMemBeg <= x).
Proof.
intros x sz (Z1 & Z2 & ZC). split; [exact Z1|]. split; [exact Z2|].
unfold AF0x.zone3cases, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, kLowShadowBeg in ZC.
unfold kLowShadowBeg. destruct ZC as [C|[C|C]]; lia.
Qed.
End dis.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The image instance, the hypotheses, and the two contracts.                                                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable IM0 : AImg.
(* The AImg instance with image A's segments (FSReallocAGg.img_at); at IM0 := the relocation's AImg_cgif it is AImg_cgif
   by conversion. *)
#[local] Instance IMA : AImg := img_at tfibsegs IM0.
Context {AG : AGImg} {IMS : AImgS} {DI : DImg}.

(* ---- (H1) the generic Allocate pieces, as the relocation closes them (c5 statements; see the header) ---- *)

(* AGtopcgif.aalloc_prim_realizes_if (c5 AGtopcgif.v:28-58) *)
Hypothesis H_prim_if : forall (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
  (ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
  (AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
  (dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z),
  AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag ->
  AIfaceK B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag ->
  TfibSyms B -> forall cf : Z, cf = 0 \/ cf = 1 ->
  (forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
     alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr -> 49 <= n <= 64512 ->
     pc_chunks (cache S (chunk_class n)) = [] ->
     amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs pcA regs mem md)
       (alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr)) ->
  (forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
     alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr -> 0 <= n <= 48 ->
     pc_chunks (cache S (chunk_class n)) = [] ->
     amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs pcA regs mem md)
       (alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr)) ->
  aalloc_prim_realizes tfibsegs B U mt ARX AOX rpre nmax lmax lpost pcA TFIB_OOM 8 1 cf.

(* AGim0.alloc_missg_cf (c5 AGim0.v:87-102, :500-503) *)
Hypothesis H_missg : forall (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
  (ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
  (AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
  (dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z),
  AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag -> TfibSyms B ->
  forall rtree : Z -> M unit, AIfaceM B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree ->
  forall cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
  49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
  amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs pcA regs mem md)
    (alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).

(* AGin0.alloc_missk_cf (c5 AGin0.v:50-65, :421-424) *)
Hypothesis H_missk : forall (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
  (ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
  (AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
  (dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z),
  AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag -> TfibSyms B ->
  forall rtree : Z -> M unit, AIfaceM B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree ->
  forall cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
  0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
  amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs pcA regs mem md)
    (alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).

(* AGio.alloc_sec (c5 AGio.v:50-75) *)
Hypothesis H_sec : forall (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
  (ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
  (AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
  (dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z),
  AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag ->
  AIfaceS B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag ->
  TfibSyms B -> nmax <= MALLOC_MAX -> forall cf : Z, cf = 0 \/ cf = 1 ->
  forall inst so bp ly S W regs mem md n tr,
  alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr -> 64513 <= n ->
  amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs pcA regs mem md)
    (alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).

(* ---- (H2) the generic raw Deallocate top ---- *)

(* DGtop.adealloc_realizes_raw_g (c5 DGtop.v:37-52, :103-105) *)
Hypothesis H_dtop : forall B : asyms, TfibSyms B ->
  forall (U : list Z -> astate -> Prop) (ft : sptr -> list Z -> M unit)
  (ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
  (AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (lpost : astate -> Prop)
  (fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop)
  (dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop)
  (dbody : astate -> M unit) (L24 : Z) (QB : astate -> Prop) (DRq : astate -> list chunk -> list Z -> Prop),
  DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq ->
  DIfaceR B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq ->
  adealloc_realizes_raw tfibsegs B U ft ARX AOX rpre lpost fpre pcD 1.

(* ---- (H3) the AR-form instance records at fs ---- *)

(* The record parameters the instances fix (c5: dpost_cgif B, 3, 12 (labels 202260, 449860), refill_tree; CLdepot.dpost_x tfibsegs B,
   drain_body, 16385, qloose, DRq_cgif B). *)
Variable dpostA : asyms -> Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtagA stagA : Z).
Variable rtree : Z -> M unit.
Variable dpostD : asyms -> Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : asyms -> astate -> list chunk -> list Z -> Prop.

(* AGif1.iface_cgif (c5 AGif1.v:245-246), over the F1 form of hview.hv_v (16 * v + 2 ^ 16 <= 2 ^ 32; a Theorem Labs lane's
   working branch 86aa4177b94, installs in c5 ~18:30Z), which holds at fs's EV_MAX 11776 (FS-INSTANCE.md 2.1).
   Its fs proof also takes fs's local AGiy / AGjc off_facts / v_facts edit (FS-INSTANCE.md 1.1). *)
Hypothesis H_if : forall B : asyms, TfibSyms B -> AFl0.tfib_depot_spec B ->
  AIface B (UA B) YG00.malloc (ARX_AR im_segs B TFIB_INST) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    (dpostA B) mtagA stagA.
(* AGif1k.iface_cgif_k (c5 AGif1k.v:162-163) *)
Hypothesis H_ifk : forall B : asyms, TfibSyms B -> AFl0.tfib_depot_spec B ->
  AIfaceK B (UA B) YG00.malloc (ARX_AR im_segs B TFIB_INST) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    (dpostA B) mtagA stagA.
(* AGif1m.iface_cgif_m (c5 AGif1m.v:496-498), over the same F1 hview.hv_v (see H_if). *)
Hypothesis H_ifm : forall B : asyms, TfibSyms B -> AFl0.tfib_depot_spec B ->
  AIfaceM B (UA B) YG00.malloc (ARX_AR im_segs B TFIB_INST) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    (dpostA B) mtagA stagA rtree.
(* AGif5.ifaceS_cgif (c5 AGif5.v:1147-1149; its can_fill argument is unused) *)
Hypothesis H_ifs : forall (B : asyms) (cf : Z), TfibSyms B -> AFl0.tfib_depot_spec B ->
  AIfaceS B (UA B) YG00.malloc (ARX_AR im_segs B TFIB_INST) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    (dpostA B) mtagA stagA.
(* DGif1.diface_cgif (c5 DGif1.v:2286-2288) at L24, its drain-side premises discharged as DGtopcgifC.v:31-41; over the
   F2 form of DMiface.di_rview_t (the rg_alloc_user (reg X kBatchClass) <= 2 ^ 31 conjunct dropped, 86aa4177b94).  Its
   fs proof also takes fs's local DGif1 dgo_bgeom edit (FS-INSTANCE.md 1.1). *)
Hypothesis H_dif : forall B : asyms, TfibSyms B -> AFl0.tfib_depot_spec B ->
  DIface B (UA B) YG00.free (ARX_AR im_segs B TFIB_INST) (ARX_AR im_segs B TFIB_INST) (aowned B) FS_rpreD qtight
    (fun _ _ _ _ _ _ => True) (dpostD B) dbody L24 QB (DRq B).

(* ---- the fs instance: B and a Theorem Labs lane's top premises ---- *)

Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.

(* The discharge of HSZ below at the relocation's AImgS_cgif: FSupoisonARXmS.zones_free_CZS at A's image end (the
   ledger fact FSupoisonARX.fs_img_end, TFIB_IMG_END = 0x5fd000), the depot zone by FSupoisonARX.fs_zones_free. *)
Lemma fs_zones_free_CZS : forall dlo dhi I,
  (forall ly a, ims_dzone ly a -> FSupoisonARX.DZONE_shape dlo dhi ly a) -> 0 <= dlo -> dhi <= SHADOW_OFF ->
  0 <= I -> I + 0xe60 <= SHADOW_OFF -> ims_img_end <= SHADOW_OFF -> 0 <= ims_shb ->
  ims_csh_end <= shadow_addr AF0x.TFIB_IMG_END -> 0 <= im_tsd -> im_tsd + 8 <= SHADOW_OFF ->
  zones_free im_segs B ims_dzone (fun ly a => CZS ly I a).
Proof.
intros dlo dhi I HDZ Hd0 Hd1 HI0 HI1 HIE HS0 HS1 HT0 HT1.
apply (FSupoisonARXmS.zones_free_CZS (IM := IMA) B AF0x.TFIB_IMG_END I); try assumption;
  [exact (FSupoisonARX.fs_img_end B)|].
intros ly S W mem md a HAR Ha.
assert (Z0 : 0 <= shadow_addr AF0x.TFIB_IMG_END).
{ unfold shadow_addr, SHADOW_OFF, AF0x.TFIB_IMG_END. assert (E : 6279168 / 8 = 784896) by reflexivity. rewrite E. lia. }
exact (FSupoisonARX.fs_zones_free B dlo dhi 0 0 0 0 Hd0 Hd1 ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) Z0
  ly S W mem md a HAR (or_introl (HDZ ly a Ha))).
Qed.

(* ---- (H4) the ARU callee fields, from a Theorem Labs lane's ARU twins ---- *)

(* if_refill at ARU (the ARU twin of AGif1m.refill_cgif, c5 AGif1m.v:157): FSupoisonAllocRt.tfib_refill_okU *)
Hypothesis H_refill_U : forall Up,
  FSupoisonARXmA.if_refill_t B (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreA qtight rtree.
(* DIfaceR at ARU (the ARU twin of DIfaceRcgif.diface_r_cgif, c5 DIfaceRcgif.v:38-42) *)
Hypothesis H_difR_U : forall Up,
  DIfaceR B (UA B) (ARX_ARU im_segs B TFIB_INST Up) (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreD qtight
    (fpreU im_segs B Up) (dpostD B) dbody L24 QB (DRq B).

(* ---- the image premises of the transfers (discharges in the header) ---- *)

Hypothesis HAI : inst_low ag_inst_ok.
Hypothesis HAIk : ag_inst_ok TFIB_INST.
Hypothesis HAZ : zones_free im_segs B ag_dzone ag_czone.
Hypothesis HIL : img_low.
Hypothesis HSHB : ims_shb = SHADOW_OFF.
Hypothesis HSZ : zones_free im_segs B ims_dzone (fun ly a => CZS ly TFIB_INST a).
Hypothesis HZ3 : FSupoisonARXmS.zone3_app.
Hypothesis HWF : FSupoisonARXmS.wframe_up ims_wframe.
Hypothesis HDI : inst_low dg_inst_ok.
Hypothesis HDZ : zones_free im_segs B dg_dzone (fun ly a => dg_czone ly a /\ ~ dg_izone a).
Hypothesis HIZ : FSupoisonARXmD.izone_low.
Hypothesis HIAL : FSupoisonARXmD.ial_local.

(* ---- T1_U ---- *)

Theorem fs_aalloc_AU : forall Up,
  aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    pcA TFIB_OOM 8 1 1.
Proof.
intros Up.
pose proof (AFem.tfib_depot_ok B TS HDH) as HD1.
pose proof (FSupoisonARXmA.aiface_U B (UA B) YG00.malloc FS_rpreA MALLOC_MAX LIVE_MAX qtight (dpostA B) mtagA stagA
  TFIB_INST Up HAI HAZ (H_if B TS HD1)) as IF.
pose proof (FSupoisonARXmA.aifaceK_U B (UA B) YG00.malloc FS_rpreA MALLOC_MAX LIVE_MAX qtight (dpostA B) mtagA stagA
  TFIB_INST Up HAI HAZ (H_if B TS HD1) (H_ifk B TS HD1)) as IFK.
pose proof (FSupoisonARXmA.ifaceM_U B (UA B) YG00.malloc FS_rpreA MALLOC_MAX LIVE_MAX qtight (dpostA B) mtagA stagA
  rtree TFIB_INST Up HAI HAZ HIL HAIk (H_ifm B TS HD1) (H_refill_U Up)) as IFM.
pose proof (FSupoisonARXmS.ifaceS_U B (UA B) YG00.malloc FS_rpreA MALLOC_MAX LIVE_MAX qtight (dpostA B) mtagA stagA
  TFIB_INST Up FSupoisonARX.fs_inst_low HSHB HSZ HIL HZ3 HWF (Z.le_refl _) (H_ifs B 1 TS HD1)) as IFS.
apply (aalloc_realizes_U tfibsegs B (UA B) (FS_U B) YG00.malloc (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B)
  FS_rpreA MALLOC_MAX LIVE_MAX qtight pcA TFIB_OOM 8 1 1 (FS_U_UA B)).
apply aalloc_realizes_of_prim_sec.
- exact (H_prim_if B (UA B) YG00.malloc (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    (dpostA B) mtagA stagA IF IFK TS 1 (or_intror eq_refl)
    (H_missg B (UA B) YG00.malloc (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
       (dpostA B) mtagA stagA IF TS rtree IFM 1)
    (H_missk B (UA B) YG00.malloc (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
       (dpostA B) mtagA stagA IF TS rtree IFM 1)).
- exact (H_sec B (UA B) YG00.malloc (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    (dpostA B) mtagA stagA IF IFS TS (Z.le_refl _) 1 (or_intror eq_refl)).
Qed.

(* ---- T2_U ---- *)

Theorem fs_adealloc_raw_AU : forall Up,
  adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight (FS_fpre B Up) pcD 1.
Proof.
intros Up.
pose proof (AFem.tfib_depot_ok B TS HDH) as HD1.
pose proof (H_difR_U Up) as IR.
pose proof (FSupoisonARXmD.diface_U B (UA B) YG00.free FS_rpreD qtight (dpostD B) dbody L24 QB (DRq B) TFIB_INST Up
  HDI HDZ HIZ HIAL (H_dif B TS HD1)
  (enq_of_R _ _ _ _ _ _ _ _ _ _ _ _ _ IR) (drain_of_R _ _ _ _ _ _ _ _ _ _ _ _ _ IR)
  (rchunk_of_R _ _ _ _ _ _ _ _ _ _ _ _ _ IR) (cdealloc_of_R _ _ _ _ _ _ _ _ _ _ _ _ _ IR)) as IF.
apply (adealloc_realizes_raw_U tfibsegs B (UA B) (FS_U B) YG00.free (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B)
  FS_rpreD qtight (fpreU tfibsegs B Up) pcD 1 (FS_U_UA B)).
exact (H_dtop B TS (UA B) YG00.free (ARX_ARU tfibsegs B TFIB_INST Up) (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B)
  FS_rpreD qtight (fpreU tfibsegs B Up) (dpostD B) dbody L24 QB (DRq B) IF IR).
Qed.

(* ---- the composed realloc contract in ARU form ---- *)

Theorem fs_arealloc_AU_closed : PR.FS_AREALLOC_AU tfibsegs B (as_universe B).
Proof. exact (FSRealloc_top.fs_arealloc_AU B TS fs_aalloc_AU fs_adealloc_raw_AU). Qed.

End g.
