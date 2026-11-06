(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the Deallocate half of the SEAM between a unit's relocated
   walk and the generic cf instance layer.  rule 24: no function proved (kind: record of a unit's walk tops).

   The layer is generic over CfImg / CfParams, the image classes ImgBase.AImg / ImgBaseDG.DImg and the opaque
   allocator relation ARX; a unit's walk is not, because each arm is a machine run that decodes that unit's own
   bytes out of [im_segs].  So each unit supplies its Deallocate walk's tops, and [WalkSigD] is exactly what the
   layer's Deallocate top (YGcfInstFreeTop.v) consumes.  It is the twin of YGcfInstWalkSig.WalkSigA (the Allocate
   half, lane M), at the same segments [im_segs] so that the two halves share ONE allocator relation.

   The field texts are a Theorem Labs lane's Deallocate walk tops (a working branch a12639a2201, the statements
   at proofs/omx-clap-core/fuzz_preset/lib/A/MemnormD*.v listed below), which are a Theorem Labs lane's memnorm arm twins (a working branch
   29b7505aa27, installed in c5 at 30a1993588f) relocated to the unit's image, with [tfibsegs] replaced by [im_segs],
   the Deallocate entry pc (cgif's and preset's own values) by CfImg's [cf_pc_deallocate], and the call
   site's alloc_type argument (1 in every walk) by the section variable [atpD]:
   - wsd_null    A/MemnormDnull.v:197    dealloc_null_arm_em  (c5 30a1993588f MemnormDnull.v:190)
   - wsd_common  A/MemnormDcommon.v:119  dealloc_common_em    (MemnormDcommon.v:111)
   - wsd_mid     A/MemnormDmid.v:154     dealloc_mid_em       (MemnormDmid.v:148)
   - wsd_drn     A/MemnormDmid.v:217     dealloc_drn_em       (MemnormDmid.v:204)
   These are the four arms MemnormDtop.adealloc_realizes_raw_em_g (MemnormDtop.v:72-101) splits over, on the
   enqueue side of free_cf's size test (rpre := the layer's rpreD_small_cf).  The fifth field, wsd_big, is the
   unit's big-block arm on the recycle side (rpreB := the layer's rpreD_big_cf), relocated from c5's DGbig.dealloc_big_em
   (a working branch d501b72dd83, DeallocNmaxA): its walk top ends in MemnormT.dealloc_leaf_raw_em after Put's size
   test, and with MemnormDtop's NULL route it gives the whole Deallocate Prop there; its interface hypothesis
   DGbigIF.DIfaceBig is the layer's YGcfInstFreeBig.diface_big_cf.  DIfaceBig's recycle field dbg_rcs_t (PRIMED,
   a working branch 3711d297cf5a) comes from WalkSigDrh's field wsr_rcs_rh (SEC_rh_t), through
   YGcfInstFreeBig.dbg_rcs_of_sec_rh_cf; the released wsd_rcs (SEC_t) has no cgif witness (Main 14:3xZ: no RCm route).

   Each walk top's SECTION HYPOTHESES are not fields: the unit discharges them when it instantiates its theorem at
   the layer's relation, as MemnormDtop.v:141-149 does at cgif:
   - IF : DGif0.DIface at the layer's ARX: the layer's instance (YGcfInstFree.v);
   - TS : the unit's symbol facts (cgif / preset TfibSyms, the AImg field im_syms);
   - FHC : DGfy.fh_c_spec, the seed record of the common arm, by the unit's own DGfu.FH_c (MemnormDtop.v:98-99);
   - ENQm : MnEnq.de_enqueue_m_t at the layer's ARX, lane F1's YGcfInstEnq.enq_m_cf (from its seam EnqArmsCf);
   - DRNm : MnDrain.de_drain_m_t at the layer's ARX, lane F2b's YGcfInstDrain.de_drain_m_cf (from its seam
     YGcfInstDrainSig.DrainSigC);
   - EAimg / EAz3 / EAdz / EAiz : ErrnoApart's image facts (lane F1's YGcfInstErrno record).
   A/DGg1.v:571 FH_m is NOT a field: its conclusion is the unit's seed record DGgm.free_hyps over its own image
   ([world tfibsegs], the walk's symbolic state DGgm.SS0), so it has no image-free statement; it is used only inside
   the mid / drain arms (MemnormDmid.v:163, :220), which the unit proves at its image.

   Field list checked by a fresh reviewer against preset's A' lines and c5's sources (2026-10-30, F2aSeamReview:
   PASS); reply's relocation (lane W) is checked when it lands.  The premises are satisfiable at a start state:
   YGcfInstFreeWit.free_pre_nil_init (preset, via ARcf_nil_init) and free_pre_start (reply instantiates it at its
   init_state, A/AD26.v:215); no meter is involved.  No numeral of any image; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormDleaf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG DGbigIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost YGcfMallocComposeERhBase.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
(* the walk's opaque relation at one ghost set: [YGcfInstBase.ARX_cf .. Hp] has this type *)
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable atpD : Z.
(* the recycle side's premise (the big-block arm) *)
Variable rpreB : astate -> Z -> Prop.
(* the drain's cut relation and the recycle invariant at Recycle's call (the big arm's secondary Recycle walk) *)
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* MemnormT's memory predicate at Deallocate's entry (field round 3 part 3): the two arms that call Put take it
   (A/MemnormDmid.v dealloc_mid_em / dealloc_drn_em, HMP after the entry premise); their keep law MP_keep is a
   Section hypothesis of the unit's walk *)
Variable MP : (word -> option byte) -> Prop.

Local Notation PRE := (DeallocG.dealloc_pre im_segs B U ARX rpre fpre atpD).
Local Notation LEAFE := (MemnormDleaf.dealloc_leaf_raw_eem B ft ARX AOX lpost).
Local Notation LEAF := (MemnormT.dealloc_leaf_raw_em im_segs B ft ARX AOX lpost).
(* the primed leaf under the re-hide (YGcfMallocComposeERhBase, plan row (c)) *)
Local Notation LEAFrh := (YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh im_segs B ft ARX AOX lpost).

(* The post of QuarantineCallback::Recycle on one chunk without the cache flag: DMrcSecNf.rchunk_sec_m_nf's, the
   RELEASED form, kept for the unit's released walk [SEC_t]; the primed [rcs_post_rh] below is DGbigIF.dbg_rcs_t's post
   (DGbigIF.v:131-144 at a working branch 3711d297cf5a), compared by conversion in
   YGcfInstFreeBig.dbg_rcs_of_sec_rh_cf. *)
Definition rcs_post (inst : Z) (ly : alayout) (X : astate) (k : chunk) (ks : list chunk) (zs : list Z)
  (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) :
  unit * astate -> world im_segs -> config -> Prop :=
  fun r0 W' c' => exists regs' mem' md',
    c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
    acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
    acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
    ErrnoG.errno_kept B mem mem' /\
    MemnormT.memnorm_keep im_segs mem mem' /\
    (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
     aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
    (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
    DRq (snd r0) ks zs /\ (forall a, AOX ly (snd r0) a -> AOX ly X a).

(* The unit's flag-free secondary Recycle walk (H4's DMrcSecNf.rchunk_sec_m_nf, relocated to the unit's image):
   Recycle (dg_rchunk) on a live secondary chunk whose map and pointer-array slot exist. *)
Definition SEC_t : Prop :=
  forall inst ly X k ks zs cbp W regs mem md r o sm i,
    rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PSec r o ->
    nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
    amreal im_segs (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md) (rcs_post inst ly X k ks zs W regs mem md).

(* Plan row (c), c0: the PRIMED twins, under the re-hide (a secondary Recycle unmaps the dead map and re-hides its
   shadow interior, so the walk runs at amreal' over RZ_cf and the call post is acall_post_x_rh).  [rcs_post_rh] is
   DMrcRh.rchunk_sec_rh_nf's post (DMrcRh.v:482-491 at a working branch 3d8ad2aeb77e), which is row (d)'s primed
   DGbigIF.dbg_rcs_t post; [SEC_rh_t] is the type of the primed walk field wsr_rcs_rh (the unit's relocation of
   rchunk_sec_rh_nf; its cgif witness is plan row (c4)). *)
Definition rcs_post_rh (inst : Z) (ly : alayout) (X : astate) (k : chunk) (ks : list chunk) (zs : list Z)
  (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) :
  unit * astate -> world im_segs -> config -> Prop :=
  fun r0 W' c' => exists regs' mem' md',
    c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
    YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
    acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
    ErrnoG.errno_kept B mem mem' /\
    MemnormT.memnorm_keep im_segs mem mem' /\
    (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
     aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
    (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
    DRq (snd r0) ks zs /\ (forall a, AOX ly (snd r0) a -> AOX ly X a).

Definition SEC_rh_t : Prop :=
  forall inst ly X k ks zs cbp W regs mem md r o sm i,
    rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PSec r o ->
    nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
    YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
      (rcs_post_rh inst ly X k ks zs W regs mem md).
(* The unit's Deallocate walk, at this instance's parameters.  Every field is the unit's own theorem; nothing here
   is proved, and nothing here mentions a numeral. *)
Record WalkSigD : Prop := {
  (* the NULL arm *)
  wsd_null : forall inst so bp ly S W regs mem md p n tr,
    PRE inst so bp ly S W regs mem md p n tr ->
    p = PNull ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAFE inst ly S W regs mem md p n tr);
  (* the arm whose last batch has room: Enqueue inline, no drain *)
  wsd_common : forall inst so bp ly S W regs mem md p n tr lastb initr,
    PRE inst so bp ly S W regs mem md p n tr ->
    In (p, n) (blocks S) -> rev (qc_list (st_qthread S)) = lastb :: initr ->
    Z.of_nat (length (b_items lastb)) < kBatchSlots ->
    qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAFE inst ly S W regs mem md p n tr);
  (* the new-batch arm: QuarantineCache::Enqueue called, no drain *)
  wsd_mid : forall inst so bp ly S W regs mem md p n tr,
    PRE inst so bp ly S W regs mem md p n tr -> MP mem ->
    In (p, n) (blocks S) -> need_new_batch (st_qthread S) = true ->
    qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <=
      kQuarantineCacheMax ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAF inst ly S W regs mem md p n tr);
  (* the drain arm: Enqueue, then Quarantine::Drain *)
  wsd_drn : forall inst so bp ly S W regs mem md p n tr,
    PRE inst so bp ly S W regs mem md p n tr -> MP mem ->
    In (p, n) (blocks S) ->
    kQuarantineCacheMax <
      qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAF inst ly S W regs mem md p n tr);
  (* the big-block arm: Put's size test sends the chunk to QuarantineCallback::Recycle at once (c5 DGbig.dealloc_big_em,
     a working branch d501b72dd83) *)
  wsd_big : forall inst so bp ly S W regs mem md p n tr,
    DeallocG.dealloc_pre im_segs B U ARX rpreB fpre atpD inst so bp ly S W regs mem md p n tr ->
    In (p, n) (blocks S) ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAF inst ly S W regs mem md p n tr);
  (* the big arm's secondary Recycle walk (the layer turns it into DGbigIF.dbg_rcs_t: YGcfInstFreeBig).  OPEN at cgif:
     it has no cgif witness.  The old one (YGcfInstFreeRcscgif) rested on rc_sec_free_ledger_t, FALSE at a real
     recycle, and was deleted with it (cf layer 106590920c03).  Its non-vacuous twin is the PRIMED walk under the
     re-hide (DMrcRh.rchunk_sec_rh_nf, plan row (c)); Main 14:3xZ: no RCm route *)
  wsd_rcs : SEC_t
}.

(* Plan row (c): the unit's Deallocate walk under the RE-HIDE.  A Recycle of a secondary chunk unmaps its map and
   re-hides its shadow interior, so a walk that can recycle one ends at amreal' over RZ_cf in the primed leaf.  Two
   arms can: the drain arm (Quarantine::Drain recycles the popped chunks through DoRecycle) and the big-block arm
   (Put sends the chunk to Recycle at once); they are PRIMED here (wsr_drn, wsr_big_rh), and the big arm's secondary
   Recycle walk is the primed SEC_rh_t (wsr_rcs_rh).  The other three arms recycle nothing; their texts are
   WalkSigD's, and the primed top lifts them (YGcfMallocComposeERh.dealloc_leaf_raw_em_rh_of). *)
Record WalkSigDrh : Prop := {
  (* the NULL arm (WalkSigD.wsd_null's text) *)
  wsr_null : forall inst so bp ly S W regs mem md p n tr,
    PRE inst so bp ly S W regs mem md p n tr ->
    p = PNull ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAFE inst ly S W regs mem md p n tr);
  (* the arm whose last batch has room (WalkSigD.wsd_common's text) *)
  wsr_common : forall inst so bp ly S W regs mem md p n tr lastb initr,
    PRE inst so bp ly S W regs mem md p n tr ->
    In (p, n) (blocks S) -> rev (qc_list (st_qthread S)) = lastb :: initr ->
    Z.of_nat (length (b_items lastb)) < kBatchSlots ->
    qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAFE inst ly S W regs mem md p n tr);
  (* the new-batch arm (WalkSigD.wsd_mid's text) *)
  wsr_mid : forall inst so bp ly S W regs mem md p n tr,
    PRE inst so bp ly S W regs mem md p n tr -> MP mem ->
    In (p, n) (blocks S) -> need_new_batch (st_qthread S) = true ->
    qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <=
      kQuarantineCacheMax ->
    amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAF inst ly S W regs mem md p n tr);
  (* the drain arm, PRIMED: WalkSigD.wsd_drn's premises, the walk at amreal' over RZ_cf in the primed leaf *)
  wsr_drn : forall inst so bp ly S W regs mem md p n tr,
    PRE inst so bp ly S W regs mem md p n tr -> MP mem ->
    In (p, n) (blocks S) ->
    kQuarantineCacheMax <
      qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
    YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAFrh inst ly S W regs mem md p n tr);
  (* the big-block arm, PRIMED: WalkSigD.wsd_big's premises, the walk at amreal' over RZ_cf in the primed leaf *)
  wsr_big_rh : forall inst so bp ly S W regs mem md p n tr,
    DeallocG.dealloc_pre im_segs B U ARX rpreB fpre atpD inst so bp ly S W regs mem md p n tr ->
    In (p, n) (blocks S) ->
    YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (LEAFrh inst ly S W regs mem md p n tr);
  (* the big arm's secondary Recycle walk under the re-hide (plan row (c2); its cgif witness is row (c4)) *)
  wsr_rcs_rh : SEC_rh_t
}.

End b.
End a.
