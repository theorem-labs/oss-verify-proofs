(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YGcfInstEnqMissreply.v (commit 96257eb45295, file sha256 bd26f828fff9) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 1 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane F1 of the generic cf instance layer; integrator ReallocPrimary): reply's own twin, at
   image B, of lane F1's cgif instance file proofs/cgif/cgif_file_fuzzer/lib/YGcfInstEnqMisscgif.v (commit
   9e13a7a1004, field round 3 part 3, with the Enqueue seam): lane B2's Enqueue MISS-arm interface
   (EnqGmiss.EnqIfaceMiss) at the cf instance at reply B, and the
   room / hit records (lib/B/YGcfInstEnqTrpreset.v) closed by reply B's own walks.  The text is lib/A's
   YGcfInstEnqMisspreset.v with reply B's modules (B/YFh3.segP, B/YFh4.segQH, B/YFh5.segR1, B/YFh6.segT, B/YFgq / YFgr,
   B/YFft, B/YFf6, and lane W's lib/B relocations of YFg4cf / YFg5cf / YFg6cf / YFfqcf / YFf2cf, same lemma and
   argument names); the one image numeral is the Refill call's return address in B/YFh5.at_CALLR (0x36cb4; reply A
   0x361e8; cgif 0x35954).
   Premises left (named): YGcfInstRefill.refill_spec_cf B IOK (the internal allocator's walk at reply B), TfibSyms B,
   HIOK (IOK i -> i = as_inst B), HRS (YG0ncf.relro_seg_t, reply: PresetRelroGeoB.relro_seg_preset_B); since field round 2
   the two machine cells and their rows are ARmcf fields.  enq_arms_cf_preset inhabits the seam YGcfInstEnq.EnqArmsCf from
   the three records (lane B2's EnqGroom / EnqGhit / EnqGmiss arms), under the same refill contract.
   rule 24: no function proved (kind: interface-instance discharge at reply's image B). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The reply image instances first, as the cgif file takes cgif's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFex YFfu YFfq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFgp YFgq YFgr YFh3 YFh4 YFh5 YFh6 YFft.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0qcf YG0scf YG0dcf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstEnq YGcfInstEnqG YGcfInstRefill. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YGcfInstEnqTrpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFf2cf YFfqcf YFg4cf YFg5cf YFg6cf. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFf6 EnqGbase. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require EnqGmiss. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLenq MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MnRefillLocpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require EnqGroom EnqGhit.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (IOK : Z -> Prop) (Hp : list Z).
Hypothesis HIOK : forall i, IOK i -> i = as_inst B.
(* The unit row behind arodata_ok_cf's keep from Enqueue's entry to the Refill call (YG0ncf.relro_seg_t; cgif:
   PresetRelroGeoB.relro_seg_preset_B). *)
Hypothesis HRS : relro_seg_t im_segs.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation EP := (enq_pre_cf B ARX).
Let HAR := ARX_cf_ARcf B IOK Hp.

(* reply B's walk posts and windows of the miss arm (the texts of B2's EnqGcgifMiss.v at B) and the refill leaf at the cf instance. *)
Definition ACALL_cf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) : world tfibsegs -> config -> Prop :=
YFh5.at_CALLR W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X) 0 (YFfqcf.jst ly W mem).

Definition WINc_cf (ly : alayout) (regs : bvmap 5 word) (X : astate) (a : Z) : Prop := YFgq.WIN0 ly regs a.

Definition RLEAF_cf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) (c1 : config) :
unit * astate -> world tfibsegs -> config -> Prop :=
refill_leaf_gen_cf B Hp ly X kBatchClass W (ms_regs (cfg_ms c1)) (ms_mem (cfg_ms c1)) (cfg_model c1).

Definition ARETm_cf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) (X1 : astate) (W5 : world tfibsegs) (c5 : config)
(l : list Z) : world tfibsegs -> config -> Prop :=
YFh6.at_RETR W5 ly (ms_regs (cfg_ms c5)) (ms_mem (cfg_ms c5)) (cfg_model c5)
  (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X1) (Z.of_nat (length l)) (last l 0)
  (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
  (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
  (bv_unsigned (getr regs 21)).

Definition WINm_cf (ly : alayout) (regs : bvmap 5 word) (X1 : astate) (l : list Z) (a : Z) : Prop :=
YFgr.WIN ly (st_qthread X1) (Z.of_nat (length l)) (last l 0) a.

Definition Smiss_cf (X : astate) (k : chunk) (l : list Z) : astate := YFf2cf.S' X k l.

(* The tail segment's window lies in YFf2cf.D at the refilled state (B2's win_D_miss). *)
Lemma win_D_miss_cf : forall ly X1 regs l a,
WINm_cf ly regs X1 l a -> YFf2cf.D ly X1 l (bv_unsigned (getr regs 2)) a.
Proof.
intros ly X1 regs l a HW.
unfold WINm_cf, YFgr.WIN, YFgr.WINT, YFgr.WINA, YFgr.NBv, YFgr.QLv in HW.
unfold YFf2cf.D, YFf2cf.DT, YFf2cf.DN, YFf2cf.DL, YFf2cf.DS, YFf2cf.QLv.
destruct HW as [HW|[[_ HW]|[Hq HW]]];
  [left; exact HW | right; left; lia | right; right; left; split; [exact Hq | first [exact HW | lia]]].
Qed.

(* The refill leaf on the miss arm's path (the refilled class-24 cache is not empty): the layout is kept, and every
   clause the fields read, at the call configuration's registers and memory. *)
Lemma rleaf_miss : forall ly X W regs mem md k c1 X1 W5 c5,
RLEAF_cf ly X W regs mem md k c1 (tt, X1) W5 c5 -> pc_chunks (cache X1 kBatchClass) <> [] ->
exists regs' mem' md',
c5 = cfg_at tfibsegs (raZ (ms_regs (cfg_ms c1))) regs' mem' md' /\
acall_post_cf tfibsegs B RSTACK ly X Hp W (ms_regs (cfg_ms c1)) (ms_mem (cfg_ms c1)) (cfg_model c1)
  (refill_exc_cf B kBatchClass ly X ly X1) ly X1 W5 regs' mem' md' /\
getr regs' 10 = w64 1 /\ xs_mapped_cf ly X1 md' /\
(forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly X1 (bv_unsigned x) ->
   ~ (spZ (ms_regs (cfg_ms c1)) - RSTACK <= bv_unsigned x < spZ (ms_regs (cfg_ms c1))) -> mem' x = ms_mem (cfg_ms c1) x) /\
MemnormT.memnorm_keep tfibsegs (ms_mem (cfg_ms c1)) mem' /\ refill_q_cf X X1.
Proof.
intros ly X W regs mem md k c1 X1 W5 c5 HRL NE.
destruct HRL as ((ly' & regs' & mem' & md' & Hc & POST & R10 & LY & XSM & _ & _ & _ & FR & _ & MNK) & RQ & _).
cbn [snd] in *.
assert (G1 : getr regs' 10 = w64 1).
{ rewrite R10. destruct (pc_chunks (cache X1 kBatchClass)); [exfalso; exact (NE eq_refl) | reflexivity]. }
specialize (LY G1). subst ly'.
exists regs', mem', md'. split; [exact Hc|].
change (REP_W kBatchClass) with RSTACK in POST, FR.
split; [exact POST|]. split; [exact G1|]. split; [exact XSM|].
split; [|split; [exact MNK | exact RQ]].
intros x N1 N2 N3. apply FR; [exact N1 | exact N2 | change (REP_W kBatchClass) with RSTACK; exact N3 |].
intros [N _]. exact (N eq_refl).
Qed.

(* The first segment's window (YFgq.WIN0: Enqueue's stack window and the thread object's cells): owned at the
   pre-state or stack scratch (the field im_owned1), and memnorm-safe (im_safe1).  Lemmas, because im_refill reads
   both to move memnorm / arodata_ok_cf from Enqueue's entry memory to the Refill call memory. *)
Lemma owned1_cf : forall inst ly X W regs mem md k a,
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = [] -> 0 <= a < 2 ^ 64 ->
WINc_cf ly regs X a -> aowned B ly X a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs).
Proof.
intros inst ly X W regs mem md k a PREX HNB Hl0 Ha HW.
pose proof (YFg6cf.M B IOK Hp inst ly X W regs mem md k PREX) as M0.
unfold WINc_cf, YFgq.WIN0, YFgq.WINT in HW.
destruct HW as [HW|[HW|[HW|HW]]].
- right. unfold spZ, CLenq.QSTACK_G. lia.
- left. apply (own_core_cf B ly X Hp _ (ly_T ly, kThreadObjSize) a M0);
    [unfold core_extents; apply in_cons; apply in_eq | cbn [fst snd]; unfold t_qc, kThreadObjSize in *; lia].
- left. apply (own_core_cf B ly X Hp _ (ly_T ly, kThreadObjSize) a M0);
    [unfold core_extents; apply in_cons; apply in_eq | cbn [fst snd]; unfold t_cache, kThreadObjSize in *; lia].
- left. apply (own_core_cf B ly X Hp _ (ly_T ly, kThreadObjSize) a M0);
    [unfold core_extents; apply in_cons; apply in_eq | cbn [fst snd]; unfold t_cache_stats, kThreadObjSize in *; lia].
Qed.

Lemma safe1_cf : forall inst ly X W regs mem md k (x : word),
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = [] ->
WINc_cf ly regs X (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros inst ly X W regs mem md k x PREX HNB Hl0 HW.
pose proof (amc_layout _ _ _ _ _ (YFg6cf.M B IOK Hp inst ly X W regs mem md k PREX)) as LY.
pose proof (YFg6cf.IMG B IOK Hp inst ly X W regs mem md k PREX) as IMG.
pose proof (YFg6cf.HSP B IOK Hp inst ly X W regs mem md k PREX) as HSPX.
unfold WINc_cf, YFgq.WIN0, YFgq.WINT in HW.
destruct HW as [HW|[HW|[HW|HW]]].
- apply (MnRefillLocpreset.mn_safe_stack ly x LY). unfold QSTACK in *. lia.
- apply (MnRefillLocpreset.mn_safe_thread ly x LY IMG). unfold t_qc, kThreadObjSize in *. lia.
- apply (MnRefillLocpreset.mn_safe_thread ly x LY IMG). unfold t_cache, kThreadObjSize in *. lia.
- apply (MnRefillLocpreset.mn_safe_thread ly x LY IMG). unfold t_cache_stats, kThreadObjSize in *. lia.
Qed.

(* The miss arm's record at the cf instance. *)
Theorem iface_miss_cf_preset : refill_spec_cf B IOK ->
EnqGmiss.EnqIfaceMiss tfibsegs dg_enqueue B ARX (aowned B) EP ENQ_NMAX_STRICT kFreeArrayOffset
  ACALL_cf WINc_cf RLEAF_cf ARETm_cf WINm_cf Smiss_cf.
Proof.
intros R1. constructor.
- (* im_nmax *) exact (enq_nmax_cf B Hp ARX HAR).
- (* im_rmaxd_ok *) exact rmaxd_ok_cf.
- (* im_rmax: the refilled state's Wf_cf (the leaf's relation) bounds its mapped bytes *)
  intros inst ly X W regs mem md k c1 X1 W5 c5 l PREX HRL CI Hl Hlne.
  destruct HRL as ((ly' & regs' & mem' & md' & _ & POST & _) & _). cbn [snd] in POST.
  pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 POST))) as WX1.
  exact (mapped_bound_cf _ 0 0 0 X1 kBatchClass WX1 ltac:(unfold kBatchClass; lia)).
- (* im_step: YFft.amreal_enqueue_nb with YFft.enq_after_refill *)
  intros X k W c Q HNB H.
  apply (amreal_enqueue_nb k X W c Q HNB).
  eapply amreal_mono; [|exact H]. cbv beta.
  intros r W1 c1 (NE & HS).
  unfold enq_after_refill.
  destruct (pc_chunks (cache (snd r) kBatchClass)) as [|o l0] eqn:Ec0; [exfalso; exact (NE eq_refl)|].
  cbn [amreal]. eapply SRr_mono; [exact (HS (o :: l0) eq_refl)|]. intros W2 c2 _ HQ. exact HQ.
- (* im_walk1: reply B's first segment at YFg6cf.FH0_ok_cf *)
  intros inst ly X W regs mem md k PREX HNB Hl0 _.
  unfold ACALL_cf, cfg_at. rewrite <- (YFf6.wvb_self md) at 1.
  exact (YFh5.segR1 W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X) 0 0
    (YFfqcf.jst ly W mem) (m_vm_materialized md)
    (YFg6cf.FH0_ok_cf B TB IOK Hp inst ly X W regs mem md k PREX HNB Hl0) eq_refl).
- (* im_frame1 *)
  intros inst ly X W regs mem md k W1 c1 PREX HNB Hl0 HC x NW.
  unfold ACALL_cf in HC.
  destruct HC as (_ & regs1 & mem1 & mat & Ec1 & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  rewrite Ec1. cbn [cfg_ms ms_mem]. exact (MQ1 x NW).
- (* im_owned1: the thread object is owned at the pre-state *)
  exact owned1_cf.
- (* im_safe1 *)
  exact safe1_cf.
- (* im_arx_call: YFg6cf.AR1X *)
  intros inst ly X W regs mem md k W1 c1 PREX HNB Hl0 HC.
  unfold ACALL_cf in HC.
  destruct HC as (-> & regs1 & mem1 & mat & -> & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  cbn [cfg_ms ms_mem cfg_model].
  exact (YFg6cf.AR1X B IOK Hp inst ly X W regs mem md k PREX Hl0 mem1 mat MQ1 PR1 V1 V2 V3 V4 V5 V6).
- (* im_refill: RefillSpec's contract at the call configuration (YFg6cf.REFILL_CALL), with the two call-state
     facts (part 3c): cf_hull_ok X from the pre, and arodata_ok_cf moved from Enqueue's entry memory to the call
     memory over the first segment's frame (its window is owned or stack scratch, so it misses every non-owned
     covered byte) *)
  intros inst ly X W regs mem md k W1 c1 PREX HNB Hl0 HC HARc.
  pose proof (enq_pre_mp_cf B ARX inst ly X W regs mem md k PREX) as (HULL & AD).
  pose proof PREX as (HARX0 & _ & _ & _ & _ & _ & _ & _ & _ & HLQ & _).
  pose proof (amc_layout _ _ _ _ _ (YFg6cf.M B IOK Hp inst ly X W regs mem md k PREX)) as LY.
  assert (FR1 : forall x : word, ~ WINc_cf ly regs X (bv_unsigned x) -> ms_mem (cfg_ms c1) x = mem x).
  { intros x NW. unfold ACALL_cf in HC.
    destruct HC as (_ & regs1 & mem1 & mat & Ec1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MQ1 & _).
    rewrite Ec1. cbn [cfg_ms ms_mem]. exact (MQ1 x NW). }
  assert (AD1 : YG0dcf.arodata_ok_cf im_segs B (ms_mem (cfg_ms c1))).
  { apply (YG0dcf.arodata_keep_cf im_segs B ly X Hp W mem md ly X Hp W1 (ms_mem (cfg_ms c1)) (cfg_model c1)
      (WINc_cf ly regs X) (HAR _ _ _ _ _ _ HARX0) (HAR _ _ _ _ _ _ HARc) HRS); [|exact FR1|exact AD].
    intros a Ha NO R I I' NA NA' NX NX' HW.
    destruct (owned1_cf inst ly X W regs mem md k a PREX HNB Hl0 ltac:(unfold kImgLo, kImgEnd in R; lia) HW) as [O|O].
    - exact (NA O).
    - pose proof (lo_top _ LY) as (_ & _ & _ & _ & _ & _ & T7).
      clear - O HLQ T7 R. unfold CLenq.QSTACK_G, kHighMemBeg, kImgEnd in *. lia. }
  unfold ACALL_cf in HC.
  destruct HC as (-> & regs1 & mem1 & mat & -> & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  destruct (YFg6cf.REFILL_CALL B TB IOK Hp inst ly X W regs mem md k PREX Hl0 regs1 mem1 mat R_ra R_sp R_gp R_tp
    R_a0 R_a1 R_a2 R_a3 MQ1 PR1 V1 V2 V3 V4 V5 V6 HIOK) as [ST CALL].
  unfold RLEAF_cf. cbn [cfg_ms ms_regs ms_mem cfg_model] in *.
  exact (R1 Hp inst ly X W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass ST AD1 HULL CALL).
- (* im_apostg: YGcfInstEnqG.refill_batch_apostg_cf at WfR_cf U 1 0 1 X *)
  intros inst ly X W regs mem md k PREX HNB Hl0 tr r HP HG.
  pose proof (enq_pre_wf_cf B Hp ARX HAR inst ly X W regs mem md k PREX) as W0.
  destruct (enq_pre_tick_cf B ARX inst ly X W regs mem md k PREX) as [E1 E2].
  pose proof PREX as (_ & BR & _).
  exact (refill_batch_apostg_cf (as_universe B) X (enq_reslack_cf (as_universe B) X W0 E2 E1) BR tr r HP HG).
- (* im_frameR: the leaf's raw frame and keep, with Refill's RSTACK window inside Enqueue's *)
  intros inst ly X W regs mem md k W1 c1 [u X1] W5 c5 PREX HNB Hl0 HC HRL NE. cbn [snd] in NE |- *.
  destruct u.
  pose proof HC as HC'. unfold ACALL_cf in HC'.
  destruct HC' as (_ & regs1 & mem1 & mat & Ec1 & R_ra & R_sp & _).
  destruct (rleaf_miss ly X W regs mem md k c1 X1 W5 c5 HRL NE) as (regs' & mem' & md' & Hc5 & _ & _ & _ & FR & MNK & _).
  assert (E1r : ms_regs (cfg_ms c1) = regs1) by (rewrite Ec1; reflexivity).
  assert (SP1 : spZ regs1 = spZ regs - 64).
  { pose proof (YFg6cf.HSP B IOK Hp inst ly X W regs mem md k PREX) as HSPX.
    pose proof (YFg6cf.HI0 B IOK Hp inst ly X W regs mem md k PREX) as (_ & _ & _ & _ & hS1 & _).
    pose proof (u64_range (getr regs 2)) as U.
    unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small.
    unfold QSTACK, kHighMemBeg in *. lia. }
  assert (E5m : ms_mem (cfg_ms c5) = mem') by (rewrite Hc5; reflexivity).
  rewrite E5m. split; [|exact MNK].
  intros x NO NO1 NS. apply (FR x NO NO1). rewrite E1r, SP1. intros O. apply NS. unfold CLenq.QSTACK_G, RSTACK in *. lia.
- (* im_walk2: reply B's tail segment at YFg6cf.FHR_ok_cf *)
  intros inst ly X W regs mem md k W1 c1 X1 W5 c5 l PREX HNB Hl0 HC HRL RO CI Hl Hlne HN HRM.
  unfold ACALL_cf in HC.
  destruct HC as (_ & regs1 & mem1 & mat & Ec1 & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (NE : pc_chunks (cache X1 kBatchClass) <> []) by (rewrite Hl; exact Hlne).
  destruct (rleaf_miss ly X W regs mem md k c1 X1 W5 c5 HRL NE) as (regs' & mem' & md' & Hc5 & POST & HA0 & _).
  assert (E1r : ms_regs (cfg_ms c1) = regs1) by (rewrite Ec1; reflexivity).
  assert (E1m : ms_mem (cfg_ms c1) = mem1) by (rewrite Ec1; reflexivity).
  assert (E1d : cfg_model c1 = with_vm_backing (m_vm_lazy md) mat md) by (rewrite Ec1; reflexivity).
  rewrite E1r, E1m, E1d in POST. rewrite E1r in Hc5.
  destruct l as [|o1 l1']; [exfalso; exact (Hlne eq_refl)|].
  assert (Era : raZ regs1 = 0x36cb4).
  { unfold raZ. rewrite R_ra. unfold w64. apply unsigned_lit_small. lia. }
  assert (E5r : ms_regs (cfg_ms c5) = regs') by (rewrite Hc5; reflexivity).
  assert (E5m : ms_mem (cfg_ms c5) = mem') by (rewrite Hc5; reflexivity).
  assert (E5d : cfg_model c5 = md') by (rewrite Hc5; reflexivity).
  unfold ARETm_cf. rewrite E5r, E5m, E5d. rewrite Hc5. unfold cfg_at. rewrite Era.
  rewrite <- (YFf6.wvb_self md') at 1.
  exact (YFh6.segT W5 ly regs' mem' md' (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X1)
    (Z.of_nat (length (o1 :: l1'))) (last (o1 :: l1') 0) (YFfqcf.jst ly W5 mem')
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
    (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
    (bv_unsigned (getr regs 21)) (m_vm_materialized md')
    (YFg6cf.FHR_ok_cf B TB IOK Hp inst ly X W regs mem md k PREX HNB regs1 mem1 mat R_sp R_tp R_s0 R_s1 R_s2 R_s3 R_s5
       PR1 F1 F2 F3 F4 F5 F6 F7 W5 regs' mem' md' X1 POST RO HA0 o1 l1' Hl)).
- (* im_frame2 *)
  intros ly X W regs mem md k X1 W5 c5 l W6 c6 HR6.
  unfold ARETm_cf in HR6.
  destruct HR6 as (HWW6 & regs6 & mem6 & mat6 & Hc6 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QCS & MEQ6 &
    PRESW6 & VALS6).
  exists regs6, mem6, (with_vm_backing (m_vm_lazy (cfg_model c5)) mat6 (cfg_model c5)).
  split; [rewrite Hc6; unfold cfg_at, raZ; reflexivity | exact MEQ6].
- (* im_post: YFg6cf.FINR_cf *)
  intros inst ly X W regs mem md k W1 c1 X1 W5 c5 l W6 c6 PREX HNB Hl0 HC HRL RO CI Hl Hlne HR6.
  unfold ACALL_cf in HC.
  destruct HC as (_ & regs1 & mem1 & mat & Ec1 & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (NE : pc_chunks (cache X1 kBatchClass) <> []) by (rewrite Hl; exact Hlne).
  destruct (rleaf_miss ly X W regs mem md k c1 X1 W5 c5 HRL NE) as (regs' & mem' & md' & Hc5 & POST & HA0 & XSM5 & _).
  assert (E1r : ms_regs (cfg_ms c1) = regs1) by (rewrite Ec1; reflexivity).
  assert (E1m : ms_mem (cfg_ms c1) = mem1) by (rewrite Ec1; reflexivity).
  assert (E1d : cfg_model c1 = with_vm_backing (m_vm_lazy md) mat md) by (rewrite Ec1; reflexivity).
  rewrite E1r, E1m, E1d in POST.
  destruct l as [|o1 l1']; [exfalso; exact (Hlne eq_refl)|].
  assert (E5r : ms_regs (cfg_ms c5) = regs') by (rewrite Hc5; reflexivity).
  assert (E5m : ms_mem (cfg_ms c5) = mem') by (rewrite Hc5; reflexivity).
  assert (E5d : cfg_model c5 = md') by (rewrite Hc5; reflexivity).
  unfold ARETm_cf in HR6. rewrite E5r, E5m, E5d in HR6.
  exact (YFg6cf.FINR_cf B TB IOK Hp inst ly X W regs mem md k PREX HNB Hl0 regs1 mem1 mat R_sp R_gp R_tp R_hi
    MQ1 PR1 V1 V2 V3 V4 V5 V6 W5 regs' mem' md' X1 POST XSM5 RO CI o1 l1' Hl W6 c6 HR6).
- (* im_owned2: YFf2cf.D_owned_cf at the refilled state *)
  intros inst ly X W regs mem md k c1 X1 W5 c5 l a PREX HNB Hl0 HRL CI Hl Hlne Ha HW.
  assert (NE : pc_chunks (cache X1 kBatchClass) <> []) by (rewrite Hl; exact Hlne).
  destruct (rleaf_miss ly X W regs mem md k c1 X1 W5 c5 HRL NE) as (regs' & mem' & md' & _ & POST & _).
  pose proof (win_D_miss_cf ly X1 regs l a HW) as HD.
  destruct (YFf2cf.D_owned_cf B ly X1 (aview tfibsegs (w_H W5) mem') Hp (proj1 (proj1 POST)) k CI l Hl Hlne
    (bv_unsigned (getr regs 2)) (YFg6cf.HSP B IOK Hp inst ly X W regs mem md k PREX) a (proj1 Ha) HD) as [O|O].
  + left. exact O.
  + right. unfold YFf2cf.DS in O. unfold spZ, CLenq.QSTACK_G, QSTACK in *. exact O.
- (* im_safe2 *)
  intros inst ly X W regs mem md k c1 X1 W5 c5 l x PREX HNB Hl0 HRL CI Hl Hlne HW.
  assert (NE : pc_chunks (cache X1 kBatchClass) <> []) by (rewrite Hl; exact Hlne).
  destruct (rleaf_miss ly X W regs mem md k c1 X1 W5 c5 HRL NE) as (regs' & mem' & md' & _ & POST & _).
  pose proof (win_D_miss_cf ly X1 regs l (bv_unsigned x) HW) as HD.
  exact (YFf2cf_D_safe B ly X1 (aview tfibsegs (w_H W5) mem') Hp (proj1 (proj1 POST)) CI l Hl Hlne
    (bv_unsigned (getr regs 2)) (YFg6cf.HSP B IOK Hp inst ly X W regs mem md k PREX)
    (YFg6cf.IMG B IOK Hp inst ly X W regs mem md k PREX) x HD).
- (* im_aox: YFg6cf.aowned_same *)
  intros ly S S' a Hch Hfs HO. exact (YFg6cf.aowned_same B ly S S' a Hch Hfs HO).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The room and hit records with their walk fields discharged by reply B's own walks.                                  *)
Theorem iface_room_cf_preset_closed :
EnqGbase.EnqIfaceRoom tfibsegs dg_enqueue B ARX (aowned B) EP ENQ_NMAX_STRICT (ARETr_cf B) WINr_cf.
Proof.
apply (iface_room_cf_preset B TB IOK Hp).
intros inst ly X W regs mem md k PRE HNB _.
unfold ARETr_cf, cfg_at. rewrite <- (YFf6.wvb_self md) at 1.
exact (YFh3.segP W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (YFgq.QSZv (st_qthread X))
  (YFg4cf.QLv ly X) (YFgq.QBv (st_qthread X)) (YFg4cf.CNTv X) (YFg4cf.BSZv X) (m_vm_materialized md)
  (YFg4cf.FH_ok_cf B TB IOK Hp inst ly X W regs mem md k PRE HNB)).
Qed.

Theorem iface_hit_cf_preset_closed :
EnqGbase.EnqIfaceHit tfibsegs dg_enqueue B ARX (aowned B) EP ENQ_NMAX_STRICT kFreeArrayOffset (ARETh_cf B) WINh_cf Shit_cf.
Proof.
apply (iface_hit_cf_preset B TB IOK Hp).
intros inst ly X W regs mem md k l PRE HNB Hl Hlne _ _.
unfold ARETh_cf, cfg_at. rewrite <- (YFf6.wvb_self md) at 1.
exact (YFh4.segQH W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X)
  (Z.of_nat (length l)) (last l 0) (YFfqcf.jst ly W mem) (m_vm_materialized md)
  (YFg5cf.FH_ok_cf B TB IOK Hp inst ly X W regs mem md k PRE HNB l Hl Hlne)
  ltac:(clear - Hlne; destruct l as [|o l0]; [congruence | cbn [length]; lia])).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The Enqueue seam YGcfInstEnq.EnqArmsCf at reply B: lane B2's three generic arms (EnqGroom.enq_room_g,                 *)
(* EnqGhit.enq_hit_g, EnqGmiss.enq_miss_g) at the three records above; open premise: the unit's Refill contract       *)
(* (refill_spec_cf), the miss arm's.                                                                                  *)

(* The arms' post is the seam's, by conversion (EnqGbase.enq_arm_post_g at segs := im_segs, AOX := aowned B). *)
Lemma enq_arm_post_conv : forall inst ly X W regs mem md k r W' c',
  EnqGbase.enq_arm_post_g tfibsegs B ARX (aowned B) inst ly X W regs mem md k r W' c' =
  enq_arm_post_cf B ARX inst ly X W regs mem md k r W' c'.
Proof. reflexivity. Qed.

Theorem enq_arms_cf_preset : refill_spec_cf B IOK -> EnqArmsCf B ARX.
Proof.
intros RS. split.
- intros inst ly X W regs mem md k PRE HNB.
  exact (EnqGroom.enq_room_g _ _ _ _ _ _ _ _ _ iface_room_cf_preset_closed inst ly X W regs mem md k PRE HNB).
- intros inst ly X W regs mem md k l PRE HNB Hl Hlne.
  exact (EnqGhit.enq_hit_g _ _ _ _ _ _ _ _ _ _ _ iface_hit_cf_preset_closed inst ly X W regs mem md k l PRE HNB Hl Hlne).
- intros inst ly X W regs mem md k PRE HNB Hl0.
  exact (EnqGmiss.enq_miss_g _ _ _ _ _ _ _ _ _ _ _ _ _ _ (iface_miss_cf_preset RS) inst ly X W regs mem md k PRE HNB Hl0).
Qed.
End b.
End a.
