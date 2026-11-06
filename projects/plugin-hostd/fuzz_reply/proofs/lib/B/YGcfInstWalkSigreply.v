(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane; 2026-10-31 part 3c and the closers, a Theorem Labs lane, for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply): the image B twin
   (fuzz_reply.asan-ubsan) of lib/A/YGcfInstWalkSigreply.v (a Theorem Labs lane):
   reply's Allocate walk tops at image B assembled into YGcfInstWalkSig.WalkSigA at YGcfInstAllocTop.v's instance.
   rule 24: no function proved (kind: assembly of proved Allocate arms into WalkSigA).
   Changes against the A text: module paths lib.A -> lib.B and the image twins A<r> -> Y<r> (CfImgA -> CfImgB,
   ReplyUnitFactsA -> ReplyUnitFactsB, hoeb_A -> hoeb_B); the entry is B's
   cf_pc_allocate = 0x31c30 (B/CfImgB.v:40 = B/AGhy.v:34 A_Allocate).  The CfParams instance stays A's CfParams_reply
   (lib/A/CfParamsReply.v), not lib/B/CfParamsReplyB.v's CfParams_reply_B: image B's target text (B/ReplyAllocTargetsB.v:7-10)
   and its consumers (a Theorem Labs lane's B/ReplyMallocB.v, B/ReplyClosedB.v) name CfParams_reply.
   Round 3 part 3c (this line is a Theorem Labs lane's 3c-b): the miss arms are the B miss chain's tops
   YGcfInstMissW.cfi_alloc_missg_cf_em / cfi_alloc_missk_cf_em (CfInstMiss), which take part 3c's arodata_ok_cf
   (WalkSigA's wsa_missg / wsa_missk at cf layer 9e2e0be6e3e5); the round-3 image premises PF_AG / HPFA / HRS come from
   YGcfInstHitreply.hit_pf_ag_B and ReplyRelroGeoB.  No premise of the instance files is left named: HRW is B3LeafCf's
   YGcfRefillTopreply.refill_walk_cf_reply_closed (a Theorem Labs lane's B relocation), IFS / IFSE are CfInstSec's
   YGcfInstSecreply.ifaceSw_B / ifaceSE_B.
   EVENT-FREE: no event counter, event bound, meter or regime appears in this file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The reply image instances first, as the walk files take them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG AGif0reply ImgBaseAGS AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLdepot ErrnoApart MemnormT AGif0n AGif4 ErrnoGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface YGcfErrbSep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstRefill YGcfInstWalkSig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstErrno YGcfInstHit YGcfInstHitreply YGcfInstMissW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstAllocTop.
(* reply's unit facts *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyUnitFactsB ReplyImg_hoeb ReplyRelroGeoB.
(* CfInstSec's secondary interfaces and B3LeafCf's refill walk at reply B *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstSecreply YGcfRefillTopreply.
(* the depot instance (lane F1's YGcfInstDepot, by path) and reply's depot walk row (CfF1) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstDepot YGcfInstDepotWreply.
(* the walk tops, used qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGhy AGioM MemnormHitG MemnormHitK.
Import ListNotations.
(* ErrnoGS's Require hazard (its header): restore lia's euclidean division after the Requires. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* YM05 / YM03 redefine [lia] for the run-ceiling goals; this file's arithmetic is plain. *)
Local Ltac zl := YM03.lf_lia_orig.

(* reply's CfImg instance at B (cf_pc_allocate = 0x31c30, B/CfImgB.v:40, the walk tops' entry) and its allocator parameters. *)
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Section b.
(* the unit's instance object (YGcfInstBase's IOK) *)
Variable IOK : Z -> Prop.
Hypothesis IOK_inst : IOK_ok TfibB IOK.
(* the call site's can_fill (YGcfInstAllocTop.v:44-45) *)
Variable cf : Z.
Hypothesis HCF : cf = 0 \/ cf = 1.

(* ---- the image premises, from reply's unit facts ---- *)
Let TS : TfibSyms TfibB := TfibB_syms.
Let UF := ReplyUnitFactsB.reply_unit_facts_B TfibB TfibB_syms.

(* The refill walk at the instance: B3LeafCf's closer at reply B (a Theorem Labs lane's lib/B/YGcfRefillTopreply.v
   refill_walk_cf_reply_closed, the class-full arm discharged by the relocated report). *)
Lemma HRW_reply : refill_walk_cf TfibB IOK.
Proof. exact (YGcfRefillTopreply.refill_walk_cf_reply_closed TfibB IOK TfibB_syms IOK_inst). Qed.

(* The secondary interface at the instance (AGioM.v IFS at NMAXW := cf_malloc_max, NOBW := cf_nob, ROOMW := 2 ^ 32,
   and IFSE): CfInstSec's closers at reply B (lib/B/YGcfInstSecreply.v ifaceSw_B / ifaceSE_B), whose four premises are
   TfibSyms, IOK_ok, IMG_COVER and reply's dhash (uf_dhash_img). *)
Lemma IFS_reply : forall Hp, AGif4.AIfaceSw TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow
  cf_malloc_max cf_nob (2 ^ 32).
Proof.
exact (YGcfInstSecreply.ifaceSw_B TfibB IOK TS IOK_inst (ReplyUnitFactsB.uf_IMG_COVER _ UF)
  (ReplyUnitFactsB.uf_dhash_img _ UF)).
Qed.
Lemma IFSE_reply : forall Hp, ErrnoGS.AIfaceSE TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
exact (YGcfInstSecreply.ifaceSE_B TfibB IOK TS IOK_inst (ReplyUnitFactsB.uf_IMG_COVER _ UF)
  (ReplyUnitFactsB.uf_dhash_img _ UF)).
Qed.

(* the error buffer object is outside ag_dzone: uf_ERRB_SEP's last conjunct, contraposed *)
Lemma ERRB_AG_reply : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd TfibB ->
  ag_dzone ly' a -> ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Proof.
intros ly' a LY IC HT DZ Ha.
destruct (proj2 (ReplyUnitFactsB.uf_ERRB_SEP _ UF) ly' a LY IC HT Ha) as (_ & _ & _ & NDZ). exact (NDZ DZ).
Qed.

(* reply's universe has no wild part (univ_of Tfib_universe [], A/AD2l.v), so depot_fits gives the depot's traces in the
   fixed set: the form reply's depot-keep row states (uf_dep_keep_img_ag). *)
Lemma depot_fits_incl_reply : forall d, depot_fits (as_universe TfibB) d ->
  List.NoDup d /\ incl d (as_universe TfibB).
Proof.
intros d (ND & FA & _). split; [exact ND|]. intros t Ht.
destruct (proj1 (Forall_forall _ _) FA t Ht) as (_ & [I | (pw & sfx & HP & _)]); [exact I|].
assert (EW : u_wild (as_universe TfibB) = []) by reflexivity. rewrite EW in HP. destruct HP.
Qed.

(* The depot field at the instance (YGcfInstDepot.if_depot_cf, YGcfInstDepot.v:201), from reply's image facts and CfF1's
   depot walk row YGcfInstDepotWreply.depot_spec_a_reply at reply's dhash (uf_dhash_img). *)
Lemma HDEP_reply : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp TfibB (ARXq_cf TfibB IOK Hp) (U_cf TfibB)
  ag_dzone (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof.
intros Hp.
refine (YGcfInstDepot.if_depot_cf TfibB Hp (ARXq_cf TfibB IOK Hp) _ (ReplyUnitFactsB.uf_IMG_COVER _ UF) _
  (ReplyUnitFactsB.uf_dep_fp_img_ag _ UF)
  (YGcfInstDepotWreply.depot_spec_a_reply TfibB TS (ReplyUnitFactsB.uf_dhash_img _ UF))).
- intros inst ly S W mem md H. eapply ARX_cf_ARcf. eapply ARXq_cf_ARX. exact H.
- intros ly S W mem0 mem LY IC HT DF C D K. destruct (depot_fits_incl_reply _ DF) as (ND & INC).
  exact (ReplyUnitFactsB.uf_dep_keep_img_ag _ UF ly S W mem0 mem LY IC HT ND INC C D K).
Qed.

(* the secondary arm's bounds at CfParams_reply (cf_malloc_max = 2 ^ 30 - 2 ^ 20, cf_nob = 2 ^ 30) *)
Lemma HNW_reply : cf_malloc_max + 4 * 4096 <= 2 ^ 30.
Proof. unfold CfParams_reply. cbn [cf_malloc_max]. zl. Qed.
Lemma HNOB_reply : cf_malloc_max + 4 * 4096 <= cf_nob.
Proof. unfold CfParams_reply. cbn [cf_malloc_max cf_nob]. zl. Qed.
Lemma HROOM_reply : 2 * (cf_malloc_max + 4 * 4096) + (cf_malloc_max + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= 2 ^ 32.
Proof.
pose proof HNW_reply as N. pose proof cf_malloc_max_pos as P.
assert (D : (cf_malloc_max + 4 * 4096) / 8 <= cf_malloc_max + 4 * 4096) by (apply Z.div_le_upper_bound; zl).
zl.
Qed.

(* The image premises in the instance files' names. *)
Local Ltac img_facts :=
  pose proof (TS : im_syms TfibB) as TSi;
  pose proof (ReplyUnitFactsB.uf_IMG_COVER _ UF) as HIMG;
  pose proof (ReplyUnitFactsB.uf_HSHB _ UF) as HSHB;
  pose proof (ReplyUnitFactsB.uf_HDZO _ UF) as HDZO;
  pose proof (ReplyUnitFactsB.uf_HDZX _ UF) as HDZX;
  pose proof (ReplyUnitFactsB.uf_HCW _ UF) as HCW;
  pose proof (ReplyUnitFactsB.uf_dep_fp_img_ag _ UF) as HFP;
  pose proof (ReplyUnitFactsB.uf_ag_inst_ok _ UF) as INST_AG;
  pose proof (ReplyUnitFactsB.uf_INST_CELLS_t _ UF) as INST_CELLS;
  assert (HTSD : as_tsd TfibB = im_tsd) by exact (ReplyUnitFactsB.uf_HTSD _ UF);
  assert (HOOM : as_oom_byte TfibB = im_oom) by exact (ts_oom TfibB TS);
  assert (HERR : as_errno TfibB = im_errno) by exact (ts_errno TfibB TS);
  destruct (ReplyUnitFactsB.uf_ErrnoImgCf _ UF) as (EII & _ & EDZ & ESH & _);
  pose proof (ReplyUnitFactsB.uf_errno_seg_t _ UF) as HEROM;
  pose proof (ReplyUnitFactsB.uf_errno_nstatic_t _ UF) as HENS;
  pose proof ERRB_AG_reply as ERRB_AG;
  pose proof HDEP_reply as HDEP;
  pose proof (ReplyUnitFactsB.uf_oom_owned_img _ UF) as oom_owned_img;
  pose proof (ReplyUnitFactsB.uf_oom_const_img _ UF) as oom_const_img;
  pose proof (ReplyImg_hoeb.hoeb_B TfibB TS) as HOEB;
  pose proof (YGcfInstHitreply.hit_pf_ag_B TfibB TS) as PF_AG;
  pose proof (ReplyRelroGeoB.pf_cells_apart_reply_B TfibB TS) as HPFA;
  pose proof ReplyRelroGeoB.relro_seg_reply_B as HRS;
  pose proof HRW_reply as HRW.

(* The walk tops' interface premises at the cf instance. *)
Lemma IF_reply : forall Hp, AGif0n.AIface TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_facts. eapply (YGcfInstHit.iface_cf TfibB IOK); eassumption. Qed.

Lemma IFK_reply : forall Hp, AGif0n.AIfaceK TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_facts. eapply (YGcfInstHit.ifaceK_cf TfibB IOK); eassumption. Qed.



(* Each walk top's Section premises, in any order. *)
Local Ltac walk_args Hp :=
  first [ exact (IF_reply Hp) | exact (IFK_reply Hp) | exact TS
        | exact (proj1 (ReplyUnitFactsB.uf_ErrnoImgCf _ UF))
        | exact (proj1 (proj2 (proj2 (proj2 (ReplyUnitFactsB.uf_ErrnoImgCf _ UF)))))
        | exact (proj1 (proj2 (proj2 (ReplyUnitFactsB.uf_ErrnoImgCf _ UF))))
        | eassumption ].

(* A field's premise and goal, restated at reply's image: im_segs is tfibsegs, cf_pc_allocate is [pc], AOXm_cf TfibB is
   AOX_cf TfibB and rpre_cfr TfibB is rpre_cf TfibB (conversion), as_oom_byte TfibB is TFIB_OOM (ts_oom). *)
Local Ltac to_arm Hp inst so bp ly S W regs mem md n tr HPRE pc :=
  change (alloc_pre tfibsegs TfibB (U_cf TfibB) (ARXq_cf TfibB IOK Hp) (rpre_cf TfibB) cf_malloc_max LIVE_MAX 8 1 cf
    inst so bp ly S W regs mem md n tr) in HPRE;
  rewrite (ts_oom TfibB TS);
  change (amreal tfibsegs (malloc_cf n tr S) W (cfg_at tfibsegs pc regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs TfibB malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) qtight TFIB_OOM
      inst ly S W regs mem md n tr)).

(* The walk signature at the instance YGcfInstAllocTop.v:49-50 names, at every ghost set. *)
Theorem walksig_cf_reply : forall Hp, WalkSigA im_segs TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp)
  (AOXm_cf TfibB) (YGcfRmodel.rpre_cfr TfibB) cf_malloc_max LIVE_MAX qtight cf.
Proof.
intros Hp. apply Build_WalkSigA.
- (* wsa_hit: MemnormHitG.ARM_HITG_em *)
  intros inst so bp ly S W regs mem md n tr l off HC HPRE Hn CI El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31c30.
  eapply (MemnormHitG.ARM_HITG_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) (rpre_cf TfibB)
    cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow); walk_args Hp.
- (* wsa_hitk: MemnormHitK.ARM_HITK_em *)
  intros inst so bp ly S W regs mem md n tr l off HC HPRE Hn CI El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31c30.
  eapply (MemnormHitK.ARM_HITK_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) (rpre_cf TfibB)
    cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow); walk_args Hp.
- (* wsa_missg: the B miss chain's top YGcfInstMissW.cfi_alloc_missg_cf_em (CfInstMiss, round 3 part 3c: it takes arodata_ok_cf only) *)
  intros inst so bp ly S W regs mem md n tr HC HPRE HAO Hn El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31c30.
  img_facts.
  eapply (YGcfInstMissW.cfi_alloc_missg_cf_em TfibB IOK); eassumption.
- (* wsa_missk: the B miss chain's top YGcfInstMissW.cfi_alloc_missk_cf_em (CfInstMiss, round 3 part 3c: it takes arodata_ok_cf only) *)
  intros inst so bp ly S W regs mem md n tr HC HPRE HAO Hn El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31c30.
  img_facts.
  eapply (YGcfInstMissW.cfi_alloc_missk_cf_em TfibB IOK); eassumption.
- (* wsa_sec: AGioM.alloc_sec_w_em, at NMAXW := cf_malloc_max, NOBW := cf_nob, ROOMW := 2 ^ 32 *)
  intros inst so bp ly S W regs mem md n tr HC HPRE Hn.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE AGhy.A_Allocate.
  exact (AGioM.alloc_sec_w_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) (rpre_cf TfibB)
    cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow (IF_reply Hp)
    cf_malloc_max cf_nob (2 ^ 32) HNW_reply HNOB_reply HROOM_reply (IFS_reply Hp) TS (Z.le_refl cf_malloc_max) cf HC (IFSE_reply Hp)
    inst so bp ly S W regs mem md n tr HPRE Hn).
Qed.

(* YGcfInstAllocTop's top (YGcfInstAllocTop.v:98) at reply, its WS given by walksig_cf_reply. *)
Theorem aalloc_realizes_cf_reply : aalloc_realizes_cf_em_m im_segs TfibB cf_malloc_max 8 1 cf (ARXq_cf TfibB IOK).
Proof. exact (YGcfInstAllocTop.aalloc_realizes_cf_em_m_cf TfibB IOK cf HCF walksig_cf_reply). Qed.

End b.
End a.
