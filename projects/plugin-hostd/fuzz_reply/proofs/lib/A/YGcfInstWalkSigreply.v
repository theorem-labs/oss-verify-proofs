(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for lane W of a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply).
   reply's Allocate walk tops at image A (fuzz_reply.asan, pin 42c58610e125) assembled into YGcfInstWalkSig.WalkSigA at
   the instance YGcfInstAllocTop.v's Section hypothesis WS names: the reply twin of the cf layer's
   YGcfInstWalkSigcgif.v (commit cb7d3c39603).
   rule 24: no function proved (kind: assembly of proved Allocate arms into WalkSigA).

   The instance (YGcfInstAllocTop.v:49-50) at B := TfibB, cp := CfParams_reply (A/CfParamsReply.v): segs := im_segs (=
   tfibsegs at AImg_reply, A/AGif2reply.v:24), U := U_cf TfibB, mt := malloc_cf, ARX := ARXq_cf TfibB IOK Hp,
   AOX := AOXm_cf TfibB, rpre := YGcfRmodel.rpre_cfr TfibB, nmax := cf_malloc_max, lmax := LIVE_MAX, lpost := qtight, cf.
   reply's entry is cf_pc_allocate = 0x31bd8 (A/CfImgA.v, this file's CfImg instance) = AGhy.A_Allocate.
   reply's arm tops are cgif's with that entry: MemnormHitG.ARM_HITG_em, MemnormHitK.ARM_HITK_em,
   MemnormMissG0W.alloc_missg_cf_em, MemnormMissK0W.alloc_missk_cf_em (route-A relocations), AGioM.alloc_sec_w_em.
   Field round 3 part 3c: the two miss fields give the call state's arodata_ok_cf, which goes to the miss arms.

   The image premises of the interface instances (YGcfInstHit / YGcfInstMiss / YGcfInstMissW Section b) come from
   reply's unit facts, ReplyUnitFactsA.reply_unit_facts_A TfibB TfibB_syms: HIMG uf_IMG_COVER, HSHB uf_HSHB, HDZO uf_HDZO,
   HDZX uf_HDZX, HCW uf_HCW, HFP uf_dep_fp_img_ag, HTSD uf_HTSD, INST_AG uf_ag_inst_ok, INST_CELLS uf_INST_CELLS_t,
   EII / EDZ / ESH the errno_in_img / errno_apart_dzone_ag / errno_apart_shadow_ag conjuncts of uf_ErrnoImgCf, HEROM
   uf_errno_seg_t, HENS uf_errno_nstatic_t, ERRB_AG from uf_ERRB_SEP (its last conjunct, contraposed), oom_owned_img
   uf_oom_owned_img, oom_const_img uf_oom_const_img; HOOM / HERR from TfibSyms (ts_oom / ts_errno; the same statements
   as uf_HOOM / uf_HERR); HOEB from CfInstMiss's row ReplyImg_hoeb.hoeb_A (lib/A/ReplyImg_hoeb.v:30); the round-3 rows
   PF_AG from CfInstHit's YGcfInstHitreply.hit_pf_ag_A, HPFA / HRS from a Theorem Labs lane's ReplyRelroGeoA.pf_cells_apart_reply_A
   / relro_seg_reply_A; the secondary arm's bounds HNW / HNOB / HROOM at CfParams_reply by computation.  The
   exhausted-byte and error-buffer cells are not premises here: they are ARmcf fields (amc_cells_owned), carried by
   ARXq_cf.
   HDEP (CLdepot.depot_field at ARXq_cf, every ghost set) from YGcfInstDepot.if_depot_cf with uf_IMG_COVER,
   uf_dep_keep_img_ag (through depot_fits_incl_reply: reply's universe has no wild part), uf_dep_fp_img_ag and CfF1's row
   YGcfInstDepotWreply.depot_spec_a_reply at reply's dhash (uf_dhash_img).
   The secondary interface at the instance (IFS: AGif4.AIfaceSw at NMAXW := cf_malloc_max, NOBW := cf_nob,
   ROOMW := 2 ^ 32; IFSE: ErrnoGS.AIfaceSE) is CfInstSec's closers YGcfInstSecreply.ifaceSw_A / ifaceSE_A (IFS_reply /
   IFSE_reply below), over TfibSyms, IOK_ok, uf_IMG_COVER and uf_dhash_img.
   The refill walk HRW (refill_walk_cf TfibB IOK) is B3LeafCf's YGcfRefillTopreply.refill_walk_cf_reply_closed.
   No premise of the instance files is left named: the Section keeps only IOK / IOK_inst and the can_fill cf / HCF.
   IOK is a Variable with IOK_ok TfibB IOK (the unit's choice is ReplyAllocInst's IOK_reply).
   EVENT-FREE: no event counter, event bound, meter or regime appears in this file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The reply image instances first, as the walk files take them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseAG AGif0reply ImgBaseAGS AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AF0x AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot ErrnoApart MemnormT MnRefillW AGif0n AGif4 ErrnoGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfDIface YGcfErrbSep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstRefill YGcfInstWalkSig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstErrno YGcfInstHit YGcfInstMiss YGcfInstMissW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstAllocTop.
(* reply's unit facts *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyUnitFactsA ReplyImg_hoeb.
(* round-3 image rows of the miss / hit instances: CfInstHit's PF_AG row, a Theorem Labs lane's pf_cells_apart / relro_seg rows;
   and CfInstSec's secondary interfaces at reply A *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstHitreply ReplyRelroGeoA YGcfInstSecreply.
(* B3LeafCf's refill walk at reply A *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRefillTopreply.
(* the depot instance (lane F1's YGcfInstDepot, by path) and reply's depot walk row (CfF1) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstDepot YGcfInstDepotWreply.
(* the walk tops, used qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGhy AGioM MemnormHitG MemnormHitK MemnormMissG0W MemnormMissK0W.
Import ListNotations.
(* ErrnoGS's Require hazard (its header): restore lia's euclidean division after the Requires. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* YM05 / YM03 redefine [lia] for the run-ceiling goals; this file's arithmetic is plain. *)
Local Ltac zl := YM03.lf_lia_orig.

(* reply's CfImg instance (cf_pc_allocate = 0x31bd8, the walk tops' entry) and its allocator parameters. *)
#[local] Existing Instance CfImg_A.
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

(* The refill walk at the instance: B3LeafCf's closer at reply A (lib/A/YGcfRefillTopreply.v
   refill_walk_cf_reply_closed, the class-full arm discharged by the relocated report). *)
Lemma HRW_reply : refill_walk_cf TfibB IOK.
Proof. exact (YGcfRefillTopreply.refill_walk_cf_reply_closed TfibB IOK TfibB_syms IOK_inst). Qed.
(* ---- the image premises, from reply's unit facts ---- *)
Let TS : TfibSyms TfibB := TfibB_syms.
Let UF := ReplyUnitFactsA.reply_unit_facts_A TfibB TfibB_syms.

(* The secondary interface at the instance (AGioM.v:59 IFS at NMAXW := cf_malloc_max, NOBW := cf_nob, ROOMW := 2 ^ 32,
   and AGioM.v:67 IFSE): CfInstSec's closers at reply A (lib/A/YGcfInstSecreply.v ifaceSw_A / ifaceSE_A), whose four
   premises are TfibSyms, IOK_ok, IMG_COVER and reply's dhash (uf_dhash_img). *)
Lemma IFS_reply : forall Hp, AGif4.AIfaceSw TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow
  cf_malloc_max cf_nob (2 ^ 32).
Proof.
exact (YGcfInstSecreply.ifaceSw_A TfibB IOK TS IOK_inst (ReplyUnitFactsA.uf_IMG_COVER _ UF)
  (ReplyUnitFactsA.uf_dhash_img _ UF)).
Qed.
Lemma IFSE_reply : forall Hp, ErrnoGS.AIfaceSE TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
exact (YGcfInstSecreply.ifaceSE_A TfibB IOK TS IOK_inst (ReplyUnitFactsA.uf_IMG_COVER _ UF)
  (ReplyUnitFactsA.uf_dhash_img _ UF)).
Qed.

(* the error buffer object is outside ag_dzone: uf_ERRB_SEP's last conjunct, contraposed *)
Lemma ERRB_AG_reply : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd TfibB ->
  ag_dzone ly' a -> ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Proof.
intros ly' a LY IC HT DZ Ha.
destruct (proj2 (ReplyUnitFactsA.uf_ERRB_SEP _ UF) ly' a LY IC HT Ha) as (_ & _ & _ & NDZ). exact (NDZ DZ).
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
refine (YGcfInstDepot.if_depot_cf TfibB Hp (ARXq_cf TfibB IOK Hp) _ (ReplyUnitFactsA.uf_IMG_COVER _ UF) _
  (ReplyUnitFactsA.uf_dep_fp_img_ag _ UF)
  (YGcfInstDepotWreply.depot_spec_a_reply TfibB TS (ReplyUnitFactsA.uf_dhash_img _ UF))).
- intros inst ly S W mem md H. eapply ARX_cf_ARcf. eapply ARXq_cf_ARX. exact H.
- intros ly S W mem0 mem LY IC HT DF C D K. destruct (depot_fits_incl_reply _ DF) as (ND & INC).
  exact (ReplyUnitFactsA.uf_dep_keep_img_ag _ UF ly S W mem0 mem LY IC HT ND INC C D K).
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
  pose proof HRW_reply as HRW;
  pose proof (ReplyUnitFactsA.uf_IMG_COVER _ UF) as HIMG;
  pose proof (ReplyUnitFactsA.uf_HSHB _ UF) as HSHB;
  pose proof (ReplyUnitFactsA.uf_HDZO _ UF) as HDZO;
  pose proof (ReplyUnitFactsA.uf_HDZX _ UF) as HDZX;
  pose proof (ReplyUnitFactsA.uf_HCW _ UF) as HCW;
  pose proof (ReplyUnitFactsA.uf_dep_fp_img_ag _ UF) as HFP;
  pose proof (ReplyUnitFactsA.uf_ag_inst_ok _ UF) as INST_AG;
  pose proof (ReplyUnitFactsA.uf_INST_CELLS_t _ UF) as INST_CELLS;
  assert (HTSD : as_tsd TfibB = im_tsd) by exact (ReplyUnitFactsA.uf_HTSD _ UF);
  assert (HOOM : as_oom_byte TfibB = im_oom) by exact (ts_oom TfibB TS);
  assert (HERR : as_errno TfibB = im_errno) by exact (ts_errno TfibB TS);
  destruct (ReplyUnitFactsA.uf_ErrnoImgCf _ UF) as (EII & _ & EDZ & ESH & _);
  pose proof (ReplyUnitFactsA.uf_errno_seg_t _ UF) as HEROM;
  pose proof (ReplyUnitFactsA.uf_errno_nstatic_t _ UF) as HENS;
  pose proof ERRB_AG_reply as ERRB_AG;
  pose proof HDEP_reply as HDEP;
  pose proof (ReplyUnitFactsA.uf_oom_owned_img _ UF) as oom_owned_img;
  pose proof (ReplyUnitFactsA.uf_oom_const_img _ UF) as oom_const_img;
  pose proof (ReplyImg_hoeb.hoeb_A TfibB TS) as HOEB;
  pose proof (YGcfInstHitreply.hit_pf_ag_A TfibB TS) as PF_AG;
  pose proof (ReplyRelroGeoA.pf_cells_apart_reply_A TfibB TS) as HPFA;
  pose proof ReplyRelroGeoA.relro_seg_reply_A as HRS.

(* The walk tops' interface premises at the cf instance. *)
Lemma IF_reply : forall Hp, AGif0n.AIface TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_facts. eapply (YGcfInstHit.iface_cf TfibB IOK); eassumption. Qed.

Lemma IFK_reply : forall Hp, AGif0n.AIfaceK TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. img_facts. eapply (YGcfInstHit.ifaceK_cf TfibB IOK); eassumption. Qed.

Lemma IFM_reply : forall Hp, MnRefillW.AIfaceMw TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
  (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow
  refill_tree_cf REP_STACK.
Proof. intros Hp. img_facts. eapply (YGcfInstMissW.IFM_cfi TfibB IOK); eassumption. Qed.

Lemma RFm_reply : forall Hp,
  MnRefillW.amm_refill_w_t TfibB (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) (rpre_cf TfibB) qtight refill_tree_cf REP_STACK.
Proof. intros Hp. img_facts. eapply (YGcfInstMissW.RFm_cfi TfibB IOK); eassumption. Qed.

(* Each walk top's Section premises, in any order. *)
Local Ltac walk_args Hp :=
  first [ exact (IF_reply Hp) | exact (IFK_reply Hp) | exact (IFM_reply Hp) | exact (RFm_reply Hp)
        | exact YGcfInstMiss.REP_STACK_af | exact TS
        | exact (proj1 (ReplyUnitFactsA.uf_ErrnoImgCf _ UF))
        | exact (proj1 (proj2 (proj2 (proj2 (ReplyUnitFactsA.uf_ErrnoImgCf _ UF)))))
        | exact (proj1 (proj2 (proj2 (ReplyUnitFactsA.uf_ErrnoImgCf _ UF))))
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
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31bd8.
  eapply (MemnormHitG.ARM_HITG_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) (rpre_cf TfibB)
    cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow); walk_args Hp.
- (* wsa_hitk: MemnormHitK.ARM_HITK_em *)
  intros inst so bp ly S W regs mem md n tr l off HC HPRE Hn CI El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31bd8.
  eapply (MemnormHitK.ARM_HITK_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB) (rpre_cf TfibB)
    cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow); walk_args Hp.
- (* wsa_missg: MemnormMissG0W.alloc_missg_cf_em; the call state's arodata_ok_cf (part 3c) goes to the arm *)
  intros inst so bp ly S W regs mem md n tr HC HPRE HRO Hn El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31bd8.
  eapply (MemnormMissG0W.alloc_missg_cf_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
    (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow);
    walk_args Hp.
- (* wsa_missk: MemnormMissK0W.alloc_missk_cf_em; the call state's arodata_ok_cf (part 3c) goes to the arm *)
  intros inst so bp ly S W regs mem md n tr HC HPRE HRO Hn El.
  to_arm Hp inst so bp ly S W regs mem md n tr HPRE 0x31bd8.
  eapply (MemnormMissK0W.alloc_missk_cf_em TfibB (U_cf TfibB) malloc_cf (ARXq_cf TfibB IOK Hp) (AOX_cf TfibB)
    (rpre_cf TfibB) cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf TfibB) cf_pc_malloc_max cf_pc_spin_shadow);
    walk_args Hp.
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
