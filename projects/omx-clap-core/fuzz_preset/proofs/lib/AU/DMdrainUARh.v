(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainUARh.v (commit ce1a656b52b7, file sha256 5f599c5fe325) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b): the lib/B twin of lib/A/DMdrainUARh.v by path (67deba317dfb), with lib.A -> lib.B in the Require lines and image B's names (the rows _reply_B, YGcfInstCdeallocB; CfParams_preset stays lib/A/CfParamsReply's, the one record the B files use; image B's addresses: Recycle's return after DoRecycle 0x345cc and its DoRecycle call 0x345c8, as lib/B/DMdrainUA.v / DMdrainU7Rh.v). *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b; drain-rh split row (b2), route P): the drain's SHARED RECYCLE TAIL at
   the re-hide relation - the twin of DMdrainUA.recyc_tail over amreal' (= amrealG tfibsegs (wle' tfibsegs RZ_cf),
   so a route-P instance of the generic engine at R := wle').  Every stage before DoRecycle is DMdrainUA's text
   (rewrites of the itree and facts about the cut, no world step).  DoRecycle runs at its primed contract
   (DMdrainU7Rh.dorecycle_at_cut_rh_of over DMwalkIFRh.dorecycle_ok_rh_t), Recycle's epilogue is the released machine
   segment (YG0dHc.amreal'_then_SRr, then DMdrainU8Rh.epi_after_recycle_rh), and the leaf is
   DMdrainUBRh.leaf_recyc_rh.  The re-hide shows in two places: the final world is above the entry's only off the
   dead secondaries' new shadow (wle_in (dead_shadow_new ly X Sr); the cut moves only the queues, so its set equals
   the entry's), and Drain's stack presence pulls back through it (YGcfRehidePost.wle_in_hsub_off_Z; a stack address
   is above kHighMemBeg, so off the set: dead_shadow_new_high).  A new file: DMdrainUA.v stays byte-unchanged.
   rule 24: no function proved (kind: one composition of walked segments at the primed contracts). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf YFgt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR MnEnq MnRecycle. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMdrainK DMdrainM DMdrainQ DMdrainG1 DMdrainG3 DMdrainG4 DMdrainT7.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMdrainU3 DMdrainU6 DMdrainU7 DMdrainU8 DMdrainU9 DMdrainUB DMdrainUC DMdrainUD.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMsegD DMdeq. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMdrainT5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost DIfaceRh. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIFRh DMdrainU7Rh DMdrainU8Rh DMdrainUBRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variable ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis QV : di_qview_t B ARX L24 QB.
Hypothesis QO : di_qowned_t ARX AOX L24 QB.
Hypothesis STK : di_stack_t ARX AOX.
Hypothesis FRX : di_frame_t ARX AOX.
Hypothesis FRr : di_frame_t ARXr AOX.
Hypothesis RQR : di_requar_r_t B ARX ARXr AOX L24 QB DRq.
Hypothesis RQE : di_requar_e_t ARX ARXr DRq.
Hypothesis HRM : rmaxd_ok RMAXD.
Hypothesis RV : di_rview_x_t B ARXr DRq RMAXD.
Hypothesis RCH : DIfaceRh.de_rchunk_m_rh_t B ARXr AOX DRq.
(* DoRecycle's primed contract (row (a), the DMrec* Rh chain) *)
Hypothesis DOK : DMwalkIFRh.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD.
Hypothesis CDH : MnRecycle.de_cdealloc_m_t B ARXr AOX DRq.
Hypothesis HL24 : L24 < 2 ^ 40.

Theorem recyc_tail_rh : forall inst ly X W regs mem md F1 regs1 mem1 gk P W' c',
DMdrainU9.recyc_cut_in B ARX L24 QB inst ly X W regs mem md F1 regs1 mem1 gk P W' c' ->
amreal' tfibsegs YGcfRehidePost.RZ_cf (drain_body_cf X X) W' c'
  (DIfaceRh.drain_leaf_g_rh B ARX AOX (MnEnq.acall_raw_em_x B AOX) inst ly X W regs mem md).
Proof.
intros inst ly X W regs mem md F1 regs1 mem1 gk P W' c' HIN.
unfold DMdrainU9.recyc_cut_in in HIN. cbv zeta in HIN.
destruct HIN as (PRE & HREC & HM1 & HF1 & HPR1 & BADDR_PR & HSLOT_PR & HND_PR & HOBJ & HCL1
  & S8 & S16 & S24 & S32 & S40 & S48 & T0 & T8 & T16 & T24 & ESP1 & HSRM & HR12 & HQBK & HAT).
pose proof PRE as (HAR & HTB0 & HQB & HL24x & Hra & Hra4 & Hal & Hsp1 & Hsp2 & Hpres & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in Hal, Hsp1, Hsp2, Hpres, Hra4.
pose proof (QV inst ly X W mem md HAR (conj HTB0 (conj HQB HL24x))) as QVX.
destruct QVX as [Qinst Qly Qimg Qtsd Qcells Qconst Qhpres Qbpres Qgeom Qnodup Qwf Qbytes Qinited].
assert (AQ : inst + o_quar = A_QUAR) by (rewrite Qinst, (ts_inst _ TB); reflexivity).
assert (HPREM : dprem L24 QB X) by exact (conj HTB0 (conj HQB HL24x)).
(* the model's cut *)
pose proof HREC as HREC0.
destruct HREC as (HGT & gm & ex & g' & popped & HMS & HPOP & ES' & EP).
assert (Egk : gk = g') by (apply (f_equal st_qglobal) in ES'; exact ES').
subst gk.
rewrite (DMdrainM.drain_body_cf_rec X HGT).
rewrite (DMdrainM.recycle_body_cf_run (DMdrainM.gxf X) gm ex g' popped (DMdrainM.sxf X) HMS HPOP).
replace (set_qglobal g' (DMdrainM.sxf X)) with (set_qglobal g' (set_qthread qc0 X)) by (destruct X; reflexivity).
rewrite <- EP.
(* the dequeue loop's post at DoRecycle's call *)
unfold DMdeq.ATDR in HAT. cbv zeta in HAT.
destruct HAT as (-> & regs' & mem' & mat & -> & A2 & A10 & A11 & A12 & A13 & A1 & ASR & AFR & APR & AMUT
  & A160 & A168 & A176 & A184 & APN & ARN & AS0 & AS8 & AS16 & AS24).
assert (ES1 : DMdeq.sp1 regs1 = bv_unsigned (getr regs 2) - 80) by (unfold DMdeq.sp1; exact ESP1).
set (md' := with_vm_backing (m_vm_lazy md) mat md).
pose proof (DMdrainG1.STKR ly Qly) as [K1 K2].
assert (ESP' : bv_unsigned (getr regs' 2) = bv_unsigned (getr regs 2) - 80).
{ rewrite A2, ES1. unfold w64. apply unsigned_lit_small.
  unfold YFeuC.DSTACK in Hsp1. pose proof (@YG0f.ASAN_CEIL_range _) as CR.
  unfold kHighMemBeg, kHighMemEnd in *. lia. }
assert (HM2 : forall x : word,
  ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2) - 80 + 32) ->
  ~ (A_QUAR + 152 <= bv_unsigned x < A_QUAR + 156) ->
  ~ (A_QUAR + 160 <= bv_unsigned x < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= bv_unsigned x < addrb ly b + 8)) ->
  mem' x = mem1 x).
{ intros x N1 N2 N3 N4. apply AFR. unfold DMdeq.DW. rewrite ES1.
  intros [H|[H|[H|(b & Hb & H)]]]; [exact (N1 H) | exact (N2 H) | exact (N3 H) | exact (N4 b Hb H)]. }
assert (HPR2 : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a ->
  ~ (A_QUAR + 152 <= a < A_QUAR + 192) -> apresent (w_H W) mem' a).
{ intros a RA HP HN. exact (APR a RA HP HN). }
(* the cut's facts in the tail's vocabulary *)
assert (HMV1 : m_vmmaps md' = m_vmmaps md) by reflexivity.
assert (HMV2 : m_vm_lazy md' = m_vm_lazy md) by reflexivity.
assert (HMV3 : eager_used md' = eager_used md) by reflexivity.
assert (Hinst' : as_inst B = inst) by (symmetry; exact Qinst).
assert (HSP : ly_stk_lo ly + YFeuC.DSTACK <= bv_unsigned (getr regs 2) /\ bv_unsigned (getr regs 2) <= ly_stk_hi ly)
  by (split; [exact Hsp1 | exact Hsp2]).
assert (HC160 : val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 160) 8 (Z.of_nat (length (qc_list g')))) by exact A160.
assert (HC168 : val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 168) 8 (fa ly (qc_list g') 0))
  by (destruct (qc_list g'); exact A168).
assert (HC176 : val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 176) 8 (la ly (qc_list g')))
  by (pose proof A176 as A; unfold la; unfold DMdeq.lastaddr in A; destruct (rev (qc_list g')); exact A).
assert (HC184 : val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 184) 8 (qc_bytes g')) by (rewrite HQBK; exact A184).
assert (HPN : forall i b, nth_error P i = Some b -> val_mem tfibsegs (mrestrict (w_H W) mem') (addrb ly b) 8 (next_addr ly P i))
  by exact APN.
assert (HRN : forall i b, nth_error (qc_list g') i = Some b ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (addrb ly b) 8 (next_addr ly (qc_list g') i))
  by (intros i b Hi; exact (proj1 (ARN i b Hi))).
rewrite ES1 in AS0, AS8, AS16, AS24.
assert (HS0 : val_mem tfibsegs (mrestrict (w_H W) mem') (bv_unsigned (getr regs 2) - 80) 8 (zl P)) by exact AS0.
assert (HS8 : val_mem tfibsegs (mrestrict (w_H W) mem') (bv_unsigned (getr regs 2) - 80 + 8) 8 (fa ly P 0))
  by (destruct P; exact AS8).
assert (HS16 : val_mem tfibsegs (mrestrict (w_H W) mem') (bv_unsigned (getr regs 2) - 80 + 16) 8 (la ly P))
  by (pose proof AS16 as A; unfold la; unfold DMdeq.lastaddr in A; destruct (rev P); exact A).
assert (HS24 : val_mem tfibsegs (mrestrict (w_H W) mem') (bv_unsigned (getr regs 2) - 80 + 24) 8 (sum_bytes P)) by exact AS24.
pose proof (DMdrainUD.hmut2 X W regs mem' AMUT) as HMUT2.
(* the thread header's four words survive the loop *)
assert (TQC : val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_qc) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_qc + 8) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_qc + 16) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_qc + 24) 8 0).
{ eapply DMdrainUD.tqc_call; eassumption. }
destruct TQC as (HT0 & HT8 & HT16 & HT24).
(* the instance's invariant at the cut *)
assert (CI : ARXr inst ly (set_qglobal g' (set_qthread qc0 X)) W mem' md' /\
  DRq (set_qglobal g' (set_qthread qc0 X)) (flat_map b_items P) (map b_self P) /\
  (forall a, AOX ly (set_qglobal g' (set_qthread qc0 X)) a -> AOX ly X a)).
{ eapply DMdrainU6.cut_invariant; eassumption. }
destruct CI as (HARr & HDRq & HAOXm).
(* DoRecycle's call premise *)
set (S' := set_qglobal g' (set_qthread qc0 X)) in *.
assert (ESPz : spZ regs' = bv_unsigned (getr regs 2) - 80) by exact ESP'.
assert (HSTK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S' a).
{ intros a Ha HA. exact (STK inst ly X W mem md a HAR Ha (HAOXm a HA)). }
assert (HIT : Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P).
{ apply Forall_forall. intros b Hb. apply HSLOT_PR. apply in_app_iff. left. exact Hb. }
assert (HLEN : zl P < 2 ^ 40) by (eapply DMdrainUD.len_P; eassumption).
assert (HCI : st_cache_inited S' = true) by exact Qinited.
assert (Hsp' : ly_stk_lo ly + DMwalkIF.DRSTACK_X <= spZ regs' /\ spZ regs' + 32 <= ly_stk_hi ly).
{ rewrite ESPz. unfold DMwalkIF.DRSTACK_X, YFeuC.DSTACK in *. lia. }
assert (Hal' : spZ regs' mod 16 = 0).
{ rewrite ESPz. replace (bv_unsigned (getr regs 2) - 80) with (bv_unsigned (getr regs 2) + (-5) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal. }
assert (HPS : forall a, bv_unsigned (getr regs 2) - YFeuC.DSTACK <= a < bv_unsigned (getr regs 2) ->
  apresent (w_H W) mem' a) by (eapply DMdrainUD.pres_stack; eassumption).
assert (Hpres' : forall a, spZ regs' - DMwalkIF.DRSTACK_X <= a < spZ regs' + 32 -> apresent (w_H W) mem' a).
{ intros a Ha. apply HPS. rewrite ESPz in Ha. unfold DMwalkIF.DRSTACK_X, YFeuC.DSTACK in *. lia. }
assert (HinS : forall r : bv 5, In r DMsegD.SREGS_M -> In r YFgl.SREGS)
  by (intros r Hr; unfold DMsegD.SREGS_M in Hr; unfold YFgl.SREGS; cbn [In] in Hr |- *; tauto).
assert (Hgp' : getr regs' 3 = w64 (as_gp B)).
{ rewrite (ASR 3%bv ltac:(apply HinS; unfold DMsegD.SREGS_M; cbn [In]; tauto)).
  rewrite (HSRM 3%bv ltac:(unfold DMsegD.SREGS_M; cbn [In]; tauto)). exact Hgp. }
assert (Htp' : getr regs' 4 = w64 (as_tp B)).
{ rewrite (ASR 4%bv ltac:(apply HinS; unfold DMsegD.SREGS_M; cbn [In]; tauto)).
  rewrite (HSRM 4%bv ltac:(unfold DMsegD.SREGS_M; cbn [In]; tauto)). exact Htp. }
assert (Ha0' : getr regs' 10 = w64 (inst + o_quar)) by (rewrite A10, AQ; reflexivity).
assert (Ha1' : getr regs' 11 = w64 (spZ regs')) by (rewrite A11, ES1, ESPz; reflexivity).
assert (Ha2' : getr regs' 12 = w64 (ly_T ly + t_cache)) by (rewrite A12; exact HR12).
rewrite <- ESPz in HS0, HS8, HS16, HS24.
assert (HPL : lcn ly (DMdrainK.iwB B ly) (mrestrict (w_H W) mem') P 0) by (eapply DMdrainU6.lcn_P; eassumption).
assert (DOREC : amreal' tfibsegs YGcfRehidePost.RZ_cf (do_recycle (length P) P S') W
  (cfg_at tfibsegs A_DoRecycle regs' mem' md')
  (DMwalkIFRh.dr_leaf_rh B ARXr AOX DRq inst ly S' W regs' mem' md'))
  by (eapply DMdrainU7Rh.dorecycle_at_cut_rh_of; eassumption).
(* the six words Recycle's prologue saved, carried over the loop *)
pose proof (DMdrainG1.LYB2 ly Qly) as (Ly1 & Ly2 & Ly3 & Ly4 & _).
pose proof (DMdrainT7.prim_apart ly Qly) as [_ PSTK].
assert (SV : forall off v, 32 <= off -> off + 8 <= 80 ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) (bv_unsigned (getr regs 2) - 80 + off) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (bv_unsigned (getr regs 2) - 80 + off) 8 v).
{ intros off v H1 H2 HV.
  apply (YF0x.val_mem_frame (w_H W) mem1 mem'); [|exact HV].
  intros k Hk.
  assert (RA : 0 <= bv_unsigned (getr regs 2) - 80 + off + Z.of_nat k < 2 ^ 64).
  { unfold YFeuC.DSTACK, kHighMemBeg, kHighMemEnd in *. lia. }
  apply HM2; rewrite (unsigned_lit_small _ RA).
  - lia.
  - unfold A_QUAR, A_ALLOCATOR, o_quar, YFeuC.DSTACK, kHighMemBeg in *. lia.
  - unfold A_QUAR, A_ALLOCATOR, o_quar, YFeuC.DSTACK, kHighMemBeg in *. lia.
  - intros b Hb HX. destruct (BADDR_PR b ltac:(apply in_app_iff; left; exact Hb)) as (B1 & B2 & B3 & B4).
    unfold addrb, kBatchBytes, kSpaceSize, kPrimResvSize, YFeuC.DSTACK in *. lia. }
assert (W72 : val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs' + 72) 8 (bv_unsigned (getr regs 1))).
{ rewrite ESPz. apply SV; [lia | lia |]. replace (bv_unsigned (getr regs 2) - 80 + 72) with (bv_unsigned (getr regs 2) - 8) by lia. exact S8. }
assert (W64 : val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs' + 64) 8 (bv_unsigned (getr regs 8))).
{ rewrite ESPz. apply SV; [lia | lia |]. replace (bv_unsigned (getr regs 2) - 80 + 64) with (bv_unsigned (getr regs 2) - 16) by lia. exact S16. }
assert (W56 : val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs' + 56) 8 (bv_unsigned (getr regs 9))).
{ rewrite ESPz. apply SV; [lia | lia |]. replace (bv_unsigned (getr regs 2) - 80 + 56) with (bv_unsigned (getr regs 2) - 24) by lia. exact S24. }
assert (W48 : val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs' + 48) 8 (bv_unsigned (getr regs 18))).
{ rewrite ESPz. apply SV; [lia | lia |]. replace (bv_unsigned (getr regs 2) - 80 + 48) with (bv_unsigned (getr regs 2) - 32) by lia. exact S32. }
assert (W40 : val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs' + 40) 8 (bv_unsigned (getr regs 19))).
{ rewrite ESPz. apply SV; [lia | lia |]. replace (bv_unsigned (getr regs 2) - 80 + 40) with (bv_unsigned (getr regs 2) - 40) by lia. exact S40. }
assert (W32 : val_mem tfibsegs (mrestrict (w_H W) mem') (spZ regs' + 32) 8 (bv_unsigned (getr regs 20))).
{ rewrite ESPz. apply SV; [lia | lia |]. replace (bv_unsigned (getr regs 2) - 80 + 32) with (bv_unsigned (getr regs 2) - 48) by lia. exact S48. }
assert (Hsp80 : ly_stk_lo ly + DMwalkIF.DRSTACK_X <= spZ regs' /\ spZ regs' + 80 <= ly_stk_hi ly).
{ rewrite ESPz. unfold DMwalkIF.DRSTACK_X, YFeuC.DSTACK in *. lia. }
assert (HtpT : getr regs' 4 = w64 TFIB_TP) by (rewrite Htp', (ts_tp _ TB); reflexivity).
assert (HraV : YK0s.ret_ok (w64 (bv_unsigned (getr regs 1)))) by (unfold w64; rewrite Z_to_bv_bv_unsigned; exact Hra).
assert (Hvals : 0 <= bv_unsigned (getr regs 1) < 2 ^ 64 /\ 0 <= bv_unsigned (getr regs 8) < 2 ^ 64 /\
  0 <= bv_unsigned (getr regs 9) < 2 ^ 64 /\ 0 <= bv_unsigned (getr regs 18) < 2 ^ 64 /\
  0 <= bv_unsigned (getr regs 19) < 2 ^ 64 /\ 0 <= bv_unsigned (getr regs 20) < 2 ^ 64) by (splits; apply u64_range).
(* DoRecycle, then Recycle's epilogue *)
eapply amreal'_then_SRr; [exact DOREC|].
intros r W2 c2 HL. destruct r as [[] Sr].
unfold DMwalkIFRh.dr_leaf_rh in HL. cbn [snd] in HL.
destruct HL as (regs'' & mem'' & md'' & -> & HPOST & HRAWr & HERRr & HMNr & HDRqE & HCIE & HAOXE & HPRESE).
assert (ERA : raZ regs' = 0x345cc) by (unfold raZ; rewrite A1; reflexivity).
rewrite ERA. unfold cfg_at. rewrite <- (YFhf.wvb_self md'') at 1.
eapply SRr_mono; [eapply DMdrainU8Rh.epi_after_recycle_rh; eassumption |].
intros W3 c3 _ HRET. unfold YFgt.at_RETX in HRET.
destruct HRET as (-> & regs3 & mat3 & -> & R2 & R1 & R8 & R9 & R18 & R19 & R20 & RS3).
set (md3 := with_vm_backing (m_vm_lazy md'') mat3 md'').
destruct HPOST as (HARr2 & HLLE & HWLE & HREGP & HSIO & HVIEWr & HPRESr).
(* the cut moves only the queues, so the dead-shadow set DoRecycle's post names (from the cut S') is the entry's:
   the set reads the entry state only through st_secs (the index-keyed body) *)
assert (ESS : st_secs S' = st_secs X) by (unfold S'; destruct X; reflexivity).
assert (EDS : forall a, YGcfRehidePost.dead_shadow_new ly S' Sr a <-> YGcfRehidePost.dead_shadow_new ly X Sr a)
  by (intros a; unfold YGcfRehidePost.dead_shadow_new; rewrite ESS; reflexivity).
assert (HWLEX : wle_in tfibsegs (YGcfRehidePost.dead_shadow_new ly X Sr) W W2)
  by (eapply wle_in_mono; [intros a Ha; exact (proj1 (EDS a) Ha) | exact HWLE]).
(* the invariant at the end *)
assert (HARX : ARX inst ly Sr W2 mem'' md3).
{ pose proof (RQE inst ly Sr W2 mem'' md'' HARr2 HDRqE) as HA0.
  apply (FRX inst ly Sr W2 mem'' md'' mem'' md3 HA0); [intros; reflexivity | intros; assumption
    | reflexivity | reflexivity | reflexivity | intros; reflexivity]. }
assert (HSHR : forall a, AOX ly Sr a -> AOX ly X a) by (intros a HA; exact (HAOXm a (HAOXE a HA))).
assert (HMD : same_io md md3).
{ apply (YFhf.same_io_trans md md'' md3); [apply (YFhf.same_io_trans md md' md''); [apply YFhf.same_io_with_vm_backing | exact HSIO]
  | apply YFhf.same_io_with_vm_backing]. }
(* the registers Drain returns with *)
assert (ESP'' : spZ regs'' = spZ regs').
{ unfold spZ. exact (f_equal bv_unsigned (HREGP 2 ltac:(unfold acallee_saved; lia))). }
assert (KS : forall r, In r [3; 4; 21; 22; 23; 24; 25; 26; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hr1 : In (Z_to_bv 5 r) YFgt.SREGS) by (cbn [In] in Hr; unfold YFgt.SREGS; cbn [In];
    repeat destruct Hr as [<-|Hr]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right])).
  assert (Hr2 : In (Z_to_bv 5 r) YFgl.SREGS) by (cbn [In] in Hr; unfold YFgl.SREGS; cbn [In];
    repeat destruct Hr as [<-|Hr]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right])).
  assert (Hr3 : In (Z_to_bv 5 r) DMsegD.SREGS_M) by (cbn [In] in Hr; unfold DMsegD.SREGS_M; cbn [In];
    repeat destruct Hr as [<-|Hr]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right])).
  assert (Hr4 : acallee_saved r) by (unfold acallee_saved; cbn [In] in Hr; lia).
  rewrite (RS3 _ Hr1), (HREGP r Hr4), (ASR _ Hr2), (HSRM _ Hr3). reflexivity. }
assert (HREG : aregs_preserved regs regs3).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ In r [3; 4; 21; 22; 23; 24; 25; 26; 27])
    by (cbn [In]; lia).
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | Hc]]]]]].
  - assert (E2 : w64 (bv_unsigned (getr regs'' 2) + YFeu.LFRAME) = getr regs 2).
    { fold (spZ regs''). rewrite ESP'', ESPz. unfold YFeu.LFRAME.
      replace (bv_unsigned (getr regs 2) - 80 + 80) with (bv_unsigned (getr regs 2)) by lia.
      unfold w64. apply Z_to_bv_bv_unsigned. }
    exact (eq_trans R2 E2).
  - exact (eq_trans R8 (Z_to_bv_bv_unsigned _ _)).
  - exact (eq_trans R9 (Z_to_bv_bv_unsigned _ _)).
  - exact (eq_trans R18 (Z_to_bv_bv_unsigned _ _)).
  - exact (eq_trans R19 (Z_to_bv_bv_unsigned _ _)).
  - exact (eq_trans R20 (Z_to_bv_bv_unsigned _ _)).
  - exact (KS r Hc). }
(* the stage-1 + loop frame against the entry, and its two keeps (DMdrainUC) *)
assert (BADDR_X : forall b, In b (all_batches X) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL) by (intros b Hb; exact (DMdrainG3.baddr ly X Qly Qgeom b Hb)).
assert (HSLOT_X : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. destruct Qwf as (_ & _ & W3 & _). exact (proj2 (proj1 (Forall_forall _ _) W3 b Hb)). }
assert (CRAW : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ ascratch B YFeuC.DSTACK regs (bv_unsigned x) -> mem' x = mem x).
{ eapply DMdrainUC.cut_raw with (P := P) (gk := g') (F1 := F1) (mem1 := mem1); eassumption. }
assert (CERR : ErrnoG.errno_kept B mem mem')
  by (eapply DMdrainUC.cut_errno with (P := P) (gk := g') (F1 := F1) (mem1 := mem1); eassumption).
assert (CMN : MemnormT.memnorm_keep tfibsegs mem mem')
  by (eapply DMdrainUC.cut_memnorm with (P := P) (gk := g') (F1 := F1) (mem1 := mem1); eassumption).
(* DoRecycle's scratch and extra window are inside Drain's scratch *)
pose proof (ts_errno _ TB) as EE.
assert (SCR : forall a, ~ ascratch B YFeuC.DSTACK regs a ->
  ~ ascratch B DMwalkIF.DRSTACK_X regs' a /\ ~ (spZ regs' <= a < spZ regs' + 32)).
{ intros a HN. unfold ascratch in *. rewrite ESPz. unfold spZ in HN.
  split; intros H; apply HN; unfold DMwalkIF.DRSTACK_X, YFeuC.DSTACK in *; lia. }
unfold DIfaceR.acall_raw_x in HRAWr.
assert (HRAW : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ AOX ly Sr (bv_unsigned x) ->
  ~ ascratch B YFeuC.DSTACK regs (bv_unsigned x) -> mem'' x = mem x).
{ intros x H1 H2 H3. destruct (SCR _ H3) as [H4 H5].
  rewrite (HRAWr x (fun H => H1 (HAOXm _ H)) H2 H4 H5). exact (CRAW x H1 H3). }
assert (HVIEW : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X a -> ~ AOX ly Sr a ->
  ~ ascratch B YFeuC.DSTACK regs a -> ~ YGcfRehidePost.dead_shadow_new ly X Sr a ->
  aview tfibsegs (w_H W2) mem'' a = aview tfibsegs (w_H W) mem a).
{ intros a RA H1 H2 H3 H6. destruct (SCR _ H3) as [H4 H5].
  etransitivity; [exact (HVIEWr a RA (fun H => H1 (HAOXm _ H)) H2 H4 H5 (fun H => H6 (proj1 (EDS a) H)))|].
  apply DMdrainT5.aview_of_raw. apply CRAW; rewrite (unsigned_lit_small a RA); assumption. }
assert (HPRES : forall a, spZ regs - YFeuC.DSTACK <= a < spZ regs -> apresent (w_H W2) mem'' a).
{ intros a Ha. unfold spZ in Ha.
  destruct (DMdrainU2.zrange_dec (spZ regs' - DMwalkIF.DRSTACK_X) a (spZ regs')) as [HA|HA];
  [exact (HPRESr a HA)|].
  destruct (DMdrainU2.zrange_dec (spZ regs') a (spZ regs' + 32)) as [HB|HB]; [exact (HPRESE a HB)|].
  assert (RA : 0 <= a < 2 ^ 64) by (unfold YFeuC.DSTACK, kHighMemBeg, kHighMemEnd in *; lia).
  assert (HS : ly_stk_lo ly <= a < ly_stk_hi ly) by (unfold YFeuC.DSTACK in *; lia).
  destruct (HPS a ltac:(lia)) as [Hh [b Hb]].
  split.
  - destruct (w_H W2 (Z_to_bv 64 a)) eqn:E2; [|reflexivity].
    (* a stack address is above kHighMemBeg, so off the re-hidden shadow *)
    assert (NDS : ~ YGcfRehidePost.dead_shadow_new ly S' Sr a)
      by (apply YGcfRehidePost.dead_shadow_new_high; unfold YFeuC.DSTACK, kHighMemBeg, kHighMemEnd in *; lia).
    exfalso. assert (HF : w_H W (Z_to_bv 64 a) = true)
      by exact (YGcfRehidePost.wle_in_hsub_off_Z _ _ W W2 a RA HWLE NDS E2).
    assert (HG : w_H W (Z_to_bv 64 a) = false) by exact Hh. rewrite HF in HG. discriminate.
  - exists b. rewrite <- Hb. apply HRAWr.
    + rewrite (unsigned_lit_small a RA). exact (HSTK a HS).
    + rewrite (unsigned_lit_small a RA). intros HO. exact (HSTK a HS (HAOXE a HO)).
    + rewrite (unsigned_lit_small a RA). unfold ascratch. rewrite EE. intros [H|H].
      * apply HA. exact H.
      * unfold TFIB_ERRNO, YFeuC.DSTACK, kHighMemBeg in *. lia.
    + rewrite (unsigned_lit_small a RA). exact HB. }
assert (HERR : ErrnoG.errno_kept B mem mem'') by (intros i Hi; exact (eq_trans (HERRr i Hi) (CERR i Hi))).
assert (HMN : MemnormT.memnorm_keep tfibsegs mem mem'') by (intros H; exact (HMNr (CMN H))).
change (mkCfg (mkst regs3 (w64 (bv_unsigned (getr regs 1))) mem'' (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs (raZ regs) regs3 mem'' md3).
eapply DMdrainUBRh.leaf_recyc_rh; eassumption.
Qed.
End g.
End f.
