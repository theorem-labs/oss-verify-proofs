(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTF.v (commit 67deba317dfb, blob 2019e7be9bb6) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj AFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR MnEnq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMdrainK DMdrainM DMdrainP DMdrainQ DMdrainG1 DMdrainG2 DMdrainG3 DMdrainG4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMdrainT1 DMdrainT2 DMdrainT3 DMdrainT4 DMdrainT5 DMdrainT7 DMdrainT8 DMdrainTA DMdrainTB DMdrainTC DMdrainTE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMsegDA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdrainMN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Hypothesis TB : TfibSyms B.
Hypothesis QV : di_qview_t B ARX L24 QB.
Hypothesis QO : di_qowned_t ARX AOX L24 QB.
Hypothesis QS : di_stack_t ARX AOX.
Hypothesis RQX : di_requar_x_t B ARX AOX L24 QB.
Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.

Lemma lb_eq : forall X, AFgj.LBv (st_qglobal X) (st_qthread X) = qc_bytes (gxf X).
Proof. intros X. unfold AFgj.LBv, AFgj.GBv, AFgj.TBv. rewrite gxf_bytes. lia. Qed.

Theorem ret_arm : forall inst ly X W regs mem md,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
qc_bytes (gxf X) <= kQuarantineMax ->
amreal tfibsegs (drain_body_cf X X) W (cfg_at tfibsegs dg_drain regs mem md)
  (DIfaceR.drain_leaf_g B ARX AOX (MnEnq.acall_raw_em_x B AOX) inst ly X W regs mem md).
Proof.
intros inst ly X W regs mem md PRE HLE.
pose proof PRE as (HAR & HTB0 & HQB & HL24 & Hra & Hra4 & Hal & Hsp1 & Hsp2 & Hpres & Hgp & Htp & Ha0 & Ha1 & Ha2).
pose proof (QV inst ly X W mem md HAR (conj HTB0 (conj HQB HL24))) as QVX.
pose proof (entry_free_hyps B ARX L24 QB TB QV QBB inst ly X W regs mem md PRE) as FH.
destruct QVX as [Qinst Qly Qimg Qtsd Qcells Qconst Qhpres Qbpres Qgeom Qnodup Qwf Qbytes Qinited].
rewrite (drain_body_cf_xfer X HLE).
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono;
[ exact (drain_entry_run W ly regs mem md (st_qglobal X) (st_qthread X) (m_vm_materialized md) FH
    (proj1 (proj2 Qwf)) (proj1 Qwf) ltac:(intros k Hk; apply (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 Qwf))));
      unfold q_items; apply in_flat_map; apply in_flat_map in Hk as (b & Hb & Hk'); exists b; split;
      [ unfold all_batches; apply in_app_iff; apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb] | exact Hk' ])) | ].
intros W' c' _ HPost.
unfold DMsegDA.postDm in HPost.
assert (HLEB : (AFgj.LBv (st_qglobal X) (st_qthread X) <=? kQuarantineMax) = true)
  by (apply Z.leb_le; rewrite (lb_eq X); exact HLE).
rewrite HLEB in HPost.
destruct HPost as (-> & regs' & mem' & mat & -> & R2 & RS & HM & HWP & HMUT & HC160 & HC168 & HC176 & HC184 & HT0 & HT8 & HT16 & HT24 & HLINK).
set (md' := with_vm_backing (m_vm_lazy md) mat md).

assert (MV1 : m_vmmaps md' = m_vmmaps md) by apply m_vmmaps_wvb.
assert (MV2 : m_vm_lazy md' = m_vm_lazy md) by apply m_vm_lazy_wvb.
assert (MV3 : eager_used md' = eager_used md) by apply eager_used_wvb.
assert (MIO : same_io md md') by apply same_io_with_vm_backing.

assert (BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize /\
  (ly_space ly + b_self b) mod 8192 = 0 /\ 0 <= ly_space ly + b_self b < ASAN_CEIL)
  by (intros b Hb; exact (DMdrainG3.baddr ly X Qly Qgeom b Hb)).
assert (Hglast2 : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  AFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X)).
{ intros lastb initr ER. split.
  - unfold AFgj.GLv. rewrite ER. reflexivity.
  - unfold all_batches. apply in_app_iff. right.
    rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity. }

assert (HLT : lcn ly (iwB B ly) (mrestrict (w_H W) mem) (qc_list (st_qthread X)) 0).
{ apply lcn_of_cells. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) Qcells).
  unfold quar_cells. right; right. apply in_app_iff. left. unfold qc_cells. do 4 right. exact Hc. }
assert (HLG : lcn ly (iwB B ly) (mrestrict (w_H W) mem) (qc_list (st_qglobal X)) 0).
{ apply lcn_of_cells. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) Qcells).
  unfold quar_cells. right; right. apply in_app_iff. right. unfold qc_cells. do 4 right. exact Hc. }
assert (HTne : qc_list (st_qthread X) <> []).
{ pose proof (DMdrainG3.T_count X Qwf Qbytes HTB0) as TC2. unfold AFgj.TSZv in TC2.
  destruct (qc_list (st_qthread X)) as [|b t]; [cbn in TC2; lia | discriminate]. }
assert (HSLOT : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 Qwf))) b Hb) as HS. destruct HS as [_ HS2]. exact HS2. }
assert (HND : List.NoDup (map b_self (all_batches X))) by (apply nodup_of_stdpp; exact Qnodup).
assert (AQB : as_inst B + o_quar = A_QUAR) by (rewrite (ts_inst _ TB); reflexivity).
assert (AQ : inst + o_quar = A_QUAR) by (rewrite Qinst; exact AQB).
unfold spZ, raZ in *.
assert (HINST : as_inst B = inst) by (rewrite Qinst; reflexivity).
assert (HQW : qc_bytes (YFeuC.transfer_g X) = AFgj.LBv (st_qglobal X) (st_qthread X))
  by (rewrite gxf_bytes; unfold AFgj.LBv, AFgj.GBv, AFgj.TBv; lia).

assert (HGT : lcn ly (iwB B ly) (mrestrict (w_H W) mem') (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) 0)
  by (eapply GT_lcn; try eassumption; try (split; [exact Hsp1 | exact Hsp2]);
      try (split; [exact (proj1 Qwf) | exact (proj1 (proj2 Qwf))])).
assert (HCELLS : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells (sxf X)))
  by (eapply cut_cells; try eassumption; try (split; [exact Hsp1 | exact Hsp2]);
      try (split; [exact (proj1 Qwf) | exact (proj1 (proj2 Qwf))])).

assert (HMUT2 : val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 152 + 2) 2 0).
{ intros k Hk. cbn in Hk. assert (Hk2 : k = 0%nat \/ k = 1%nat) by lia.
  destruct Hk2 as [-> | ->];
  [ change (YO0f.le_byte 0 2 0) with 0; replace (A_QUAR + 152 + 2 + Z.of_nat 0) with (A_QUAR + 154) by lia
  | change (YO0f.le_byte 0 2 1) with 0; replace (A_QUAR + 152 + 2 + Z.of_nat 1) with (A_QUAR + 155) by lia ];
  apply HMUT; lia. }

assert (DMQ : dmem_q B W inst ly (spZ regs) X (sxf X) [] mem mem').
{ eapply dmem_q_cut; try eassumption; try (split; [exact Hsp1 | exact Hsp2]);
    try (split; [exact (proj1 Qwf) | exact (proj1 (proj2 Qwf))]). }
destruct (RQX inst ly X W mem md (spZ regs) (sxf X) mem' md'
  HAR (conj HTB0 (conj HQB HL24)) (drain_xfer_intro X HLE) Hsp1 Hsp2 DMQ MV1 MV2 MV3) as [HARX HSHR].
assert (HGLhi : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  kHighMemBeg <= AFgj.GLv ly (st_qglobal X)).
{ intros lastb initr ER. destruct (Hglast2 lastb initr ER) as [EG HIN].
  destruct (BADDR lastb HIN) as (A1 & A2 & A3 & A4).
  pose proof (DMdrainG1.LYB2 ly Qly) as (P1 & _). rewrite EG. unfold kHighMemBeg in *. lia. }

replace (getr regs 1) with (w64 (raZ regs)) by (unfold raZ, w64; apply Z_to_bv_bv_unsigned).
eapply leaf_ret.
- exact HARX.
- splits; [exact MV1 | exact MV2 | exact MV3 | exact MIO].
- intros r Hr. unfold acallee_saved in Hr.
  assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; subst r;
  first [ exact R2
        | (apply RS; unfold AFgj.SREGS; cbn [In];
           repeat (first [ (left; first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) ]) | right ])) ].
-
  intros a Ha.
  destruct (DMdrainTE.winb ly X regs a) eqn:EW.
  + apply HWP; [exact (DMdrainTE.win_of_winb ly X regs HGLhi a EW)|].
    pose proof (DMdrainG1.LYB2 ly Qly) as (_ & _ & _ & _ & _ & _ & _ & _ & K9).
    unfold spZ in Ha. lia.
  + apply (apresent_eq (w_H W) mem mem' a); [|apply Hpres; exact Ha].
    apply HM.
    assert (HAR' : 0 <= a < 2 ^ 64).
    { unfold spZ in Ha. pose proof (u64_range (getr regs 2)).
      pose proof (DMdrainG1.LYB2 ly Qly) as (_ & _ & _ & _ & _ & _ & _ & _ & K9).
      unfold kHighMemBeg in K9. lia. }
    rewrite unsigned_lit_small by exact HAR'.
    intros HW. rewrite (DMdrainTE.win_winb ly X regs ltac:(split; [exact Hsp1 | exact Hsp2]) HGLhi a HW) in EW. discriminate.
-
  intros x A1 A2 A3. apply HM. intros HW.
  pose proof (u64_range x) as UX.
  destruct HW as [HWs | [HWf | [Hne HWa]]].
  + apply A3. unfold ascratch. left. unfold spZ. try unfold YFeuC.DSTACK in *; try unfold DSTACK in *; lia.
  + apply A1. apply (QO inst ly X W mem md (bv_unsigned x) HAR (conj HTB0 (conj HQB HL24)) UX).
    left. unfold qhdr. destruct HWf as [HQ | [HQ | HQ]];
    [ left; rewrite AQ | right; left; rewrite AQ | right; right ]; lia.
  + apply A1. apply (QO inst ly X W mem md (bv_unsigned x) HAR (conj HTB0 (conj HQB HL24)) UX).
    right. destruct (rev (qc_list (st_qglobal X))) as [|lastb initr] eqn:ER.
    * exfalso. apply Hne. rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. reflexivity.
    * destruct (Hglast2 lastb initr eq_refl) as [EG HIN].
      exists lastb. split; [exact HIN|]. unfold bobj. rewrite EG in HWa. unfold kBatchBytes. lia.
- eapply DMdrainTE.errno_keep;
  first [ exact TB | exact Qly | exact Qimg | exact HM | exact HGLhi | (split; [exact Hsp1 | exact Hsp2]) ].
-
  apply (MemnormT.memnorm_frame tfibsegs (AFgj.WIN ly regs (st_qglobal X))); [|exact HM].
  intros x HW.
  destruct HW as [HWs | [HWf | [Hne HWa]]].
  + apply (DMdrainMN.mn_safe_stk ly Qly).
    try unfold YFeuC.DSTACK in *; try unfold DSTACK in *; lia.
  + apply (DMdrainMN.mn_safe_qhdr ly Qly Qimg inst x AQ).
    unfold qhdr. destruct HWf as [HQ | [HQ | HQ]];
    [ left; rewrite AQ | right; left; rewrite AQ | right; right ]; lia.
  + destruct (rev (qc_list (st_qglobal X))) as [|lastb initr] eqn:ER.
    * exfalso. apply Hne. rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. reflexivity.
    * destruct (Hglast2 lastb initr eq_refl) as [EG HIN].
      destruct (BADDR lastb HIN) as (B1 & B2 & _).
      apply (DMdrainMN.mn_safe_bobj ly Qly lastb x B1 B2).
      unfold bobj. rewrite EG in HWa. unfold kBatchBytes. lia.
Qed.
End g.
End f.
Print Assumptions ret_arm.
