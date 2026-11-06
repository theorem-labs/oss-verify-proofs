(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainTF.v (commit ce1a656b52b7, file sha256 7eeb4e500d41) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTF.v (commit 68fe993efc49, Quarantine::Drain walk set; file sha256 55fbc5d0fb6a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTF.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the drain's RETURN ARM end to end - when the transferred
   quarantine is within kQuarantineMax, Quarantine::Drain's walk from 0x342b8 reaches its return and the whole
   tree is the transfer, so the arm gives DIfaceR.drain_leaf_g at MnEnq.acall_raw_em_x, the form
   MnDrain.de_drain_m_t takes.
   The pieces: DMdrainG4.entry_free_hyps (the shell's premise from qview), DMdrainT1.drain_entry_run (the walk to
   DMsegD.postDm), YFgj.at_RETD on this branch, DMdrainTC.dmem_q_cut (the cut's memory relation),
   DMiface.di_requar_x (ARX at the transferred state), DMdrainTE's errno / memnorm keeps, DMdrainT5.leaf_ret
   (the leaf), and DMdrainM.drain_body_cf_xfer (the model's cut).
   rule 24: no function proved (kind: composition of segments already walked; the lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR MnEnq. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMdrainK DMdrainM DMdrainP DMdrainQ DMdrainG1 DMdrainG2 DMdrainG3 DMdrainG4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMdrainT1 DMdrainT2 DMdrainT3 DMdrainT4 DMdrainT5 DMdrainT7 DMdrainT8 DMdrainTA DMdrainTB DMdrainTC DMdrainTE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMsegD. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMdrainMN.
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
(* No premise on the quarantine's header presence: DMiface.dmem_q's presence clause is stated for 0 <= a < 2^64
   only, and in that range it excludes the header words (DMiface.v:121-125), so DMdrainTC.dmem_q_cut needs none. *)

(* the transferred bytes are the two caches' (DMdrainM.gxf_bytes) in the shell's vocabulary *)
Lemma lb_eq : forall X, YFgj.LBv (st_qglobal X) (st_qthread X) = qc_bytes (gxf X).
Proof. intros X. unfold YFgj.LBv, YFgj.GBv, YFgj.TBv. rewrite gxf_bytes. lia. Qed.

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
unfold DMsegD.postDm in HPost.
assert (HLEB : (YFgj.LBv (st_qglobal X) (st_qthread X) <=? kQuarantineMax) = true)
  by (apply Z.leb_le; rewrite (lb_eq X); exact HLE).
rewrite HLEB in HPost.
destruct HPost as (-> & regs' & mem' & mat & -> & R2 & RS & HM & HWP & HMUT & HC160 & HC168 & HC176 & HC184 & HT0 & HT8 & HT16 & HT24 & HLINK).
set (md' := with_vm_backing (m_vm_lazy md) mat md).
(* the model facts of the walk's Model *)
assert (MV1 : m_vmmaps md' = m_vmmaps md) by apply m_vmmaps_wvb.
assert (MV2 : m_vm_lazy md' = m_vm_lazy md) by apply m_vm_lazy_wvb.
assert (MV3 : eager_used md' = eager_used md) by apply eager_used_wvb.
assert (MIO : same_io md md') by apply same_io_with_vm_backing.
(* the batches' geometry, from qview *)
assert (BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize /\
  (ly_space ly + b_self b) mod 8192 = 0 /\ 0 <= ly_space ly + b_self b < ASAN_CEIL)
  by (intros b Hb; exact (DMdrainG3.baddr ly X Qly Qgeom b Hb)).
assert (Hglast2 : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  YFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X)).
{ intros lastb initr ER. split.
  - unfold YFgj.GLv. rewrite ER. reflexivity.
  - unfold all_batches. apply in_app_iff. right.
    rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity. }
(* the two caches, linked, at the entry *)
assert (HLT : lcn ly (iwB B ly) (mrestrict (w_H W) mem) (qc_list (st_qthread X)) 0).
{ apply lcn_of_cells. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) Qcells).
  unfold quar_cells. right; right. apply in_app_iff. left. unfold qc_cells. do 4 right. exact Hc. }
assert (HLG : lcn ly (iwB B ly) (mrestrict (w_H W) mem) (qc_list (st_qglobal X)) 0).
{ apply lcn_of_cells. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) Qcells).
  unfold quar_cells. right; right. apply in_app_iff. right. unfold qc_cells. do 4 right. exact Hc. }
assert (HTne : qc_list (st_qthread X) <> []).
{ pose proof (DMdrainG3.T_count X Qwf Qbytes HTB0) as TC2. unfold YFgj.TSZv in TC2.
  destruct (qc_list (st_qthread X)) as [|b t]; [cbn in TC2; lia | discriminate]. }
assert (HSLOT : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 Qwf))) b Hb) as HS. destruct HS as [_ HS2]. exact HS2. }
assert (HND : List.NoDup (map b_self (all_batches X))) by (apply nodup_of_stdpp; exact Qnodup).
assert (AQB : as_inst B + o_quar = A_QUAR) by (rewrite (ts_inst _ TB); reflexivity).
assert (AQ : inst + o_quar = A_QUAR) by (rewrite Qinst; exact AQB).
unfold spZ, raZ in *.
assert (HINST : as_inst B = inst) by (rewrite Qinst; reflexivity).
assert (HQW : qc_bytes (YFeuC.transfer_g X) = YFgj.LBv (st_qglobal X) (st_qthread X))
  by (rewrite gxf_bytes; unfold YFgj.LBv, YFgj.GBv, YFgj.TBv; lia).
(* the joined list and the cells at the cut *)
assert (HGT : lcn ly (iwB B ly) (mrestrict (w_H W) mem') (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) 0)
  by (eapply GT_lcn; try eassumption; try (split; [exact Hsp1 | exact Hsp2]);
      try (split; [exact (proj1 Qwf) | exact (proj1 (proj2 Qwf))])).
assert (HCELLS : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells (sxf X)))
  by (eapply cut_cells; try eassumption; try (split; [exact Hsp1 | exact Hsp2]);
      try (split; [exact (proj1 Qwf) | exact (proj1 (proj2 Qwf))])).
(* the two bytes after the mutex word *)
assert (HMUT2 : val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 152 + 2) 2 0).
{ intros k Hk. cbn in Hk. assert (Hk2 : k = 0%nat \/ k = 1%nat) by lia.
  destruct Hk2 as [-> | ->];
  [ change (YO0f.le_byte 0 2 0) with 0; replace (A_QUAR + 152 + 2 + Z.of_nat 0) with (A_QUAR + 154) by lia
  | change (YO0f.le_byte 0 2 1) with 0; replace (A_QUAR + 152 + 2 + Z.of_nat 1) with (A_QUAR + 155) by lia ];
  apply HMUT; lia. }
(* the cut's memory relation, and with it ARX at the transferred state *)
assert (DMQ : dmem_q B W inst ly (spZ regs) X (sxf X) [] mem mem').
{ eapply dmem_q_cut; try eassumption; try (split; [exact Hsp1 | exact Hsp2]);
    try (split; [exact (proj1 Qwf) | exact (proj1 (proj2 Qwf))]). }
destruct (RQX inst ly X W mem md (spZ regs) (sxf X) mem' md'
  HAR (conj HTB0 (conj HQB HL24)) (drain_xfer_intro X HLE) Hsp1 Hsp2 DMQ MV1 MV2 MV3) as [HARX HSHR].
assert (HGLhi : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  kHighMemBeg <= YFgj.GLv ly (st_qglobal X)).
{ intros lastb initr ER. destruct (Hglast2 lastb initr ER) as [EG HIN].
  destruct (BADDR lastb HIN) as (A1 & A2 & A3 & A4).
  pose proof (DMdrainG1.LYB2 ly Qly) as (P1 & _). rewrite EG. unfold kHighMemBeg in *. lia. }
(* the leaf *)
replace (getr regs 1) with (w64 (raZ regs)) by (unfold raZ, w64; apply Z_to_bv_bv_unsigned).
eapply leaf_ret.
- exact HARX.
- splits; [exact MV1 | exact MV2 | exact MV3 | exact MIO].
- intros r Hr. unfold acallee_saved in Hr.
  assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; subst r;
  first [ exact R2
        | (apply RS; unfold YFgj.SREGS; cbn [In];
           repeat (first [ (left; first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) ]) | right ])) ].
- (* the stack window is present at the cut *)
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
- (* the raw frame: everything the walk writes is owned at the entry or is Drain's own frame *)
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
- (* memnorm: every word the walk writes is mn_safe at the image (DMdrainMN) *)
  apply (MemnormT.memnorm_frame tfibsegs (YFgj.WIN ly regs (st_qglobal X))); [|exact HM].
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
