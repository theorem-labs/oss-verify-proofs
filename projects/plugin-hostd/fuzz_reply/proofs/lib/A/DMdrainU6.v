(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU6.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 2715ecee6cbe) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the instance's invariant AT THE RECYCLE CUT.  At Recycle's call
   of DoRecycle (0x33afc) the interface field DMiface.di_requar_r (DMiface.v:216-223) turns the drain's entry
   invariant into the recycle invariant: it takes the cut's memory relation (DMdrainU4.dmem_q_recyc), the
   quarantine's cells there (DMdrainU5.cut_cells_recyc) and the temp list's cells at Recycle's sp, and returns
   ARXr at the cut state together with DRq over the temp list.  This file is the bridge that assembles those
   three from what the two walks leave (YFgj.at_L0 / at_MB and DMdeq.ATDR), for BOTH arms: it is stated over
   the lists, not over a particular branch, so the no-merge arm (temp list [ex ++ popped]) and the merge arm
   (same shape with [ex] non-empty) use the one lemma.
   - [plist_cells_cut]: the temp list's four header words at Recycle's sp and its batch cells.
   - [cut_invariant]: ARXr at the cut, DRq over the temp list, and AOX's monotonicity.
   rule 24: no function proved (kind: an interface field applied at a cut of segments already walked; the
   lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle
   QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMdrainK DMdrainP DMdrainQ DMdrainG1 DMdrainU3 DMdrainU4 DMdrainU5.
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
Hypothesis RQR : di_requar_r_t B ARX ARXr AOX L24 QB DRq.

Variables (W : world tfibsegs) (ly : alayout) (X : astate) (gk : qcache) (P : list batch).
Variables (regs0 regs' : bvmap 5 word) (mem mem1 mem' : word -> option byte) (md md' : Model).
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let sp1 : Z := sp0 - 80.
Let m' := mrestrict (w_H W) mem'.
Local Notation R := (qc_list gk).
Local Notation S' := (set_qglobal gk (set_qthread qc0 X)).

(* the cut's model: the walks only materialise lazy pages (DMdeq.ATDR's with_vm_backing) *)
Hypothesis HMV1 : m_vmmaps md' = m_vmmaps md.
Hypothesis HMV2 : m_vm_lazy md' = m_vm_lazy md.
Hypothesis HMV3 : eager_used md' = eager_used md.
(* Recycle's stack pointer at the call *)
Hypothesis ESP' : bv_unsigned (getr regs' 2) = sp1.
(* the entry invariant and the drain's model premises *)
Hypothesis HAR : ARX inst ly X W mem md.
Hypothesis HPREM : dprem L24 QB X.
Hypothesis HRECYC : drain_recyc X S' P.
Hypothesis Hinst : as_inst B = inst.
Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + YFeuC.DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize /\
  (ly_space ly + b_self b) mod 8192 = 0 /\ 0 <= ly_space ly + b_self b < ASAN_CEIL.
Hypothesis HSLOT : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis Hglast : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  AFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X).
(* the cut's lists' batch objects (DMdrainU9.recyc_cut_in) *)
Hypothesis BADDR_PR : forall b, In b (P ++ R) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Hypothesis HSLOT_PR : forall b, In b (P ++ R) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
(* stage 1, the arm's walk to the loop's head (DMdrainU9.recyc_cut_in): its written set [F1], inside the
   cut's window, presence off the header, and every batch's size / count / slot words *)
Variable F1 : Z -> Prop.
Hypothesis HM1 : forall x : word, ~ F1 (bv_unsigned x) -> mem1 x = mem x.
Hypothesis HF1 : forall a, F1 a -> dwin_q inst ly sp0 X S' P a.
Hypothesis HPR1 : forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem1 a.
Hypothesis HCL1 : forall b, In b (P ++ R) ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) (addrb ly b + 8) 8 (b_bytes b) /\
  val_mem tfibsegs (mrestrict (w_H W) mem1) (addrb ly b + 16) 8 (zl (b_items b)) /\
  (forall j k, nth_error (b_items b) j = Some k ->
     val_mem tfibsegs (mrestrict (w_H W) mem1) (addrb ly b + 24 + 8 * Z.of_nat j) 8 (DMdrainK.iwB B ly k)).
(* stage 2: the dequeue loop (DMdeq.ATDR) *)
Hypothesis HM2 : forall x : word,
  ~ (sp1 <= bv_unsigned x < sp1 + 32) ->
  ~ (A_QUAR + 152 <= bv_unsigned x < A_QUAR + 156) ->
  ~ (A_QUAR + 160 <= bv_unsigned x < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= bv_unsigned x < addrb ly b + 8)) ->
  mem' x = mem1 x.
Hypothesis HPR2 : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a ->
  ~ (A_QUAR + 152 <= a < A_QUAR + 192) -> apresent (w_H W) mem' a.
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).
Hypothesis HC160 : val_mem tfibsegs m' (A_QUAR + 160) 8 (Z.of_nat (length R)).
Hypothesis HC168 : val_mem tfibsegs m' (A_QUAR + 168) 8 (fa ly R 0).
Hypothesis HC176 : val_mem tfibsegs m' (A_QUAR + 176) 8 (la ly R).
Hypothesis HC184 : val_mem tfibsegs m' (A_QUAR + 184) 8 (qc_bytes gk).
Hypothesis HPN : forall i b, nth_error P i = Some b -> val_mem tfibsegs m' (addrb ly b) 8 (next_addr ly P i).
Hypothesis HRN : forall i b, nth_error R i = Some b -> val_mem tfibsegs m' (addrb ly b) 8 (next_addr ly R i).
(* the temp list's four header words at Recycle's sp (DMdeq.ATDR, DMdeq.v:206-207) *)
Hypothesis HS0 : val_mem tfibsegs m' sp1 8 (zl P).
Hypothesis HS8 : val_mem tfibsegs m' (sp1 + 8) 8 (fa ly P 0).
Hypothesis HS16 : val_mem tfibsegs m' (sp1 + 16) 8 (la ly P).
Hypothesis HS24 : val_mem tfibsegs m' (sp1 + 24) 8 (sum_bytes P).
(* the thread cache's four header words, zero since the transfer *)
Hypothesis HT0 : val_mem tfibsegs m' (ly_T ly + t_qc) 8 0.
Hypothesis HT8 : val_mem tfibsegs m' (ly_T ly + t_qc + 8) 8 0.
Hypothesis HT16 : val_mem tfibsegs m' (ly_T ly + t_qc + 16) 8 0.
Hypothesis HT24 : val_mem tfibsegs m' (ly_T ly + t_qc + 24) 8 0.
Hypothesis HMUT2 : val_mem tfibsegs m' (A_QUAR + 152 + 2) 2 0.

Lemma baddr_PR : forall b, In b (P ++ R) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Proof. exact BADDR_PR. Qed.

Lemma slot_PR : forall b, In b (P ++ R) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Proof. exact HSLOT_PR. Qed.

Lemma frame_addr : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 <= a < sp1 + 32) -> ~ (A_QUAR + 152 <= a < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= a < addrb ly b + 8)) ->
  mem' (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a).
Proof.
intros a RA H1 H2 H3. apply HM2; rewrite (unsigned_lit_small a ltac:(lia)).
- exact H1.
- intros HH. apply H2. lia.
- intros HH. apply H2. lia.
- exact H3.
Qed.

Lemma lcn_P : lcn ly (DMdrainK.iwB B ly) m' P 0.
Proof.
assert (HSP1 : ly_stk_lo ly + AFeu.DRSTACK <= bv_unsigned (getr regs' 2) /\ bv_unsigned (getr regs' 2) + AFeu.LFRAME <= ly_stk_hi ly).
{ rewrite ESP'. unfold sp1, sp0, AFeu.DRSTACK, AFeu.LFRAME, YFeuC.DSTACK in *. destruct HSP as [S1 S2]. lia. }
assert (HFR' : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (getr regs' 2) <= a < bv_unsigned (getr regs' 2) + 32) ->
  ~ (A_QUAR + 152 <= a < A_QUAR + 192) -> (forall b, In b P -> ~ (addrb ly b <= a < addrb ly b + 8)) ->
  mem' (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a RA H1 H2 H3. rewrite ESP' in H1. exact (frame_addr a RA H1 H2 H3). }
apply (DMdrainU3.plist_lcn_c B W ly regs' mem1 mem' P R);
first [ exact LY | exact HSP1 | exact baddr_PR | exact slot_PR | exact HFR' | exact HPN | exact HRN | exact HCL1 ].
Qed.

Lemma lcn_R : lcn ly (DMdrainK.iwB B ly) m' R 0.
Proof.
assert (HSP1 : ly_stk_lo ly + AFeu.DRSTACK <= bv_unsigned (getr regs' 2) /\ bv_unsigned (getr regs' 2) + AFeu.LFRAME <= ly_stk_hi ly).
{ rewrite ESP'. unfold sp1, sp0, AFeu.DRSTACK, AFeu.LFRAME, YFeuC.DSTACK in *. destruct HSP as [S1 S2]. lia. }
assert (HFR' : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (getr regs' 2) <= a < bv_unsigned (getr regs' 2) + 32) ->
  ~ (A_QUAR + 152 <= a < A_QUAR + 192) -> (forall b, In b P -> ~ (addrb ly b <= a < addrb ly b + 8)) ->
  mem' (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a RA H1 H2 H3. rewrite ESP' in H1. exact (frame_addr a RA H1 H2 H3). }
apply (DMdrainU3.kept_lcn_c B W ly regs' mem1 mem' P R);
first [ exact LY | exact HSP1 | exact baddr_PR | exact slot_PR | exact HFR' | exact HPN | exact HRN | exact HCL1 ].
Qed.

(* The temp list's cells at Recycle's sp: its four header words and its batches. *)
Lemma plist_cells_cut : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (YFeuC.plist_cells sp1 P).
Proof.
unfold YFeuC.plist_cells, qc_cells. cbn [qc_list qc_bytes].
apply Forall_cons.
{ apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (ANum sp1) 8 _). cbn [aeval]. exact HS0. }
apply Forall_cons.
{ apply (DMdrainP.val_mem_cell B ly (w_H W) mem' (aoff (ANum sp1) 8) 8 _). cbn [aeval aoff batch_exp].
  match goal with |- val_mem _ _ ?a _ ?v =>
    replace v with (fa ly P 0) by (unfold fa, addrb; destruct P; reflexivity) end.
  exact HS8. }
apply Forall_cons.
{ apply (DMdrainP.val_mem_cell B ly (w_H W) mem' (aoff (ANum sp1) 16) 8 _). cbn [aeval aoff batch_exp].
  match goal with |- val_mem _ _ ?a _ ?v =>
    replace v with (la ly P) by (unfold la, addrb; destruct (rev P); reflexivity) end.
  exact HS16. }
apply Forall_cons.
{ apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (aoff (ANum sp1) 24) 8 _). cbn [aeval aoff]. exact HS24. }
exact (DMdrainP.batch_cells_of_lcn B ly (w_H W) mem' P lcn_P).
Qed.

(* The cut's memory relation and the quarantine's cells there. *)
Lemma cells_cut : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells S').
Proof.
exact (DMdrainU5.cut_cells_recyc B W ly X gk mem' inst Hinst AQ HMUT HC160 HC168 HC176 HC184
  HT0 HT8 HT16 HT24 lcn_R).
Qed.

Lemma dmem_cut : dmem_q B W inst ly sp0 X S' P mem mem'.
Proof.
eapply (DMdrainU4.dmem_q_recyc B W ly X S' P regs0 mem mem1 mem' inst);
first [ exact AQ | exact LY | exact HSP | exact BADDR
      | (intros b Hb; apply BADDR_PR; apply in_app_iff; left; exact Hb)
      | exact HM1 | exact HF1 | exact HPR1 | exact HM2 | exact HPR2 | exact cells_cut | exact HMUT2 ].
Qed.

(* The instance's invariant at the cut, through DMiface.di_requar_r. *)
Theorem cut_invariant :
ARXr inst ly S' W mem' md' /\ DRq S' (flat_map b_items P) (map b_self P) /\ (forall a, AOX ly S' a -> AOX ly X a).
Proof.
apply (RQR inst ly X W mem md sp0 sp1 S' P mem' md').
- exact HAR.
- exact HPREM.
- exact HRECYC.
- exact (proj1 HSP).
- exact (proj2 HSP).
- unfold sp1. unfold YFeuC.DSTACK. lia.
- unfold sp1. lia.
- exact dmem_cut.
- exact plist_cells_cut.
- exact HMV1.
- exact HMV2.
- exact HMV3.
Qed.
End g.
End f.
