(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainV0.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 73a9ec74dbb5) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the NO-MERGE arm to the shared recycle tail's input.  From
   Quarantine::Drain's entry at 0x337ec, on the arm where the quarantine is over kQuarantineMax and Recycle's merge
   test fails (DMsegD.merge_test = false, the third outcome of DMsegD.postDm), the walk reaches Recycle's call of
   DoRecycle with DMdrainU9.recyc_cut_in: stage 1 is Drain's entry walk (written set YFgj.WIN, YFgj.at_L0), stage
   2 the released dequeue loop DMdeq.tfib_deq_ok, the model's cut DMiface.drain_recyc with gm the transferred
   quarantine and ex = [] (DMdrainM.merge_split_cf_triv).
   Chain: DMdrainG4.entry_free_hyps -> DMdrainT1.drain_entry_run -> at_L0 -> DMdrainN.deq_pre_nomerge (with the
   joined list from DMdrainTA.GT_lcn) -> DMdeq.tfib_deq_ok -> DMdeq.ATDR, then the input's conjuncts.
   - [pop_split]: the dequeue pops the front of the list, so the popped and the kept batches make up the list,
     and a cache whose byte count is its list's weight keeps that property.
   rule 24: proves function __sanitizer::Quarantine::Drain (no-merge arm, entry to DoRecycle's call),
   frame-generic over ARX; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches
   Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM.
   Additive: moved here from DMdrainU2.v, whose helpers it uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMdrainK DMdrainQ DMdrainG1 DMdrainG3 DMdrainG4 DMdrainT1 DMdrainTA DMdrainN.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMdrainU2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMdrainM DMdrainU4 DMdrainU9.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMsegD DMdeq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The dequeue pops the front of the list: what it pops and what it keeps make up the list, and a cache whose
   byte count is its list's weight keeps that property. *)
Lemma pop_split_acc : forall f q acc g' popped, pop_batches f q acc = (g', popped) ->
  popped ++ qc_list g' = rev acc ++ qc_list q /\
  (qc_bytes q = sum_bytes (qc_list q) -> qc_bytes g' = sum_bytes (qc_list g')).
Proof.
induction f as [|f IH]; intros q acc g' popped H; cbn [pop_batches] in H.
- injection H as <- <-. split; [reflexivity | auto].
- destruct (qc_bytes q <=? kQuarantineMin).
  + injection H as <- <-. split; [reflexivity | auto].
  + destruct (qc_list q) as [|b t] eqn:EQ.
    * injection H as <- <-. rewrite EQ. split; [reflexivity | intros HB; exact HB].
    * destruct (IH _ _ _ _ H) as [E1 E2]. split.
      { rewrite E1. cbn [qc_list rev]. rewrite <- app_assoc. reflexivity. }
      { intros HB. apply E2. cbn [qc_bytes qc_list]. rewrite HB, AFey.sum_bytes_cons. lia. }
Qed.

Lemma pop_split : forall f q g' popped, pop_batches f q [] = (g', popped) ->
  popped ++ qc_list g' = qc_list q /\ (qc_bytes q = sum_bytes (qc_list q) -> qc_bytes g' = sum_bytes (qc_list g')).
Proof. intros f q g' popped H. exact (pop_split_acc f q [] g' popped H). Qed.

Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Hypothesis TB : TfibSyms B.
Hypothesis QV : di_qview_t B ARX L24 QB.
Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.

Theorem nomerge_to_call : forall inst ly X W regs mem md mat,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
kQuarantineMax < AFgj.LBv (st_qglobal X) (st_qthread X) ->
DMsegD.merge_test (st_qglobal X) (st_qthread X) = false ->
SRr tfibsegs W (mkCfg (mkst regs (w64 0x337ec) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => exists F1 regs1 mem1 gk P,
   DMdrainU9.recyc_cut_in B ARX L24 QB inst ly X W regs mem md F1 regs1 mem1 gk P W' c').
Proof.
intros inst ly X W regs mem md mat PRE HGT HMT.
pose proof PRE as (HAR & HTB0 & HQB & HL24 & Hra & Hra4 & Hal & Hsp1 & Hsp2 & Hpres & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *.
pose proof (QV inst ly X W mem md HAR (conj HTB0 (conj HQB HL24))) as QVX.
destruct QVX as [Qinst Qly Qimg Qtsd Qcells Qconst Qhpres Qbpres Qgeom Qnodup Qwf Qbytes Qinited].
pose proof (entry_free_hyps B ARX L24 QB TB QV QBB inst ly X W regs mem md PRE) as FH.
pose proof (DMdrainG1.STKR ly Qly) as [K1 K2].
pose proof (u64_range (getr regs 2)) as U2.
assert (AQ : as_inst B + o_quar = A_QUAR) by (rewrite (ts_inst _ TB); reflexivity).
(* the batches' non-negative sizes, over the joined list's order *)
assert (HNN : forall k, In k (flat_map b_items (qc_list (st_qglobal X) ++ qc_list (st_qthread X))) -> 0 <= ck_n k).
{ intros k Hk. destruct Qwf as (_ & _ & _ & W4). apply (proj1 (Forall_forall _ _) W4).
  unfold q_items. apply in_flat_map in Hk as (b & Hb & Hk). apply in_flat_map. exists b. split; [|exact Hk].
  unfold all_batches. apply in_app_iff. apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb]. }
eapply SRr_bind;
[ exact (drain_entry_run W ly regs mem md (st_qglobal X) (st_qthread X) mat FH
    (proj1 (proj2 Qwf)) (proj1 Qwf) HNN) | ].
intros W' c' _ HPost.
unfold DMsegD.postDm in HPost.
assert (HLEB : (AFgj.LBv (st_qglobal X) (st_qthread X) <=? kQuarantineMax) = false) by (apply Z.leb_gt; exact HGT).
rewrite HLEB, HMT in HPost. cbv zeta in HPost.
destruct HPost as (-> & regs1 & mem1 & mat1 & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS
  & HM & HPR & CQW & CQS & CQF & CQL & CQB & CT0 & CT8 & CT16 & CT24 & HLINK
  & V80 & V72 & V64 & V56 & V48 & V40 & V32 & V24 & V16 & V8).
(* the loop's stack pointer *)
assert (ESP : bv_unsigned (getr regs1 2) = bv_unsigned (getr regs 2) - 80).
{ rewrite R2. unfold w64. apply unsigned_lit_small.
  unfold YFeuC.DSTACK in Hsp1. pose proof (@YG0f.ASAN_CEIL_range _) as CR.
  unfold kHighMemBeg, kHighMemEnd in *. lia. }
(* the thread list is not empty: the drain is entered over the thread cache's max *)
pose proof (DMdrainG3.T_count X Qwf Qbytes HTB0) as HTcnt.
assert (HTne : qc_list (st_qthread X) <> []).
{ intros E. unfold AFgj.TSZv in HTcnt. rewrite E in HTcnt. cbn [length] in HTcnt. lia. }
(* the entry memory's two linked lists *)
pose proof (DMdrainG3.G_lcn B ly X W mem Qcells) as HLG.
assert (HLT : lcn ly (DMdrainK.iwB B ly) (mrestrict (w_H W) mem) (qc_list (st_qthread X)) 0).
{ apply (DMdrainK.lcn_of_cells B ly (w_H W) mem). apply Forall_forall. intros c Hc.
  apply (proj1 (Forall_forall _ _) Qcells). unfold quar_cells. right; right.
  apply in_app_iff. left. unfold qc_cells. do 4 right. exact Hc. }
pose proof (DMdrainG3.baddr ly X Qly Qgeom) as BADDR.
assert (HSLOT : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. destruct Qwf as (_ & _ & W3 & _). exact (proj2 (proj1 (Forall_forall _ _) W3 b Hb)). }
assert (HNDa : List.NoDup (map b_self (all_batches X))) by (apply DMdrainQ.nodup_of_stdpp; exact Qnodup).
(* the joined list at the loop's entry *)
pose proof (DMdrainTA.GT_lcn B W ly X regs mem mem1 HM HLINK HLG HLT HTne Qly (conj Hsp1 Hsp2)
  BADDR HSLOT HNDa (conj (proj1 Qwf) (proj1 (proj2 Qwf)))) as CLK.
(* the dequeue loop's premise *)
assert (HBF : forall b, In b (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ kBatchBytes <= b_bytes b).
{ intros b Hb.
  assert (Ha : In b (all_batches X))
    by (unfold all_batches; apply in_app_iff; apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb]).
  destruct (BADDR b Ha) as (A1 & A2 & A3 & _). unfold addrb. splits; try assumption.
  apply DMdrainQ.b_bytes_lb. intros k Hk. apply HNN. apply in_flat_map. exists b. split; [exact Hb | exact Hk]. }
assert (HNDl : List.NoDup (map b_self (qc_list (st_qglobal X) ++ qc_list (st_qthread X)))).
{ rewrite map_app. unfold all_batches in HNDa. rewrite map_app in HNDa.
  apply (Permutation_NoDup (l := map b_self (qc_list (st_qthread X)) ++ map b_self (qc_list (st_qglobal X))));
  [apply Permutation_app_comm | exact HNDa]. }
assert (HSUM : sum_bytes (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) <= 2 ^ 31).
{ rewrite DMdrainQ.sum_bytes_app_q. destruct Qwf as (W1 & W2 & _). rewrite <- W1, <- W2. lia. }
assert (HPRS : forall a, bv_unsigned (getr regs1 2) - AFeu.DRSTACK <= a < bv_unsigned (getr regs1 2) + AFeu.LFRAME ->
  apresent (w_H W) mem1 a).
{ intros a Ha. rewrite ESP in Ha. unfold AFeu.DRSTACK, AFeu.LFRAME in Ha.
  assert (HA0 : bv_unsigned (getr regs 2) - YFeuC.DSTACK <= a < bv_unsigned (getr regs 2))
    by (unfold YFeuC.DSTACK; lia).
  pose proof (Hpres a HA0) as P0.
  destruct (win_dec ly regs (st_qglobal X) a) as [HW|HW].
  - apply (HPR a HW). unfold YFeuC.DSTACK in Hsp1. unfold kHighMemBeg in *. lia.
  - apply (AF0x.apresent_same (w_H W) mem mem1 a); [|exact P0].
    apply HM. rewrite unsigned_lit_small; [exact HW|].
    unfold YFeuC.DSTACK in Hsp1. pose proof (@YG0f.ASAN_CEIL_range _) as CR.
    unfold kHighMemBeg, kHighMemEnd in *. lia. }
pose proof FH as FH2.
destruct FH2 as [fLY fIMG fHtp fHra fHra4 fHsp fHal fHpres fHg fHt fHglast fSEED].
assert (HLSZ : AFgj.LSZv (st_qglobal X) (st_qthread X) =
  Z.of_nat (length (qc_list (st_qglobal X) ++ qc_list (st_qthread X)))) by apply lsz_len.
assert (HLF : AFgj.LFv ly (st_qglobal X) (st_qthread X) =
  fa ly (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) 0) by apply lf_fa.
assert (HTL : AFgj.TLv ly (st_qthread X) = la ly (qc_list (st_qglobal X) ++ qc_list (st_qthread X)))
  by (apply tl_la; exact HTne).
assert (HLB : AFgj.LBv (st_qglobal X) (st_qthread X) =
  sum_bytes (qc_list (st_qglobal X) ++ qc_list (st_qthread X)))
  by (apply lb_sum; [exact (proj1 (proj2 Qwf)) | exact (proj1 Qwf)]).
rewrite HLSZ in R16, CQS. rewrite HLF in R5, CQF. rewrite HTL in CQL. rewrite HLB in CQB.
pose proof (deq_pre_nomerge W ly regs1 mem1 (qc_list (st_qglobal X) ++ qc_list (st_qthread X))
  (DMdrainK.iwB B ly) Qly HBF HNDl HSUM
  ltac:(rewrite ESP; unfold AFeu.DRSTACK, AFeu.LFRAME, YFeuC.DSTACK in *; lia)
  ltac:(rewrite ESP; replace (bv_unsigned (getr regs 2) - 80) with (bv_unsigned (getr regs 2) + (-5) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hal)
  HPRS
  ltac:(rewrite (RS 4%bv ltac:(unfold AFgj.SREGS; cbn [In]; tauto)); exact fHtp)
  ltac:(rewrite R1; exact fHra)
  R10 R11 R14 R15 R16 R5 CQW CQS CQF CQL CQB
  ltac:(rewrite ESP; replace (bv_unsigned (getr regs 2) - 80 + 8) with (bv_unsigned (getr regs 2) - 72) by lia; exact V72)
  ltac:(rewrite ESP; replace (bv_unsigned (getr regs 2) - 80 + 24) with (bv_unsigned (getr regs 2) - 56) by lia; exact V56)
  CLK) as DP.
(* the released dequeue loop *)
assert (EQL : qc_list (AFeu.transfer_g X) = qc_list (st_qglobal X) ++ qc_list (st_qthread X)) by reflexivity.
assert (EQB : qc_bytes (AFeu.transfer_g X) = sum_bytes (qc_list (st_qglobal X) ++ qc_list (st_qthread X))).
{ cbn [AFeu.transfer_g qc_bytes]. rewrite DMdrainQ.sum_bytes_app_q.
  destruct Qwf as (W1 & W2 & _). rewrite <- W1, <- W2. reflexivity. }
assert (HMIN : kQuarantineMin < qc_bytes (AFeu.transfer_g X)).
{ rewrite EQB, <- HLB. unfold kQuarantineMin, kQuarantineMax in *. lia. }
eapply SRr_mono;
[ exact (DMdeq.tfib_deq_ok W ly md regs1 mem1 mat1 [] (qc_list (st_qglobal X) ++ qc_list (st_qthread X))
    (AFeu.transfer_g X) DP EQL EQB HMIN) | ].
intros W2 c2 _ (g' & popped & HPB & HAT). cbn [app] in HAT.
rewrite EQL in HPB.
pose proof (pop_split _ _ _ _ HPB) as [HSPL HBYT].
assert (HSPL' : popped ++ qc_list g' = qc_list (st_qglobal X) ++ qc_list (st_qthread X)) by (rewrite HSPL; reflexivity).
assert (Hglast : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  AFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X)).
{ intros lastb initr ER. split.
  - unfold AFgj.GLv. rewrite ER. reflexivity.
  - unfold all_batches. apply in_app_iff. right.
    rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity. }
assert (AQi : inst + o_quar = A_QUAR) by (rewrite Qinst; exact AQ).
assert (HinGT : forall b, In b (popped ++ qc_list g') -> In b (all_batches X)).
{ intros b Hb. rewrite HSPL' in Hb. unfold all_batches. apply in_app_iff.
  apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb]. }
exists (AFgj.WIN ly regs (st_qglobal X)), regs1, mem1, g', popped.
unfold DMdrainU9.recyc_cut_in. cbv zeta.
refine (conj PRE _).
refine (conj _ _).
{ (* the model's recycle cut *)
  split.
  - change (YFeuC.transfer_g X) with (AFeu.transfer_g X). rewrite EQB, <- HLB. exact HGT.
  - exists (AFeu.transfer_g X), [], g', popped. splits.
    + change (YFeuC.transfer_g X) with (AFeu.transfer_g X). apply DMdrainM.merge_split_cf_triv.
      rewrite <- HMT. unfold DMdrainM.mtest, DMsegD.merge_test. rewrite lsz_len.
      unfold AFgj.LBv, AFgj.GBv, AFgj.TBv. reflexivity.
    + exact HPB.
    + reflexivity.
    + reflexivity. }
refine (conj HM _).
refine (conj _ _).
{ intros a HW. eapply DMdrainU4.win_in_dwin; first [exact AQi | exact Hglast | exact HW]. }
refine (conj _ _).
{ intros a RA HQ HP. eapply DMdrainU4.pres1_of_win;
  first [ exact AQi | exact Qly | exact (conj Hsp1 Hsp2) | exact BADDR | exact Hglast | exact HM | exact HPR
        | exact RA | exact HQ | exact HP ]. }
refine (conj _ _).
{ intros b Hb. destruct (BADDR b (HinGT b Hb)) as (A1 & A2 & A3 & A4 & A5). unfold addrb. splits; assumption. }
refine (conj _ _).
{ intros b Hb. exact (HSLOT b (HinGT b Hb)). }
refine (conj _ _).
{ rewrite HSPL'. exact HNDl. }
refine (conj _ _).
{ intros b Hb. exists b. split; [exact (HinGT b Hb) | reflexivity]. }
refine (conj _ _).
{ intros b Hb. rewrite HSPL' in Hb.
  destruct (In_nth_error _ _ Hb) as [i Hi].
  destruct (DMdrainQ.lcn_nth ly (DMdrainK.iwB B ly) (mrestrict (w_H W) mem1) _ 0 i b CLK Hi) as (_ & C8 & C16 & CS).
  splits; assumption. }
refine (conj V8 (conj V16 (conj V24 (conj V32 (conj V40 (conj V48 _)))))).
refine (conj CT0 (conj CT8 (conj CT16 (conj CT24 _)))).
refine (conj ESP _).
refine (conj _ _).
{ intros r Hr. apply RS. unfold DMsegD.SREGS_M in Hr. unfold AFgj.SREGS. cbn [In] in Hr |- *. tauto. }
refine (conj R12 _).
refine (conj _ HAT).
apply HBYT. exact EQB.
Qed.
End g.
End f.
