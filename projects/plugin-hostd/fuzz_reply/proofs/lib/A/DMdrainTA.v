(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTA.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 cddc145d0869) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the TRANSFERRED quarantine's cells at a drain cut - the second
   clause of DMiface.dmem_q (DMiface.v:120) at DMdrainM.sxf X, where the thread cache is empty and the global
   cache is the two lists joined.  Both the return arm (YFgj.at_RETD) and the no-merge arm (YFgj.at_L0) leave
   exactly these values, so the lemma is stated over them and used twice.
   rule 24: no function proved (kind: the cells of a cut after segments already walked; the lane's reuse search
   is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj AFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DMwalkIF DMdrainK DMdrainM DMdrainP DMdrainQ DMdrainT3 DMdrainT4 DMdrainT7 DMdrainT8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X : astate).
Variables (regs0 : bvmap 5 word) (mem0 mem' : word -> option byte).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m0 := mrestrict (w_H W) mem0.
Let m' := mrestrict (w_H W) mem'.
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).

Hypothesis AQ : as_inst B + o_quar = A_QUAR.
Hypothesis HM : forall x : word, ~ AFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).
Hypothesis HC160 : val_mem tfibsegs m' (A_QUAR + 160) 8 (AFgj.LSZv (st_qglobal X) (st_qthread X)).
Hypothesis HC168 : val_mem tfibsegs m' (A_QUAR + 168) 8 (AFgj.LFv ly (st_qglobal X) (st_qthread X)).
Hypothesis HC176 : val_mem tfibsegs m' (A_QUAR + 176) 8 (AFgj.TLv ly (st_qthread X)).
Hypothesis HC184 : val_mem tfibsegs m' (A_QUAR + 184) 8 (AFgj.LBv (st_qglobal X) (st_qthread X)).
Hypothesis HT0 : val_mem tfibsegs m' (ly_T ly + t_qc) 8 0.
Hypothesis HT8 : val_mem tfibsegs m' (ly_T ly + t_qc + 8) 8 0.
Hypothesis HT16 : val_mem tfibsegs m' (ly_T ly + t_qc + 16) 8 0.
Hypothesis HT24 : val_mem tfibsegs m' (ly_T ly + t_qc + 24) 8 0.
Hypothesis HLINK : forall lastb initr, rev G = lastb :: initr ->
  val_mem tfibsegs m' (AFgj.GLv ly (st_qglobal X)) 8 (AFgj.TFv ly (st_qthread X)).
Hypothesis HLG : lcn ly (iwB B ly) m0 G 0.
Hypothesis HLT : lcn ly (iwB B ly) m0 Tq 0.
Hypothesis HTne : Tq <> [].
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
  0 <= SB + b_self b < ASAN_CEIL.
Hypothesis HSLOT : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HND : List.NoDup (map b_self (all_batches X)).
Hypothesis HWF : qc_bytes (st_qthread X) = sum_bytes Tq /\ qc_bytes (st_qglobal X) = sum_bytes G.

Lemma rng : forall b, In b (all_batches X) -> 0 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64.
Proof.
intros b Hb. destruct (BADDR b Hb) as (A1 & A2 & A3 & A4). pose proof (HSLOT b Hb) as HS.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
unfold addrb, zl, kBatchSlots, kBatchBytes, YG0f.ASAN_CEIL in *.
assert (Z.of_nat (length (b_items b)) <= 1021) by lia. split; lia.
Qed.

(* the thread list keeps all its cells: none of its batches is the global list's last *)
Lemma T_keep : lcn ly (iwB B ly) m' Tq 0.
Proof.
apply (lcn_keep ly (iwB B ly) (w_H W) (AFgj.WIN ly regs0 (st_qglobal X)) mem0 mem' Tq 0 HM); [|exact HLT].
intros b Hb.
assert (HbA : In b (all_batches X)) by (unfold all_batches; apply in_app_iff; left; exact Hb).
destruct (rng b HbA) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
intros a Ha.
assert (HRNG : SB + b_self b <= a < SB + b_self b + kBatchBytes).
{ pose proof (HSLOT b HbA) as HS. unfold addrb, zl, kBatchSlots, kBatchBytes in *.
  assert (Z.of_nat (length (b_items b)) <= 1021) by lia. lia. }
apply (batch_off_win ly regs0 X LY HSP BADDR b HbA a HRNG).
intros lastb initr ER Hin. left. intros EQ.
pose proof HND as ND0.
assert (EM : map b_self (all_batches X) = map b_self Tq ++ map b_self G) by (unfold all_batches; rewrite map_app; reflexivity).
rewrite EM in ND0. apply NoDup_app_iff in ND0 as (_ & _ & SEP).
apply (SEP (b_self b)); [apply in_map_iff; exists b; split; [reflexivity | exact Hb]|].
rewrite EQ. apply in_map_iff. exists lastb. split; [reflexivity|].
rewrite <- (rev_involutive G), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity.
Qed.

(* the joined list at the cut *)
Lemma GT_lcn : lcn ly (iwB B ly) m' (G ++ Tq) 0.
Proof.
apply (lcn_app_link ly (iwB B ly) m' G Tq 0); [|exact T_keep].
destruct (rev G) as [|lastb initr] eqn:ER.
- assert (EG : G = []) by (rewrite <- (rev_involutive G), ER; reflexivity). rewrite EG. exact I.
- assert (EG : G = rev initr ++ [lastb]) by (rewrite <- (rev_involutive G), ER; reflexivity).
  assert (Hin : In lastb (all_batches X)).
  { unfold all_batches. apply in_app_iff. right. rewrite EG. apply in_app_iff. right. left. reflexivity. }
  assert (EGL : AFgj.GLv ly (st_qglobal X) = addrb ly lastb) by (unfold AFgj.GLv, addrb; rewrite ER; reflexivity).
  rewrite EG. apply (lcn_snoc ly (iwB B ly) m' (rev initr) lastb (fa ly Tq 0)).
  + eapply G_init_keep; first [exact EG | eassumption].
  + assert (HB0 : bcell ly (iwB B ly) m0 lastb 0).
    { rewrite EG in HLG. destruct (lcn_app_split ly (iwB B ly) m0 (rev initr) [lastb] 0 HLG) as [_ HL2].
      cbn [lcn] in HL2. exact (proj1 HL2). }
    destruct (rng lastb Hin) as [R1 R2].
    assert (HZ : val_mem tfibsegs m' (addrb ly lastb) 8 (fa ly Tq 0)).
    { rewrite <- EGL. assert (ETF : AFgj.TFv ly (st_qthread X) = fa ly Tq 0) by (unfold AFgj.TFv, fa, addrb; destruct Tq; reflexivity).
      rewrite <- ETF. exact (HLINK lastb initr eq_refl). }
    apply (bcell_relink ly (iwB B ly) (w_H W) (AFgj.WIN ly regs0 (st_qglobal X)) mem0 mem' lastb 0 (fa ly Tq 0) HM R1 R2); [|exact HZ|exact HB0].
    intros a Ha.
    assert (HRNG : SB + b_self lastb <= a < SB + b_self lastb + kBatchBytes).
    { pose proof (HSLOT lastb Hin) as HS. unfold addrb, zl, kBatchSlots, kBatchBytes in *.
      assert (Z.of_nat (length (b_items lastb)) <= 1021) by lia. lia. }
    apply (batch_off_win ly regs0 X LY HSP BADDR lastb Hin a HRNG).
    intros lastb' initr' ER' Hin'. right. rewrite EGL. unfold addrb in *. lia.
Qed.
End g.
End f.
