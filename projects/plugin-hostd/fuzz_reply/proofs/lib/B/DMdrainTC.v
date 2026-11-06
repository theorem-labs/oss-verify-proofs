(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTC.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 dda2e1e2be97) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTC.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): DMiface.dmem_q IN FULL (DMiface.v:118-127) at the transferred
   state, assembling the four clauses: the frame (DMdrainT2.dmem_frame), the cells (DMdrainTB.cut_cells), the
   presence kept off the quarantine's header, and the two bytes after the mutex word.  This is the whole machine
   side of the drain's cut; with DMiface.di_requar_x it gives ARX at the transferred state, and with
   DMiface.di_requar_r the recycle arms' ARXr.
   rule 24: no function proved (kind: the cut relation of segments already walked; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF DMdrainK DMdrainM DMdrainP DMdrainQ DMdrainG1 DMdrainT2 DMdrainT7 DMdrainTA DMdrainTB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* presence depends only on the byte at the address, and only on the address modulo 2 ^ 64 *)
Lemma apresent_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E [H1 [b Hb]]. split; [exact H1|]. exists b. rewrite E. exact Hb. Qed.

Lemma apresent_mod : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a <-> apresent H m (bv_unsigned (Z_to_bv 64 a)).
Proof.
intros H m a. unfold apresent. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X : astate).
Variables (regs0 : bvmap 5 word) (mem0 mem' : word -> option byte).
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m' := mrestrict (w_H W) mem'.
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).

Hypothesis Hinst : as_inst B = inst.
Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis HM : forall x : word, ~ YFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HWP : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> kHighMemBeg <= a -> apresent (w_H W) mem' a.
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).
Hypothesis HMUT2 : val_mem tfibsegs m' (A_QUAR + 152 + 2) 2 0.
Hypothesis HCELLS : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells (sxf X)).
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
  0 <= SB + b_self b < ASAN_CEIL.
Hypothesis Hglast : forall lastb initr, rev G = lastb :: initr ->
  YFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X).
(* presence on the quarantine's header is NOT needed: dmem_q's presence clause is stated for 0 <= a < 2^64 only, so
   it never asks for a header word (DMiface.v:122-126) *)

(* decidable tests for the two windows *)
Definition qhdrb (a : Z) : bool :=
((inst + o_quar + 152 <=? a) && (a <? inst + o_quar + 156)) ||
((inst + o_quar + 160 <=? a) && (a <? inst + o_quar + 192)) ||
((ly_T ly + t_qc <=? a) && (a <? ly_T ly + t_qc + 32)).
Definition winb (a : Z) : bool :=
((sp0 - 80 <=? a) && (a <? sp0)) ||
((A_QUAR + 152 <=? a) && (a <? A_QUAR + 156)) ||
((A_QUAR + 160 <=? a) && (a <? A_QUAR + 192)) ||
((ly_T ly + t_qc <=? a) && (a <? ly_T ly + t_qc + 32)) ||
(match G with [] => false | _ :: _ => (YFgj.GLv ly (st_qglobal X) <=? a) && (a <? YFgj.GLv ly (st_qglobal X) + 8) end).
Local Ltac bsplit H := repeat (apply Bool.orb_prop in H as [H|H]); repeat (apply andb_prop in H as [? ?]);
  repeat match goal with Hx : (_ <=? _) = true |- _ => apply Z.leb_le in Hx | Hx : (_ <? _) = true |- _ => apply Z.ltb_lt in Hx end.
Lemma qhdrb_true : forall a, qhdrb a = true -> qhdr inst ly a.
Proof.
intros a Hb. unfold qhdrb in Hb. unfold qhdr. bsplit Hb; [left | right; left | right; right]; lia.
Qed.
Lemma qhdr_qhdrb : forall a, qhdr inst ly a -> qhdrb a = true.
Proof.
intros a HQ. unfold qhdrb. unfold qhdr in HQ.
assert (T1 : forall x y z : Z, x <= z < y -> ((x <=? z) && (z <? y))%bool = true)
  by (intros x y z [H1 H2]; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; assumption).
destruct HQ as [HQ|[HQ|HQ]];
[ assert (HA : ((inst + o_quar + 152 <=? a) && (a <? inst + o_quar + 156))%bool = true) by (apply T1; lia)
| assert (HA : ((inst + o_quar + 160 <=? a) && (a <? inst + o_quar + 192))%bool = true) by (apply T1; lia)
| assert (HA : ((ly_T ly + t_qc <=? a) && (a <? ly_T ly + t_qc + 32))%bool = true) by (apply T1; lia) ];
repeat rewrite Bool.orb_true_iff; tauto.
Qed.
Lemma qhdrb_false : forall a, qhdrb a = false -> ~ qhdr inst ly a.
Proof. intros a Hb HQ. rewrite (qhdr_qhdrb a HQ) in Hb. discriminate. Qed.
Lemma winb_true : forall a, winb a = true -> YFgj.WIN ly regs0 (st_qglobal X) a.
Proof.
intros a Hb. unfold winb in Hb. unfold YFgj.WIN, YFgj.WINF, YFgj.WINA. fold sp0.
destruct G as [|b t] eqn:EG.
- bsplit Hb; [left | right; left; left | right; left; right; left | right; left; right; right | discriminate]; lia.
- bsplit Hb; [left | right; left; left | right; left; right; left | right; left; right; right |
    right; right; split; [discriminate | lia]]; try lia.
Qed.
Lemma win_winb : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> winb a = true.
Proof.
intros a HW. unfold winb. unfold YFgj.WIN, YFgj.WINF, YFgj.WINA in HW. fold sp0 in HW.
assert (T1 : forall x y z : Z, x <= z < y -> ((x <=? z) && (z <? y))%bool = true)
  by (intros x y z [H1 H2]; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; assumption).
destruct HW as [HW|[[HW|[HW|HW]]|[Hne HW]]].
- assert (HA : ((sp0 - 80 <=? a) && (a <? sp0))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : ((A_QUAR + 152 <=? a) && (a <? A_QUAR + 156))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : ((A_QUAR + 160 <=? a) && (a <? A_QUAR + 192))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : ((ly_T ly + t_qc <=? a) && (a <? ly_T ly + t_qc + 32))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : (match G with [] => false | _ :: _ =>
    (YFgj.GLv ly (st_qglobal X) <=? a) && (a <? YFgj.GLv ly (st_qglobal X) + 8) end)%bool = true).
  { destruct G as [|b t]; [exfalso; apply Hne; reflexivity | apply T1; lia]. }
  repeat rewrite Bool.orb_true_iff; tauto.
Qed.
Lemma winb_false : forall a, winb a = false -> ~ YFgj.WIN ly regs0 (st_qglobal X) a.
Proof. intros a Hb HW. rewrite (win_winb a HW) in Hb. discriminate. Qed.

(* the part of the walk's window that is NOT the quarantine's header is in high memory *)
Lemma win_hi : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> ~ qhdr inst ly a -> kHighMemBeg <= a.
Proof.
intros a HW HQ. pose proof (DMdrainG1.LYB2 ly LY) as (P1 & _ & _ & _ & _ & _ & _ & _ & K9).
pose proof HSP as [S1 S2].
unfold YFgj.WIN, YFgj.WINF, YFgj.WINA, qhdr in *. fold sp0 in HW.
destruct HW as [HW | [[HW | [HW | HW]] | [Hne HW]]].
- unfold DSTACK in *. lia.
- exfalso. apply HQ. left. rewrite AQ. lia.
- exfalso. apply HQ. right; left. rewrite AQ. lia.
- exfalso. apply HQ. right; right. lia.
- destruct (rev G) as [|lastb initr] eqn:ER.
  + exfalso. apply Hne. rewrite <- (rev_involutive G), ER. reflexivity.
  + destruct (Hglast lastb initr eq_refl) as [EG HIN]. destruct (BADDR lastb HIN) as (A1 & A2 & A3 & A4).
    rewrite EG in HW. unfold kBatchBytes in *. lia.
Qed.

Theorem dmem_q_cut : dmem_q B W inst ly sp0 X (sxf X) [] mem0 mem'.
Proof.
unfold dmem_q. splits.
- eapply dmem_frame; first [exact AQ | exact Hglast | exact HM].
- exact HCELLS.
- intros a HA HQ HP.
  set (a' := bv_unsigned (Z_to_bv 64 a)).
  assert (Ea : a' = a) by (subst a'; apply Z_to_bv_small; change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  assert (HP' : apresent (w_H W) mem0 a') by (exact (proj1 (apresent_mod (w_H W) mem0 a) HP)).
  apply (proj2 (apresent_mod (w_H W) mem' a)). fold a'.
  destruct (qhdrb a') eqn:EQ.
  + exfalso. apply HQ. rewrite <- Ea. exact (qhdrb_true a' EQ).
  + destruct (winb a') eqn:EW.
    * exact (HWP a' (winb_true a' EW) (win_hi a' (winb_true a' EW) (qhdrb_false a' EQ))).
    * apply (apresent_eq (w_H W) mem0 mem' a'); [|exact HP'].
      assert (ER : Z_to_bv 64 a' = Z_to_bv 64 a') by reflexivity.
      apply (HM (Z_to_bv 64 a')). unfold a'. rewrite Z_to_bv_bv_unsigned.
      apply winb_false. exact EW.
- match goal with |- val_mem _ _ ?a _ _ =>
    replace a with (A_QUAR + 152 + 2) by (rewrite <- AQ; unfold o_quar, o_q_cmutex; lia) end.
  exact HMUT2.
Qed.
End g.
End f.
