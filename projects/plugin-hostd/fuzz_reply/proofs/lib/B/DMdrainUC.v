(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainUC.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 9a8264f9c8c9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainUC.v at commit 2e76ed2595c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the recycle cut's memory AGAINST THE DRAIN'S ENTRY, in the
   leaf's terms.  Everything the walk changes up to Recycle's call of DoRecycle - stage 1 (written set F1)
   and the dequeue loop (DMdeq.DW) - lies in the cut's window DMiface.dwin_q, and that window is Drain's
   scratch (its stack window) or OWNED at the entry state: the quarantine header and the batch cells
   (DMiface.di_qowned, DMiface.v:175-177; the cut lists' batches are X's objects, DMdrainU9.recyc_cut_in).
   So:
   - [dwin_split]: a word of the cut's window is Drain's scratch or owned at X;
   - [cut_raw]: off X's owned set and Drain's scratch the cut's memory is the entry's (DMdrainUB's HRAW, first
     half);
   - [cut_errno] / [cut_memnorm]: errno is untouched, and memnorm is kept (every word of the window is
     mn_safe at the image, DMdrainMN) - DMdrainTE's two keeps, for the recycle cut.
   rule 24: no function proved (kind: frame consequences of segments already walked; the lane's reuse search
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF DMdrainG1 DMdrainG4 ErrnoG MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMdrainMN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Hypothesis TB : TfibSyms B.
Hypothesis QO : di_qowned_t ARX AOX L24 QB.

Variables (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word).
Variables (mem mem1 mem' : word -> option byte) (md : Model).
Variables (gk : qcache) (P : list batch) (F1 : Z -> Prop).
Let sp0 : Z := bv_unsigned (getr regs 2).
Let sp1 : Z := sp0 - 80.
Local Notation S' := (set_qglobal gk (set_qthread qc0 X)).

Hypothesis HAR : ARX inst ly X W mem md.
Hypothesis HPREM : dprem L24 QB X.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HSP : ly_stk_lo ly + YFeuC.DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis AQ : inst + o_quar = A_QUAR.
(* X's batches and the cut lists' batches: placed, with at most kBatchSlots items; the cut's are X's objects *)
Hypothesis BADDR_X : forall b, In b (all_batches X) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Hypothesis HSLOT_X : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HSLOT_PR : forall b, In b (P ++ qc_list gk) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HOBJ : forall b, In b (P ++ qc_list gk) -> exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b.
(* stage 1 and stage 2 *)
Hypothesis HM1 : forall x : word, ~ F1 (bv_unsigned x) -> mem1 x = mem x.
Hypothesis HF1 : forall a, F1 a -> dwin_q inst ly sp0 X S' P a.
Hypothesis HM2 : forall x : word,
  ~ (sp1 <= bv_unsigned x < sp1 + 32) ->
  ~ (A_QUAR + 152 <= bv_unsigned x < A_QUAR + 156) ->
  ~ (A_QUAR + 160 <= bv_unsigned x < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= bv_unsigned x < addrb ly b + 8)) ->
  mem' x = mem1 x.

(* every batch whose cells the window names is one of X's objects, so its cells are owned *)
Lemma bcellw_obj : forall a, bcellw ly (all_batches X ++ all_batches S' ++ P) a ->
  exists b0, In b0 (all_batches X) /\ bobj ly b0 a.
Proof.
intros a (b & Hb & Ha).
assert (HS : (length (b_items b) <= Z.to_nat kBatchSlots)%nat /\ exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b).
{ apply in_app_iff in Hb as [Hb|Hb].
  - split; [exact (HSLOT_X b Hb) | exists b; split; [exact Hb | reflexivity]].
  - assert (Hb' : In b (P ++ qc_list gk)).
    { apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [right | left; exact Hb].
      unfold all_batches in Hb. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 app] in Hb.
      exact Hb. }
    split; [exact (HSLOT_PR b Hb') | exact (HOBJ b Hb')]. }
destruct HS as [HSl (b0 & Hb0 & Eb)].
exists b0. split; [exact Hb0|]. unfold bobj. rewrite Eb.
unfold zl, kBatchBytes in *. unfold kBatchSlots in HSl. lia.
Qed.

(* a word of the cut's window is Drain's scratch or owned at X *)
Lemma dwin_split : forall a, 0 <= a < 2 ^ 64 -> dwin_q inst ly sp0 X S' P a ->
  ascratch B YFeuC.DSTACK regs a \/ AOX ly X a.
Proof.
intros a RA [HS | [HQ | HC]].
- left. left. unfold spZ. fold sp0. exact HS.
- right. exact (QO inst ly X W mem md a HAR HPREM RA (or_introl HQ)).
- right. exact (QO inst ly X W mem md a HAR HPREM RA (or_intror (bcellw_obj a HC))).
Qed.

(* the dequeue loop's written set is inside the cut's window *)
Lemma dw_in_dwin : forall a,
(sp1 <= a < sp1 + 32) \/ (A_QUAR + 152 <= a < A_QUAR + 156) \/ (A_QUAR + 160 <= a < A_QUAR + 192) \/
(exists b, In b P /\ addrb ly b <= a < addrb ly b + 8) ->
dwin_q inst ly sp0 X S' P a.
Proof.
intros a [H | [H | [H | (b & Hb & H)]]].
- left. unfold sp1, YFeuC.DSTACK in *. lia.
- right; left. unfold qhdr. rewrite AQ. left. lia.
- right; left. unfold qhdr. rewrite AQ. right; left. lia.
- right; right. exists b. split; [apply in_app_iff; right; apply in_app_iff; right; exact Hb | unfold addrb, zl in *; lia].
Qed.

(* off the cut's window the cut's memory is the entry's *)
Lemma cut_frame_raw : forall x : word, ~ dwin_q inst ly sp0 X S' P (bv_unsigned x) -> mem' x = mem x.
Proof.
intros x HN.
rewrite (HM2 x).
- apply HM1. intros HW. apply HN. exact (HF1 _ HW).
- intros HD. apply HN. apply dw_in_dwin. left. exact HD.
- intros HD. apply HN. apply dw_in_dwin. right; left. exact HD.
- intros HD. apply HN. apply dw_in_dwin. right; right; left. exact HD.
- intros b Hb HD. apply HN. apply dw_in_dwin. right; right; right. exists b. split; [exact Hb | exact HD].
Qed.

Theorem cut_raw : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ ascratch B YFeuC.DSTACK regs (bv_unsigned x) ->
  mem' x = mem x.
Proof.
intros x HO HS. apply cut_frame_raw. intros HW.
destruct (dwin_split (bv_unsigned x) (u64_range x) HW) as [H|H]; contradiction.
Qed.

(* errno is an image word, outside the cut's window *)
Theorem cut_errno : ErrnoG.errno_kept B mem mem'.
Proof.
intros i Hi. apply cut_frame_raw.
pose proof (ts_errno _ TB) as EE.
pose proof (DMdrainG1.LYB2 ly LY) as (L1 & _ & _ & _ & _ & _ & _ & _ & K9).
pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
pose proof HSP as [S1 S2].
unfold w64. rewrite unsigned_lit_small by (rewrite EE; unfold TFIB_ERRNO; lia).
intros [HS | [HQ | HC]].
- rewrite EE in HS. unfold YFeuC.DSTACK, kHighMemBeg, TFIB_ERRNO in *. lia.
- unfold qhdr in HQ. rewrite AQ in HQ. destruct HQ as [HQ | [HQ | HQ]].
  + rewrite EE in HQ. unfold A_QUAR, A_ALLOCATOR, o_quar, TFIB_ERRNO in HQ. lia.
  + rewrite EE in HQ. unfold A_QUAR, A_ALLOCATOR, o_quar, TFIB_ERRNO in HQ. lia.
  + pose proof (DMdrainG1.TOBJ ly LY IMG (DMdrainG4.T_app ly LY) (DMdrainG4.T_img ly LY)) as (_ & TZ & _).
    apply (zone3_apart_img _ _ (as_errno B + i) TZ);
    [ rewrite EE; unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END; lia
    | rewrite EE in HQ; unfold TFIB_ERRNO, t_qc, kThreadObjSize in *; lia ].
- destruct (bcellw_obj _ HC) as (b0 & Hb0 & Hob). destruct (BADDR_X b0 Hb0) as (B1 & _ & _ & _).
  rewrite EE in Hob. unfold bobj, addrb, kHighMemBeg, TFIB_ERRNO in *. lia.
Qed.

(* memnorm is kept: the window is the stack or owned at X *)
Theorem cut_memnorm : MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
apply (MemnormT.memnorm_frame tfibsegs (dwin_q inst ly sp0 X S' P)); [|exact cut_frame_raw].
intros x HW.
destruct HW as [HS | [HQ | HC]].
- apply (DMdrainMN.mn_safe_stk ly LY). destruct HSP as [S1 S2]. unfold YFeuC.DSTACK in *. lia.
- exact (DMdrainMN.mn_safe_qhdr ly LY IMG inst x AQ HQ).
- destruct (bcellw_obj _ HC) as (b0 & Hb0 & Hob). destruct (BADDR_X b0 Hb0) as (B1 & B2 & _).
  exact (DMdrainMN.mn_safe_bobj ly LY b0 x B1 B2 Hob).
Qed.
End g.
End f.
