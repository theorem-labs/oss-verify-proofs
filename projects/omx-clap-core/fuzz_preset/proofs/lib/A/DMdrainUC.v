(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainUC.v (commit 67deba317dfb, blob 5dd035996958) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainG1 DMdrainG4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdrainMN.
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

Hypothesis BADDR_X : forall b, In b (all_batches X) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Hypothesis HSLOT_X : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HSLOT_PR : forall b, In b (P ++ qc_list gk) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HOBJ : forall b, In b (P ++ qc_list gk) -> exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b.

Hypothesis HM1 : forall x : word, ~ F1 (bv_unsigned x) -> mem1 x = mem x.
Hypothesis HF1 : forall a, F1 a -> dwin_q inst ly sp0 X S' P a.
Hypothesis HM2 : forall x : word,
  ~ (sp1 <= bv_unsigned x < sp1 + 32) ->
  ~ (A_QUAR + 152 <= bv_unsigned x < A_QUAR + 156) ->
  ~ (A_QUAR + 160 <= bv_unsigned x < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= bv_unsigned x < addrb ly b + 8)) ->
  mem' x = mem1 x.

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

Lemma dwin_split : forall a, 0 <= a < 2 ^ 64 -> dwin_q inst ly sp0 X S' P a ->
  ascratch B YFeuC.DSTACK regs a \/ AOX ly X a.
Proof.
intros a RA [HS | [HQ | HC]].
- left. left. unfold spZ. fold sp0. exact HS.
- right. exact (QO inst ly X W mem md a HAR HPREM RA (or_introl HQ)).
- right. exact (QO inst ly X W mem md a HAR HPREM RA (or_intror (bcellw_obj a HC))).
Qed.

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
