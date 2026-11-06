(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainUD.v (commit 67deba317dfb, blob dd47b7dce337) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d YO0f.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainG1 DMdrainG4 DMdrainT7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variables (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs regs1 regs' : bvmap 5 word).
Variables (mem mem1 mem' : word -> option byte) (gk : qcache) (P : list batch) (L24 : Z).
Let sp0 : Z := bv_unsigned (getr regs 2).
Let sp1 : Z := sp0 - 80.
Let m1 := mrestrict (w_H W) mem1.
Let m' := mrestrict (w_H W) mem'.

Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HSP : ly_stk_lo ly + YFeuC.DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR_PR : forall b, In b (P ++ qc_list gk) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Hypothesis HND_PR : List.NoDup (map b_self (P ++ qc_list gk)).
Hypothesis HOBJ : forall b, In b (P ++ qc_list gk) -> exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b.
Hypothesis HLX : Z.of_nat (length (all_batches X)) <= L24.
Hypothesis HL24 : L24 < 2 ^ 40.

Hypothesis HPRE_PRES : forall a, sp0 - YFeuC.DSTACK <= a < sp0 -> apresent (w_H W) mem a.
Hypothesis HPR1 : forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem1 a.
Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis T0 : val_mem tfibsegs m1 (ly_T ly + t_qc) 8 0.
Hypothesis T8 : val_mem tfibsegs m1 (ly_T ly + t_qc + 8) 8 0.
Hypothesis T16 : val_mem tfibsegs m1 (ly_T ly + t_qc + 16) 8 0.
Hypothesis T24 : val_mem tfibsegs m1 (ly_T ly + t_qc + 24) 8 0.

Hypothesis HM2 : forall x : word,
  ~ (sp1 <= bv_unsigned x < sp1 + 32) ->
  ~ (A_QUAR + 152 <= bv_unsigned x < A_QUAR + 156) ->
  ~ (A_QUAR + 160 <= bv_unsigned x < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= bv_unsigned x < addrb ly b + 8)) ->
  mem' x = mem1 x.
Hypothesis HPR2 : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a ->
  ~ (A_QUAR + 152 <= a < A_QUAR + 192) -> apresent (w_H W) mem' a.
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).

Lemma tqc_apart : forall a, ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 <= a < sp1 + 32) /\ ~ (A_QUAR + 152 <= a < A_QUAR + 156) /\
  ~ (A_QUAR + 160 <= a < A_QUAR + 192) /\ (forall b, In b P -> ~ (addrb ly b <= a < addrb ly b + 8)).
Proof.
intros a Ha.
pose proof (DMdrainG1.TOBJ ly LY IMG (DMdrainG4.T_app ly LY) (DMdrainG4.T_img ly LY)) as (T1 & TZ & T2 & T3 & T4).
pose proof (DMdrainG1.LYB2 ly LY) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & K9).
pose proof (DMdrainT7.prim_apart ly LY) as [PT _].
pose proof HSP as [S1 S2]. ceil.
assert (TQ : t_qc + 32 <= kThreadObjSize) by (unfold t_qc, kThreadObjSize; lia).
assert (EAQ : A_QUAR = 686896) by reflexivity.
assert (ELO : TFIB_IMG_LO = 65536) by reflexivity.
assert (EHI : TFIB_IMG_END = 6291456) by reflexivity.
refine (conj _ (conj _ (conj _ (conj _ _)))).
- unfold t_qc, kThreadObjSize in *. lia.
- unfold sp1, YFeuC.DSTACK, t_qc, kThreadObjSize in *. lia.
- intros HX. apply (zone3_apart_img (ly_T ly) kThreadObjSize a TZ).
  + rewrite EAQ in HX. rewrite ELO, EHI. lia.
  + unfold t_qc, kThreadObjSize in *. lia.
- intros HX. apply (zone3_apart_img (ly_T ly) kThreadObjSize a TZ).
  + rewrite EAQ in HX. rewrite ELO, EHI. lia.
  + unfold t_qc, kThreadObjSize in *. lia.
- intros b Hb HX. assert (Hb' : In b (P ++ qc_list gk)) by (apply in_app_iff; left; exact Hb).
  destruct (BADDR_PR b Hb') as (B1 & B2 & B3 & B4).
  unfold kBatchBytes, kSpaceSize, kPrimResvSize, t_qc, kThreadObjSize in *. lia.
Qed.

Lemma tqc_keep : forall off, 0 <= off -> off + 8 <= 32 ->
  val_mem tfibsegs m1 (ly_T ly + t_qc + off) 8 0 -> val_mem tfibsegs m' (ly_T ly + t_qc + off) 8 0.
Proof.
intros off H1 H2 HV. unfold m', m1 in *.
apply (AF0x.val_mem_frame (w_H W) mem1 mem'); [|exact HV].
intros k Hk.
destruct (tqc_apart (ly_T ly + t_qc + off + Z.of_nat k) ltac:(lia)) as (RA & A1 & A2 & A3 & A4).
apply HM2; rewrite (unsigned_lit_small _ RA); assumption.
Qed.

Lemma tqc_call : val_mem tfibsegs m' (ly_T ly + t_qc) 8 0 /\ val_mem tfibsegs m' (ly_T ly + t_qc + 8) 8 0 /\
  val_mem tfibsegs m' (ly_T ly + t_qc + 16) 8 0 /\ val_mem tfibsegs m' (ly_T ly + t_qc + 24) 8 0.
Proof.
splits.
- pose proof (tqc_keep 0 ltac:(lia) ltac:(lia)) as K. rewrite Z.add_0_r in K. exact (K T0).
- exact (tqc_keep 8 ltac:(lia) ltac:(lia) T8).
- exact (tqc_keep 16 ltac:(lia) ltac:(lia) T16).
- exact (tqc_keep 24 ltac:(lia) ltac:(lia) T24).
Qed.

Lemma hmut2 : val_mem tfibsegs m' (A_QUAR + 152 + 2) 2 0.
Proof.
intros k Hk. cbn in Hk.
rewrite (HMUT (A_QUAR + 152 + 2 + Z.of_nat k)) by lia.
assert (Hk2 : k = 0%nat \/ k = 1%nat) by lia.
destruct Hk2 as [->| ->]; reflexivity.
Qed.

Lemma pres_stack : forall a, sp0 - YFeuC.DSTACK <= a < sp0 -> apresent (w_H W) mem' a.
Proof.
intros a Ha.
pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
pose proof (DMdrainG1.TOBJ ly LY IMG (DMdrainG4.T_app ly LY) (DMdrainG4.T_img ly LY)) as (_ & TZ & _ & _ & T4).
pose proof HSP as [S1 S2].
assert (RA : 0 <= a < 2 ^ 64) by (unfold YFeuC.DSTACK, kHighMemBeg, kHighMemEnd in *; lia).
apply (HPR2 a RA).
- apply (HPR1 a RA); [|exact (HPRE_PRES a Ha)].
  unfold qhdr. rewrite AQ. intros [HQ | [HQ | HQ]].
  + unfold A_QUAR, A_ALLOCATOR, o_quar, YFeuC.DSTACK, kHighMemBeg in *. lia.
  + unfold A_QUAR, A_ALLOCATOR, o_quar, YFeuC.DSTACK, kHighMemBeg in *. lia.
  + unfold YFeuC.DSTACK, t_qc, kThreadObjSize in *. lia.
- unfold A_QUAR, A_ALLOCATOR, o_quar, YFeuC.DSTACK, kHighMemBeg in *. lia.
Qed.

Lemma len_P : zl P < 2 ^ 40.
Proof.
assert (HI : incl (map b_self P) (map b_self (all_batches X))).
{ intros s Hs. apply in_map_iff in Hs as (b & <- & Hb).
  destruct (HOBJ b ltac:(apply in_app_iff; left; exact Hb)) as (b0 & Hb0 & E).
  rewrite <- E. apply in_map. exact Hb0. }
assert (ND : List.NoDup (map b_self P)).
{ rewrite map_app in HND_PR. exact (List.NoDup_app_remove_r _ _ HND_PR). }
pose proof (List.NoDup_incl_length ND HI) as HLen. rewrite !length_map in HLen.
unfold zl. lia.
Qed.
End g.
End f.
