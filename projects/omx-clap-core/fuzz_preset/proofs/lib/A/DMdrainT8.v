(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT8.v (commit 67deba317dfb, blob 789d378a5dbd) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainK DMdrainM DMdrainP DMdrainT2 DMdrainT3 DMdrainT4 DMdrainT7.
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
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m0 := mrestrict (w_H W) mem0.
Let m' := mrestrict (w_H W) mem'.
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).

Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis Hinst : as_inst B = inst.

Hypothesis HM : forall x : word, ~ AFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HWP : forall a, AFgj.WIN ly regs0 (st_qglobal X) a -> kHighMemBeg <= a -> apresent (w_H W) mem' a.
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

Lemma cellw_in_obj : forall b, In b (all_batches X) -> forall a,
addrb ly b <= a < addrb ly b + 24 + 8 * zl (b_items b) -> SB + b_self b <= a < SB + b_self b + kBatchBytes.
Proof.
intros b Hb a Ha. pose proof (HSLOT b Hb) as HS. unfold addrb, zl, kBatchSlots, kBatchBytes in *.
assert (Z.of_nat (length (b_items b)) <= 1021) by lia. lia.
Qed.

Lemma G_init_keep : forall initr lastb, G = initr ++ [lastb] ->
lcn ly (iwB B ly) m' initr (addrb ly lastb).
Proof.
intros initr lastb EG.
assert (HLI : lcn ly (iwB B ly) m0 initr (fa ly [lastb] 0)).
{ rewrite EG in HLG. exact (proj1 (lcn_app_split ly (iwB B ly) m0 initr [lastb] 0 HLG)). }
cbn [fa] in HLI.
apply (lcn_keep ly (iwB B ly) (w_H W) (AFgj.WIN ly regs0 (st_qglobal X)) mem0 mem' initr _ HM); [|exact HLI].
intros b Hb.
assert (HbA : In b (all_batches X)).
{ unfold all_batches. apply in_app_iff. right. rewrite EG. apply in_app_iff. left. exact Hb. }
destruct (BADDR b HbA) as (A1 & A2 & A3 & A4). pose proof (HSLOT b HbA) as HS.
assert (R2 : addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64).
{ unfold addrb, zl, kBatchSlots in *. assert (Z.of_nat (length (b_items b)) <= 1021) by lia.
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in *. lia. }
split; [unfold addrb; lia|]. split; [exact R2|].
intros a Ha. apply (batch_off_win ly regs0 X LY HSP BADDR b HbA a (cellw_in_obj b HbA a Ha)).
intros lastb' initr' ER Hin'. left.

assert (ELAST : lastb' = lastb).
{ rewrite EG in ER. rewrite rev_app_distr in ER. cbn [rev app] in ER. injection ER as <- _. reflexivity. }
subst lastb'.
intros EQ. pose proof HND as ND0.
assert (EM : map b_self (all_batches X) = map b_self Tq ++ map b_self initr ++ [b_self lastb]).
{ unfold all_batches. rewrite EG, !map_app. cbn [map]. reflexivity. }
rewrite EM in ND0. apply NoDup_app_iff in ND0 as (_ & ND1 & _).
apply NoDup_app_iff in ND1 as (_ & _ & SEP).
apply (SEP (b_self lastb)); [|left; reflexivity].
rewrite <- EQ. apply in_map_iff. exists b. split; [reflexivity | exact Hb].
Qed.
End g.
End f.
