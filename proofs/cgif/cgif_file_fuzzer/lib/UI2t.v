(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YL0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c YL0h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition llvm_spec (pc empty stk : Z) : Prop :=
forall L A regs mem md p n,
fn_pre ubs0_msyms MR stk L A regs mem md ->
st_init_done A = true ->
sink_none ubs0_msyms mem md -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) (blocks L A))) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR stk (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
sink_none ubs0_msyms mem' md' /\
(forall b, In b (blocks L A) -> In b (blocks L' A'))).
Theorem lib_contract_of_llvm : forall pc ra empty stk,
0 <= ra < 2 ^ 64 -> ra mod 2 = 0 -> 0 <= stk ->
llvm_spec pc empty stk ->
lib_contractS ubs0_msyms API pc ra empty stk.
Proof using.
intros pc ra empty stk Hra Hev Hstk LLVM.
unfold lib_contractS. intros L A regs mem md p n (HPRE & HSN & Hsp47 & Hsorted) HFRM.
destruct HPRE as (HMR & HW & HB & Hid & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Ha0 & Ha1 & Hpn & _).
assert (Hfn : fn_pre ubs0_msyms MR stk L A regs mem md).
{ split; [| split; [| split; [| split]]].
- split; [exact HMR | split; [exact HW | exact HB]].
- rewrite Hra1. apply YK0s.ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small ra (2 ^ 64)) by lia. exact Hev.
- split; [exact Hal|]. split; [exact Hstk|]. split; [exact Hceil|]. split; [exact H63|]. exact Hstw.
- exact Htp.
- exact Herr. }
assert (Hpn' : (n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) (blocks L A))).
{ destruct Hpn as [H0 | (Hn & q & Hq & Hqa)]; [left; exact H0 | right]. split; [exact Hn|].
apply blocks_In. exists q. auto. }
eapply SR_mono; [exact (LLVM L A regs mem md p n Hfn Hid HSN Hsp47 Ha0 Ha1 Hpn') |].
intros c' (L' & A' & regs' & mem' & md' & -> & HJ & HP & Hid' & Hr10 & HSN' & Hbl).
exists fx, L', A', regs', mem', md'. rewrite Hra1. split; [reflexivity|]. split; [exact HFRM|].
destruct HJ as ((HMR' & HW' & HB') & Hvm & Hhi & Hkeep & Hgone & Hst' & Herr' & Himg).
unfold lib_postS.
split; [exact HMR'|]. split; [exact HW'|]. split; [exact HB'|]. split; [exact Hid'|].
split; [exact Hr10|]. split; [exact HP|]. split; [exact Hvm|].
split; [exact HSN'|]. split; [exact (os_step_sorted _ _ _ Hvm Hsorted)|].
split.
{
intros q k Hq.
assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; auto).
apply Hbl in Hin. apply blocks_In in Hin as (q' & Hq' & Hin'). exists q'. auto. }
split.
{
intros a Ha Hns. apply Hhi; [exact Ha|]. intros Hw. apply Hns. unfold lib_scratch. left. exact Hw. }
split.
{ intros a Ha Hs Hc He Hno. apply (Himg a Ha Hs Hc He). intros [_ Hr]. exact (Hno Hr). }
split.
{
intros q k i Hq _ Hi.
assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; auto).
apply (Hkeep (ptr_addr L q) k i Hin (Hbl _ Hin) Hi). intros (r & [<- | []] & Hr). cbn [fst snd sink_token] in Hr.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md (ptr_addr L q) k (conj HMR (conj HW HB)) Hin ltac:(lia)) as (H4096 & _). lia. }
intros a [Hw | He].
- destruct Hst' as (_ & _ & _ & _ & Hsw). apply Hsw. exact Hw.
- apply Herr'. exact He.
Qed.
End d.
End c.
