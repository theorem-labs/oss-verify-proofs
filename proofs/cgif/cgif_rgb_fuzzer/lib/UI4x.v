(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YL0e
YI08 YI0c UI3h UI3d UI4y UI52.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Theorem lib_contract_of_rllvm : forall pc ra empty,
0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
rllvm_spec API pc empty ->
lib_contract ubs2_msyms API pc ra empty LIB_STACK_RGB.
Proof.
intros pc ra empty Hra Hev LLVM.
unfold lib_contract. intros L A regs mem md p n HPRE HFRM.
destruct HPRE as (HMR & HW & HB & Hid & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Ha0 & Ha1 & Hpn & Hro).
assert (Hfn : fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md).
{ split; [| split; [| split; [| split]]].
- split; [exact HMR | split; [exact HW | exact HB]].
- rewrite Hra1. apply YK0s.ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small ra (2 ^ 64)) by lia. exact Hev.
- split; [exact Hal|]. split; [unfold LIB_STACK_RGB; lia|]. split; [exact Hceil|]. split; [exact H63|]. exact Hstw.
- exact Htp.
- exact Herr. }
assert (Hpn' : (n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) (blocks L A))).
{ destruct Hpn as [H0 | (Hn & q & Hq & Hqa)]; [left; exact H0 | right]. split; [exact Hn|].
apply blocks_In. exists q. auto. }
eapply SR_mono; [exact (LLVM L A regs mem md p n Hfn Hid HFRM (ubs2_rgb_rodata_of_lib mem Hro) Ha0 Ha1 Hpn') |].
intros c' (fx' & L' & A' & regs' & mem' & md' & -> & HFRM' & HJ & HP & Hid' & Hr10 & Hbl).
exists fx', L', A', regs', mem', md'. rewrite Hra1. split; [reflexivity|]. split; [exact HFRM'|].
destruct HJ as ((HMR' & HW' & HB') & Hvm & Hhi & Hkeep & Hgone & Hst' & Herr' & Himg).
unfold lib_post.
split; [exact HMR'|]. split; [exact HW'|]. split; [exact HB'|]. split; [exact Hid'|].
split; [exact Hr10|]. split; [exact HP|]. split; [exact Hvm|].
split.
{
intros q k Hq.
assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; auto).
apply Hbl in Hin. apply blocks_In in Hin as (q' & Hq' & Hin'). exists q'. auto. }
split.
{
intros a Ha Hns. apply Hhi; [exact Ha|]. intros Hw. apply Hns. unfold lib_scratch. left. exact Hw. }
split.
{ exact Himg. }
split.
{
intros q k i Hq _ Hi.
assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; auto).
apply (Hkeep (ptr_addr L q) k i Hin (Hbl _ Hin) Hi). intros (r & Hr & _). exact Hr. }
intros a [Hw | He].
- destruct Hst' as (_ & _ & _ & _ & Hsw). apply Hsw. exact Hw.
- apply Herr'. exact He.
Qed.
End c.
End b.
Section d. Context {rc : YN05.RunCeil}.
Theorem ubs2_rgb_LIB : forall (API : AllocAPI ubs2_msyms),
img_laws ubs2_msyms (aa_MR API) ->
(forall fx, rgb_newgif_spec (fx:=fx) API) ->
(forall fx, rgb_addframe_spec (fx:=fx) API) ->
(forall fx, rgb_close_spec (fx:=fx) API) ->
forall ra empty, 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
lib_contract_all ubs2_msyms API ubs2_A_LLVMFuzzerTestOneInput ra empty LIB_STACK_RGB.
Proof.
intros API IMG NEWG ADDF CLOSE ra empty Hra Hev fx.
apply (lib_contract_of_rllvm API _ ra empty Hra Hev).
exact (ubs2_rllvm_spec API IMG (NEWG fx) CLOSE ADDF empty).
Qed.
End d.
