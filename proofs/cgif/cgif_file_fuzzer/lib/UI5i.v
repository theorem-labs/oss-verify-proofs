(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0o YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09
UI21 YL0g YL0i YL00
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI22 UI0l YI5a UI23 YI0a
UI5n UL0s UN3k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f UI5e UI5k UI5g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis ADDF : addframe_specX API.
Hypothesis RFC : rfc_specX API.
Hypothesis NEWGIF : newgif_x API.
Let UNLINK : unlink_x ubs0_msyms MR ubs0_A_unlink := ubs0_unlinkX API IMG.
Theorem ubs0_llvm_x :
forall L A (regs : bvmap 5 word) mem md (p n empty : Z) (PAYLOAD : list Z) (b0 : rbound) (plen : Z) (K : lleaf -> TSet),
fn_pre ubs0_msyms MR LIB_STACK L A regs mem md -> st_init_done A = true ->
sink_none ubs0_msyms mem md -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) (blocks L A))) ->
garr8 ubs0segs mem p PAYLOAD -> Z.of_nat (length PAYLOAD) = n ->
Fs.fs_sorted (m_fs md) = true -> fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None ->
res_ok A b0 -> ff_room b0 plen ->
(forall fs' c', leaf_post API regs L A mem md (ff_delta plen b0) fs' c' -> realizes ubs0segs c' (K (LL 0 fs' []))) ->
realizes ubs0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs)) md) (ff_tree K (m_fs md) PAYLOAD).
Proof using ADDF CLOSE NEWGIF RFC UNLINK.
intros L A regs mem md p n empty PAYLOAD b0 plen K HPRE Hid HSN Hsp47 G10 G11 Hpn HPL HPLn HSORT HFD HRES HROOM HK.
destruct Hpn as [[-> ->] | [Hn Hin]].
- destruct PAYLOAD as [|x l]; [| cbn [length] in HPLn; lia].
exact (lh_empty_x API IMG regs L A mem md b0 plen K HK HROOM HPRE Hid G11 HSN HRES).
- destruct (Z_lt_le_dec n 2) as [H0|H0]; [apply (lh_case_0 API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD p n PAYLOAD); try assumption; cbv beta; lia|].
destruct (Z_lt_le_dec n 4) as [H1|H1]; [apply (lh_case_1 API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD p n PAYLOAD); try assumption; cbv beta; lia|].
destruct (Z_lt_le_dec n 8) as [H2|H2]; [apply (lh_case_2 API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD p n PAYLOAD); try assumption; cbv beta; lia|].
destruct (Z_lt_le_dec n 12) as [H3|H3]; [apply (lh_case_3 API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD p n PAYLOAD); try assumption; cbv beta; lia|].
destruct (Z_lt_le_dec n 14) as [H4|H4]; [apply (lh_case_4 API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD p n PAYLOAD); try assumption; cbv beta; lia|].
apply (lh_case_5 API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD p n PAYLOAD); try assumption; cbv beta; lia.
Qed.
Theorem ubs0_lib_contract_x : @lib_contract_x fx rc ff_lib_shape ubs0_msyms API _ _ LIBPC RA_LIB EMPTY LIB_STACK.
Proof using ADDF CLOSE NEWGIF RFC UNLINK.
unfold lib_contract_x. intros L A regs mem md p n pl b K (HPRE & Hn & Hdata & HRES & HROOM & HSN & HFD & HSORT & Hsp47) HFRM HKL.
cbn [LIBK ff_lib_shape lib_delta lib_room] in *. rewrite ff_libk_tree.
destruct HPRE as (HMR & HW & HB & Hid & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Ha0 & Ha1 & Hpn & Hro).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (Hfn : fn_pre ubs0_msyms MR LIB_STACK L A regs mem md).
{ split; [| split; [| split; [| split]]].
- split; [exact HMR | split; [exact HW | exact HB]].
- rewrite Hra1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
- split; [exact Hal|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [exact Hceil|]. split; [exact H63|]. exact Hstw.
- exact Htp.
- exact Herr. }
assert (Hpn' : (n = 0 /\ p = EMPTY) \/ (0 < n /\ In (p, n) (blocks L A))).
{ destruct Hpn as [H0 | (Hn' & q & Hq & Hqa)]; [left; exact H0 | right]. split; [exact Hn'|]. apply blocks_In. exists q. auto. }
eapply (ubs0_llvm_x L A regs mem md p n EMPTY (zbytes pl) b n K Hfn Hid HSN Hsp47 Ha0 Ha1 Hpn' (blk_data_garr8 _ _ _ Hdata) ltac:(rewrite zbytes_length; lia) HSORT HFD HRES HROOM).
intros fs' c' (L' & A' & regs' & mem' & md' & -> & HJ & HP & Hid' & Hr10 & HSN' & Hbl & Hfs & HR').
apply (HKL (LL 0 fs' [])). exists fx, L', A', regs', mem', md'. rewrite Hra1. split; [reflexivity|]. split; [exact HFRM|].
pose proof (journal_fds_restored API _ _ _ _ _ _ _ _ _ _ _ HJ HSN HSN') as Hfds.
pose proof (journal_sorted API _ _ _ _ _ _ _ _ _ _ _ HJ HSORT) as Hsorted'.
destruct HJ as ((HMR' & HW' & HB') & Hos & Hhi & Hkeep & Hgone & Hst' & Herr' & Himg).
unfold lib_post_x.
split; [exact HMR'|]. split; [exact HW'|]. split; [exact HB'|]. split; [exact Hid'|].
split; [exact Hr10|]. split; [exact HP|]. split.
{
destruct Hos as (v & f & s & pn & Emd & _). exists v, f, pn. cbn [ll_fs]. split.
- rewrite <- Hfs, Emd, os_upd_fs. reflexivity.
- intros k. rewrite <- (Hfds k), Emd, os_upd_fds. reflexivity. }
split.
{
intros q k Hq.
assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; auto).
apply Hbl in Hin. apply blocks_In in Hin as (q' & Hq' & Hin'). exists q'. auto. }
split.
{
intros a Ha Hns. apply Hhi; [exact Ha|]. intros Hw. apply Hns. unfold lib_scratch. left. exact Hw. }
split.
{
assert (Hhw : forall (m : word -> option byte) a, ubs0_D_ofl_head <= a < ubs0_D_ofl_head + 8 -> writable_at ubs0segs m a).
{ intros m a Ha.
assert (Hc8 : exists k, (k < 8)%nat /\ a = ubs0_D_ofl_head + Z.of_nat k) by (exists (Z.to_nat (a - ubs0_D_ofl_head)); lia).
destruct Hc8 as (k & Hk & ->). unfold writable_at, wview.
do 8 (destruct k as [|k];
[match goal with |- match m ?x with _ => _ end <> None => destruct (m x); [discriminate | vm_compute; discriminate] end |]).
lia. }
intros a Ha Hs Hc He.
destruct (Z_lt_le_dec a sk_ofl_head) as [Hlt|Hge]; [apply (Himg a Ha Hs Hc He); intros [_ Hr]; lia|].
destruct (Z_lt_le_dec a (sk_ofl_head + 8)) as [Hin8|Hge8]; [| apply (Himg a Ha Hs Hc He); intros [_ Hr]; lia].
destruct HSN as (_ & Hw0 & _). destruct HSN' as (_ & Hw1 & _).
pose proof (Hw0 (Z.to_nat (a - sk_ofl_head)) ltac:(lia)) as B0. pose proof (Hw1 (Z.to_nat (a - sk_ofl_head)) ltac:(lia)) as B1.
rewrite Z2Nat.id in B0, B1 by lia. replace (sk_ofl_head + (a - sk_ofl_head)) with a in B0, B1 by lia.
change (ms_segs ubs0_msyms) with ubs0segs in *.
split; [rewrite B0, B1; reflexivity|].
cbv [sk_ofl_head ubs0_sink_head] in Hge, Hin8.
split; intros _; apply Hhw; lia. }
split.
{
intros q k i Hq _ Hi.
assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; auto).
apply (Hkeep (ptr_addr L q) k i Hin (Hbl _ Hin) Hi). intros (r & [<- | []] & Hr). cbn [fst snd sink_token] in Hr.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md (ptr_addr L q) k (conj HMR (conj HW HB)) Hin ltac:(lia)) as (H4096 & _). lia. }
split.
{
intros a [Hw | He].
- destruct Hst' as (_ & _ & _ & _ & Hsw). apply Hsw. exact Hw.
- apply Herr'. exact He. }
split; [reflexivity|]. split; [reflexivity|]. split; [cbn [ll_fs]; rewrite <- Hfs; exact Hsorted'|].
split; [exact HSN'|]. split; [exact HR'|].
intros i Hi. destruct Hpn' as [[-> _] | [Hn' Hinp]]; [lia|].
apply (Hkeep p n i Hinp (Hbl _ Hinp) Hi). intros (r & [<- | []] & Hr). cbn [fst snd sink_token] in Hr.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md p n (conj HMR (conj HW HB)) Hinp ltac:(lia)) as (H4096 & _). lia.
Qed.
End S.
End c.
Theorem ubs0_lib_contract_x_all {rc : YM05.RunCeil} (API : AllocAPI ubs0_msyms) :
img_laws ubs0_msyms (aa_MR API) ->
(forall fx : YK11.FPState, @close_specX fx rc API) ->
(forall fx : YK11.FPState, @addframe_specX fx rc API) ->
(forall fx : YK11.FPState, @rfc_specX fx rc API) ->
(forall fx : YK11.FPState, @newgif_x fx rc API) ->
@lib_contract_x_all rc ff_lib_shape ubs0_msyms API _ _ LIBPC RA_LIB EMPTY LIB_STACK.
Proof. intros IMG CLOSE ADDF RFC NEWGIF fx. exact (@ubs0_lib_contract_x fx rc API IMG (CLOSE fx) (ADDF fx) (RFC fx) (NEWGIF fx)). Qed.
