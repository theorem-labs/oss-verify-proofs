(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0d.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YL0d_cfw.v, with its module paths changed; 1 of its 121 lines of code is new or changed and 1 line of the source is left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import
YK11 YK0h YK14 YK1b YK1a YK0s YK15 YM06 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import
YP0m YP0e YP09 YP0l YP06 YP03 YP04 YP01 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YN03 YL07 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YL0d YL05 YL0g YK15_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract SlotAgree MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Let LAWS := aa_laws API.
Hypothesis TBL : forall L A mem md, MR L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr segs (Z_to_bv 64 a) = true -> mbyte segs mem a = seg_rom segs (Z_to_bv 64 a).
Hypothesis FCF : free_contract_cf B API.
Lemma free_post_cf : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A',
st_ok segs E ss (mkst (ms_regs ms) (Z_to_bv 64 (ms_free B)) (ms_mem ms) (seg_rom segs)) ->
stack_anchored E (ss_facts ss)   ->
site_check B ss (ms_free B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> In (p, n) (user_blocks A) ->
bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + ALLOC_STACK <= bv_unsigned (getr (ms_regs ms) 2) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
call_post B MR L A (ms_regs ms) (ms_mem ms) md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
(forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A')) ->
exists g,
st_ok segs (post_env E k regs' g) (post_state ss ra k rs2) (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) /\
stack_anchored (post_env E k regs' g) (ss_facts ss) /\
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ (exists vm', md' = with_vmmaps vm' md) /\
(forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) /\
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs mem' a = mbyte segs (ms_mem ms) a) /\
(forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)).
Proof using AX.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hincl.
destruct (site_check_sound B ss (ms_free B) ra sp_off keep blks k l1 Hck) as (Hpc & Hra & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf).
pose proof Hpost as (HMR' & HW' & HB' & Hly & Hstab & Hregs & Hvm & _ & Hbk & _).
pose proof (mr_blocks B MR LAWS L A (ms_mem ms) md p n) as HBp.
assert (HE : forall a, ptr_addr L p <= a < ptr_addr L p + n -> 0 <= a < alloc_ceiling /\ ~ in_img B a).
{ intros a Ha. destruct (HBp (a - ptr_addr L p) HMR Hin ltac:(lia)) as (_ & H1 & H2 & _). split; [lia|].
replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia. apply (ax_blocks_img AX L A (ms_mem ms) md p n _ HMR Hin). lia. }
assert (HS1 := st_ok_after_call B MR LAWS AX k E ss (ms_regs ms) _ (ms_mem ms) md _ L A L' A' regs' mem' md'
sp_off ra keep blks l1 HS HSA Hat HMR Hpost Hkc Herr Hsp Hsplo HE
ltac:(intros kb sz Hkb; destruct (Hblks kb sz Hkb) as (q & Hq & Ha & Hqp); exists q; split; [exact Hq|]; split; [apply Hincl; assumption | exact Ha])
Hrl Hma Hcf Hra).
unfold drv_add_statics in Hrs2.
destruct (abs_region_index (map snd l1) (ms_got_guard B) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_libc B + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_guard B) 0) as [i3|]; [|discriminate].
destruct (st_ok_statics B MR AX _ _ (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) L' A' md' (k + 16) i1 i2 i3 rs2
HS1 HMR' Hat2 Hrs2) as (g & Hg01 & HS2).
exists g. split; [exact HS2|].
split; [apply (stack_anchored_agree_ss k E _ ss (post_env_agree E k regs' g) Hat HSA)|].
split; [exact HMR'|]. split; [exact HW'|]. split; [exact HB'|]. split; [exact Hvm|].
split; [intros q sz Hq Hqp; split; [apply Hincl; assumption | apply (Hstab q sz Hq (Hincl q sz Hq Hqp))]|].
split.
- intros a Ha Ha64 Hns.
destruct (call_post_frame B MR LAWS AX L A (ms_regs ms) (ms_mem ms) md _ L' A' regs' mem' md' E sp_off keep blks
HMR Hpost Hkc Herr Hsp Hsplo HE
ltac:(intros kb sz Hkb; destruct (Hblks kb sz Hkb) as (q & Hq & Ha' & Hqp); exists q; split; [exact Hq|]; split; [apply Hincl; assumption | exact Ha'])) as (F1 & _).
exact (proj1 (F1 a Ha Ha64 Hns)).
- intros q sz i Hq Hqp Hi. exact (Hbk q sz i Hq (Hincl q sz Hq Hqp) Hi).
Qed.
Theorem free_site_cf : forall E ss ms md L A p n b sp_off keep blks k l1 rs2 ra T,
st_ok segs E ss ms -> stack_anchored E (ss_facts ss) ->
site_check B ss (ms_free B) ra sp_off keep blks k l1 = true ->
ro_check B (ss_mem ss) = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
In (p, n) (user_blocks A) ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L p) ->
res_ok_slots A b ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
(forall A' L' ms' md' g,
st_ok segs (post_env E k (ms_regs ms') g) (post_state ss ra k rs2) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss) ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
(forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)) ->
res_ok_slots A' (sb_free b n) ->
crealizes B (mkCfg ms' md') T) ->
crealizes B (mkCfg ms md) T.
Proof using AX FCF TBL.
intros E ss ms md L A p n b sp_off keep blks k l1 rs2 ra T HS HSA Hck Hro Hrs2 HMR HW HB Hid Hin Ha0 Hres Hblks HK.
destruct (site_check_sound B ss (ms_free B) ra sp_off keep blks k l1 Hck) as (Hpc & Hra & Hrv & Hcp & _).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
assert (Hrag : ro_agree segs (ms_mem ms)).
{ apply (ro_agree_of_rodata_ok B (ms_mem ms)); [| exact (TBL L A (ms_mem ms) md HMR)].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
exact (ro_check_sound B E (ms_mem ms) (ss_mem ss) (proj1 (proj2 HM)) Hro). }
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (FCF L A (ms_regs ms) (ms_mem ms) md p n b Hpre Hrag Hin Ha0 Hres T).
intros c' (L' & A' & regs' & mem' & md' & -> & Hpost & _ & _ & _ & _ & Hincl & _ & _ & Hres').
destruct (free_post_cf E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hincl)
as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
exact (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) md' g HS2 HSA2 HMR' HW' HB' Hvm Hkeep Hhi Hbk Hres').
Qed.
End d.
End c.
