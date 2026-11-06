(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/Reusable/YL0d.v; 28 of its 170 lines of code are new or changed and 127 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK14 YK1b YK1a YK0s YK15 YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP0l YP06 YP03 YP04 YP01 YN3v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0d_mf.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN03 YL07 YL01 YL0d YL0e_mf.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Let LAWS := aa_laws API.
Hypothesis HAM : amf = true.
Hypothesis Hmal : forall fx' : FPState, malloc_realizes (fx:=fx') (AM:=AM) B MR.
Hypothesis Hfre : forall fx' : FPState, free_realizes (fx:=fx') (AM:=AM) B MR.
Theorem malloc_site_mf : forall E ss ms md L A n sp_off keep blks k l1 rs2 ra (K : option sptr * astate -> TSet),
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
site_check B ss (ms_malloc B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (bv_unsigned (ew E 0) + sp_off) (ms_mem ms)) ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
(forall kb sz, In (kb, sz) blks -> exists p, In (p, sz) (user_blocks A) /\ ptr_addr L p = bv_unsigned (ew E kb)) ->
(forall res A' L' ms' md' g tr,
st_ok segs (post_env E k (ms_regs ms') g) (post_state ss ra k rs2) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss)   ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
cpath (malloc n A) tr (res, A') ->
(forall p sz, In (p, sz) (user_blocks A) -> In (p, sz) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall p sz i, In (p, sz) (user_blocks A) -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L p + i) = mbyte segs (ms_mem ms) (ptr_addr L p + i)) ->
match res with
| None => getr (ms_regs ms') 10%bv = Z_to_bv 64 0 /\ user_blocks A' = user_blocks A
| Some q => getr (ms_regs ms') 10%bv = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
exists b1 b2, user_blocks A' = b1 ++ (q, n) :: b2 /\ user_blocks A = b1 ++ b2
end ->
realizes segs (mkCfg ms' md') (K (res, A'))) ->
realizes segs (mkCfg ms md) (tset_mf (malloc n A) K).
Proof using AX HAM Hmal.
intros E ss ms md L A n sp_off keep blks k l1 rs2 ra K HS HSA Hck Hrs2 HMR HW HB Haux Ha0 Hn Hblks HK.
destruct (site_check_sound B _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB Haux Hcp) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (mreal_tset_g segs _ _ _ K HAM (Hmal _ L A (ms_regs ms) (ms_mem ms) md n Hpre Ha0 Hn)); [apply malloc_safe; [exact HW | lia] |].
intros [res A'] c' tr Hpath (L' & regs' & mem' & md' & -> & Hpost & Hres). cbn [fst snd] in Hres.
assert (Hincl : forall p sz, In (p, sz) (user_blocks A) -> In (p, sz) (user_blocks A')).
{ intros p sz Hin. destruct res as [q|].
- destruct Hres as (_ & _ & (b1 & b2 & Ea & Eb) & _). rewrite Eb in Hin. rewrite Ea.
apply in_app_iff in Hin. apply in_app_iff. destruct Hin; [left; assumption | right; right; assumption].
- destruct Hres as [_ Eb]. rewrite Eb. exact Hin. }
pose proof Hpost as (HMR' & HW' & HB' & Hly & Hstab & Hregs & Hvm & _).
assert (HS1 := st_ok_after_call B MR LAWS AX k E ss (ms_regs ms) _ (ms_mem ms) md (fun _ => False) L A L' A' regs' mem' md'
sp_off ra keep blks l1 HS HSA Hat HMR Hpost Hkc Herr Hsp Hsplo
ltac:(intros a F; destruct F)
ltac:(intros kb sz Hin; destruct (Hblks kb sz Hin) as (p & Hp & Ha); exists p; auto)
Hrl Hma Hcf Hra).
unfold drv_add_statics in Hrs2.
destruct (abs_region_index (map snd l1) (ms_got_guard B) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_libc B + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_guard B) 0) as [i3|]; [|discriminate].
destruct (st_ok_statics B MR AX _ _ (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) L' A' md' (k + 16) i1 i2 i3 rs2
HS1 HMR' Hat2 Hrs2) as (g & Hg01 & HS2).
apply (HK res A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) md' g tr).
- exact HS2.
- apply (stack_anchored_agree_ss k E _ ss (post_env_agree E k regs' g) Hat HSA).
- exact HMR'.
- exact HW'.
- exact HB'.
- exact Hvm.
- exact Hpath.
- intros p sz Hin. split; [apply Hincl; exact Hin | apply (Hstab p sz Hin (Hincl p sz Hin))].
- cbn [ms_mem mkst]. intros a Ha Ha64 Hns.
destruct (call_post_frame B MR LAWS AX L A (ms_regs ms) (ms_mem ms) md (fun _ => False) L' A' regs' mem' md' E sp_off keep blks
HMR Hpost Hkc Herr Hsp Hsplo ltac:(intros b F; destruct F)
ltac:(intros kb sz Hin; destruct (Hblks kb sz Hin) as (p & Hp & Hb); exists p; auto)) as (F1 & _).
exact (proj1 (F1 a Ha Ha64 Hns)).
- cbn [ms_mem mkst]. intros p sz i Hin Hi. destruct Hpost as (_ & _ & _ & _ & _ & _ & _ & _ & Hbk & _).
exact (Hbk p sz i Hin (Hincl p sz Hin) Hi).
- destruct res as [q|]; [| exact Hres].
destruct Hres as (H1 & H2 & H3 & _). exact (conj H1 (conj H2 H3)).
Qed.
Theorem free_site_mf : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra T,
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
site_check B ss (ms_free B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
In (p, n) (user_blocks A) ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L p) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
(forall A' L' ms' md' g tr,
st_ok segs (post_env E k (ms_regs ms') g) (post_state ss ra k rs2) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss)   ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
cpath (free (Some p) A) tr (tt, A') ->
(exists b1 b2, user_blocks A = b1 ++ (p, n) :: b2 /\ user_blocks A' = b1 ++ b2) ->
(forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg ms md) T.
Proof using AX Hfre.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra T HS HSA Hck Hrs2 HMR HW HB Hid Hin Ha0 Hblks HK.
destruct (site_check_sound B _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & _).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (SR_realizes segs _ _ T (mreal_SR segs _ _ _ (Hfre _ L A (ms_regs ms) (ms_mem ms) md p n Hpre Hin Ha0) ltac:(eapply free_safe; [exact HW | exact Hin]))).
intros c' ([[] A'] & tr & Hpath & (L' & regs' & mem' & md' & -> & Hpost & Hub)). cbn [fst snd] in Hub.
destruct (free_post B API AX E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hub)
as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
exact (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) md' g tr HS2 HSA2 HMR' HW' HB' Hvm Hpath Hub Hkeep Hhi Hbk).
Qed.
Theorem free_site_tset_mf : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra (K : unit * astate -> TSet),
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
site_check B ss (ms_free B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
In (p, n) (user_blocks A) ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L p) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
(forall A' L' ms' md' g tr,
st_ok segs (post_env E k (ms_regs ms') g) (post_state ss ra k rs2) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss)   ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
cpath (free (Some p) A) tr (tt, A') ->
(exists b1 b2, user_blocks A = b1 ++ (p, n) :: b2 /\ user_blocks A' = b1 ++ b2) ->
(forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)) ->
realizes segs (mkCfg ms' md') (K (tt, A'))) ->
realizes segs (mkCfg ms md) (tset_mf (free (Some p) A) K).
Proof using AX HAM Hfre.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra K HS HSA Hck Hrs2 HMR HW HB Hid Hin Ha0 Hblks HK.
destruct (site_check_sound B _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & _).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (mreal_tset_g segs _ _ _ K HAM (Hfre _ L A (ms_regs ms) (ms_mem ms) md p n Hpre Hin Ha0)); [eapply free_safe; [exact HW | exact Hin] |].
intros [[] A'] c' tr Hpath (L' & regs' & mem' & md' & -> & Hpost & Hub). cbn [fst snd] in Hub.
destruct (free_post B API AX E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hub)
as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
exact (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) md' g tr HS2 HSA2 HMR' HW' HB' Hvm Hpath Hub Hkeep Hhi Hbk).
Qed.
End d.
End c.
