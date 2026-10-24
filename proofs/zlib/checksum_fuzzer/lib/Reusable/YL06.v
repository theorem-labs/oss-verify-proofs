(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0o YK0s YK15 YM06 YM02 YP0m YP0e YP09 YP0l YP0k YP06 YP03 YP08 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL0d YL00 YL0g YL05 YI06 YI16 YI14 YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Let LAWS := aa_laws API.
Context {SH : sink_head} {SK : sink_syms}.
Variables (pc_lib ra_lib empty stk : Z).
Hypothesis LIBX : lib_contract_x_all B API pc_lib ra_lib empty stk.
Hypothesis Hstk : 0 <= stk.
Hypothesis Hfrm : frm_zero fp_csr.
Theorem lib_site_x : forall E ss ms md L A p n pl b sp_off keep blks k l1 rs2 (K : lleaf -> TSet),
st_ok segs E ss ms -> stack_anchored E (ss_facts ss) ->
lib_site_check B pc_lib ra_lib stk ss sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 p -> getr (ms_regs ms) 11%bv = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = p)) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ ptr_addr L q <> p) ->
n = Z.of_nat (length pl) -> blk_data B (ms_mem ms) p pl ->
res_ok A b -> lib_room b n ->
sink_none B (ms_mem ms) md -> fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Fs.fs_sorted (m_fs md) = true ->
bv_unsigned (ew E 0) + sp_off <= 2 ^ 47 ->
(forall (l : lleaf) (fx' : FPState) A' L' ms' md' g,
@st_ok segs fx' (post_env E k (ms_regs ms') g) (mkSS ra_lib (ss_regs (lib_post_state ra_lib ss k rs2)) rs2 None (ss_facts ss)) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss) ->
frm_zero (@fp_csr fx') ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' -> st_init_done A' = true ->
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) ->
(forall q sz, In (q, sz) (user_blocks A) -> exists q', In (q', sz) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall q sz i, In (q, sz) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)) ->
ll_ret l = 0 -> ll_out l = [] -> Fs.fs_sorted (ll_fs l) = true ->
sink_none B (ms_mem ms') md' -> res_ok A' (lib_delta n b) ->
(forall i, 0 <= i < n -> mbyte segs (ms_mem ms') (p + i) = mbyte segs (ms_mem ms) (p + i)) ->
realizes segs (mkCfg ms' md') (K l)) ->
realizes segs (mkCfg ms md) (LIBK pl (m_fs md) K).
Proof.
intros E ss ms md L A p n pl b sp_off keep blks k l1 rs2 K HS HSA Hck Hrs2 HMR HW HB Hid Hp Hn Hpn Hblks
Hlen Hpl HRb HRm HSN Hfree Hsorted Htop HK.
destruct (lib_site_check_sound B pc_lib ra_lib stk _ _ _ _ _ _ Hck) as (Hpc & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf & Hra).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (lib_pre_intro B API ra_lib empty stk Hstk E ss ms L A md sp_off p n HS HSA HMR HW HB Hid Hcp Hp Hn Hpn) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
assert (Hprex : lib_pre_x B API stk empty L A (ms_regs ms) (ms_mem ms) md ra_lib p n pl b).
{ split; [exact Hpre|]. split; [exact Hlen|]. split; [exact Hpl|]. split; [exact HRb|]. split; [exact HRm|].
split; [exact HSN|]. split; [exact Hfree|]. split; [exact Hsorted|]. unfold spZ. rewrite Hsp. exact Htop. }
apply (LIBX fx L A (ms_regs ms) (ms_mem ms) md p n pl b K Hprex Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & -> & Hfrm' & Hpostx).
pose proof Hpostx as (HMR' & HW' & HB' & Hid' & Ha0 & Hregs & Hvm & Hstab & Hfr & Hfri & Hbk & Hscr & Hret & Hout & Hsorted' & HSN' & HRES & Hplk).
destruct (lib_post_of_x B API stk L A (ms_regs ms) (ms_mem ms) md p n b l L' A' regs' mem' md' Hpostx) as (fds1 & pins1 & Hpost).
pose proof (MR_rebase B API LAWS L A (ms_mem ms) md fds1 (ll_fs l) pins1 HMR) as HMR1.
assert (HS1 := st_ok_after_lib B API ra_lib stk k E ss (ms_regs ms) _ (ms_mem ms) (md_rebase md fds1 (ll_fs l) pins1) p L A L' A' regs' mem' md'
sp_off keep blks l1 HS HSA Hat HMR1 Hpost Hkc Herr Hsp Hsplo Hblks Hrl Hma Hcf Hra).
unfold drv_add_statics in Hrs2.
destruct (abs_region_index (map snd l1) (ms_got_guard B) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_libc B + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_guard B) 0) as [i3|]; [|discriminate].
assert (Hat3 : ss_atoms_lt (k + 16) (lib_post_state ra_lib ss k (map snd l1)) = true).
{ unfold lib_post_state. unfold ss_atoms_lt in Hat2 |- *. cbn [ss_regs ss_mem ss_facts ss_resv] in Hat2 |- *.
apply andb_prop in Hat2 as [Hat2 _]. apply andb_prop in Hat2 as [Hat2 HF']. apply andb_prop in Hat2 as [HR' HM'].
rewrite (regs_atoms_lt_set (k + 16) _ 10%bv (SLit 0) HR' eq_refl), HM', HF'. reflexivity. }
apply (st_ok_xfx fx fx') in HS1.
destruct (st_ok_statics B MR AX _ _ (@mkst fx' regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)) L' A' md' (k + 16) i1 i2 i3 rs2
HS1 HMR' Hat3 Hrs2) as (g & Hg01 & HS2).
apply (HK l fx' A' L' (@mkst fx' regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)) md' g).
- exact HS2.
- apply (stack_anchored_agree_ss k E _ ss (post_env_agree E k regs' g) Hat HSA).
- exact Hfrm'.
- exact HMR'.
- exact HW'.
- exact HB'.
- exact Hid'.
- exact Hvm.
- exact Hstab.
- cbn [ms_mem mkst]. intros a Ha Ha64 Hns.
destruct (lib_post_frame B API stk L A (ms_regs ms) (ms_mem ms) (md_rebase md fds1 (ll_fs l) pins1) p L' A' regs' mem' md' E sp_off keep blks
HMR1 Hpost Hkc Herr Hsp Hsplo Hblks) as (F1 & _).
exact (proj1 (F1 a Ha Ha64 Hns)).
- cbn [ms_mem mkst]. exact Hbk.
- exact Hret.
- exact Hout.
- exact Hsorted'.
- exact HSN'.
- exact HRES.
- cbn [ms_mem mkst]. exact Hplk.
Qed.
End d.
End c.
