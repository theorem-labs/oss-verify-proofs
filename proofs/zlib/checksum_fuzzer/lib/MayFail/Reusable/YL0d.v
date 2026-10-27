(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0d.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
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
Definition site_check (ss : sstate) (pc ra : Z) (sp_off : Z) (keep : ivl) (blks : list (nat * Z))
(k : nat) (l1 : list (nat * YP09.region)) : bool :=
(ss_pc ss =? pc) && sv_eqb (sr_get (ss_regs ss) 1) (SLit ra) &&
match ss_resv ss with None => true | Some _ => false end &&
call_pre_check B ss sp_off &&
keep_check B keep && (errno_addr B + 4 <=? CEIL_MIN) &&
relayout_ok segs (ss_mem ss) l1 &&
ss_atoms_lt k ss && mem_atoms_lt k (map snd l1) &&
ss_atoms_lt (k + 16) (mkSS ra (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss)) &&
call_frame_check (ss_facts ss) sp_off ALLOC_STACK keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1).
Definition post_state (ss : sstate) (ra : Z) (k : nat) (rs2 : smem) : sstate :=
mkSS ra (sr_sets (ss_regs ss) (junk_upd k caller_saved)) rs2 None (ss_facts ss).
Definition post_env (E : env) (k : nat) (regs' : bvmap 5 word) (g : Z) : env :=
ewset (havoc E k (map (getr regs') caller_saved)) (k + 16) (Z_to_bv 64 g).
Lemma post_env_agree : forall E k regs' g, env_agree k E (post_env E k regs' g).
Proof.
intros E k regs' g. unfold post_env. eapply env_agree_trans; [apply env_agree_havoc|].
eapply env_agree_le; [| apply env_agree_ewset]. lia.
Qed.
Lemma post_env_a0 : forall E k regs' g, ew (post_env E k regs' g) (k + 4)%nat = getr regs' 10%bv.
Proof.
intros E k regs' g. unfold post_env. rewrite ew_ewset_other by lia.
rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (cbn; lia). reflexivity.
Qed.
Lemma post_state_a0 : forall ss ra k rs2, sr_get (ss_regs (post_state ss ra k rs2)) 10%bv = SOff (k + 4) 0.
Proof.
intros ss ra k rs2. unfold post_state. cbn [ss_regs].
unfold caller_saved. cbn [junk_upd sr_sets].
rewrite !sr_get_set_other by (intros H; discriminate H).
rewrite sr_get_set_same by reflexivity.
f_equal. lia.
Qed.
Lemma site_check_sound : forall ss pc ra sp_off keep blks k l1,
site_check ss pc ra sp_off keep blks k l1 = true ->
ss_pc ss = pc /\ sr_get (ss_regs ss) 1 = SLit ra /\ ss_resv ss = None /\
call_pre_check B ss sp_off = true /\ keep_check B keep = true /\ errno_addr B + 4 <= alloc_ceiling /\
relayout_ok segs (ss_mem ss) l1 = true /\ ss_atoms_lt k ss = true /\ mem_atoms_lt k (map snd l1) = true /\
ss_atoms_lt (k + 16) (mkSS ra (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss)) = true /\
call_frame_check (ss_facts ss) sp_off ALLOC_STACK keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1) = true.
Proof.
intros ss pc ra sp_off keep blks k l1 H. unfold site_check in H.
repeat match type of H with _ && _ = true => apply andb_prop in H as [H ?X] end.
apply Z.eqb_eq in H. apply sv_eqb_eq in X8.
destruct (ss_resv ss); [discriminate|]. apply Z.leb_le in X4.
pose proof YM05.alloc_ceiling_val.
repeat split; try assumption. lia.
Qed.
Theorem malloc_site : forall E ss ms md L A n sp_off keep blks k l1 rs2 ra (K : option sptr * astate -> TSet),
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
site_check ss (ms_malloc B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (bv_unsigned (ew E 0) + sp_off) (ms_mem ms)) ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
(forall kb sz, In (kb, sz) blks -> exists p, In (p, sz) (user_blocks A) /\ ptr_addr L p = bv_unsigned (ew E kb)) ->
jinv K (malloc n A) -> gtree mgrant (malloc n A) ->
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
realizes segs (mkCfg ms md) (tset (malloc n A) K).
Proof.
intros E ss ms md L A n sp_off keep blks k l1 rs2 ra K HS HSA Hck Hrs2 HMR HW HB Haux Ha0 Hn Hblks Hj Hg HK.
destruct (site_check_sound _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB Haux Hcp) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (malloc_tset B MR (aa_malloc API) L A (ms_regs ms) (ms_mem ms) md n K Hpre Ha0 Hn Hj Hg).
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
Lemma free_post : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A',
st_ok segs E ss (mkst (ms_regs ms) (Z_to_bv 64 (ms_free B)) (ms_mem ms) (seg_rom segs)) ->
stack_anchored E (ss_facts ss)   ->
site_check ss (ms_free B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> In (p, n) (user_blocks A) ->
bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + ALLOC_STACK <= bv_unsigned (getr (ms_regs ms) 2) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
call_post B MR L A (ms_regs ms) (ms_mem ms) md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
(exists b1 b2, user_blocks A = b1 ++ (p, n) :: b2 /\ user_blocks A' = b1 ++ b2) ->
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
Proof.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost (b1 & b2 & Ea & Eb).
destruct (site_check_sound _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf).
assert (Hincl : forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A')).
{ intros q sz Hq Hqp. rewrite Eb. rewrite Ea in Hq. apply in_app_iff in Hq. apply in_app_iff.
destruct Hq as [H|[H|H]]; [left; exact H | exfalso; apply Hqp; congruence | right; exact H]. }
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
Theorem free_site : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra T,
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
site_check ss (ms_free B) ra sp_off keep blks k l1 = true ->
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
Proof.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra T HS HSA Hck Hrs2 HMR HW HB Hid Hin Ha0 Hblks HK.
destruct (site_check_sound _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & _).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (SR_realizes segs _ _ T (free_SR B MR (aa_free API) L A (ms_regs ms) (ms_mem ms) md p n Hpre Hin Ha0)).
intros c' ([[] A'] & tr & Hpath & (L' & regs' & mem' & md' & -> & Hpost & Hub)). cbn [fst snd] in Hub.
destruct (free_post E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hub)
as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
exact (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) md' g tr HS2 HSA2 HMR' HW' HB' Hvm Hpath Hub Hkeep Hhi Hbk).
Qed.
Theorem free_site_tset : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra (K : unit * astate -> TSet),
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
site_check ss (ms_free B) ra sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
In (p, n) (user_blocks A) ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L p) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
jinv K (free (Some p) A) -> gtree mgrant (free (Some p) A) ->
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
realizes segs (mkCfg ms md) (tset (free (Some p) A) K).
Proof.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra K HS HSA Hck Hrs2 HMR HW HB Hid Hin Ha0 Hblks Hj Hg HK.
destruct (site_check_sound _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & _).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (call_pre_intro B MR E ss ms L A md sp_off HS HSA HMR HW HB ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (free_tset B MR (aa_free API) L A (ms_regs ms) (ms_mem ms) md p n K Hpre Hin Ha0 Hj Hg).
intros [[] A'] c' tr Hpath (L' & regs' & mem' & md' & -> & Hpost & Hub). cbn [fst snd] in Hub.
destruct (free_post E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A' HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hub)
as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
exact (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom segs)) md' g tr HS2 HSA2 HMR' HW' HB' Hvm Hpath Hub Hkeep Hhi Hbk).
Qed.
End d.
End c.
