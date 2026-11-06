(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0o.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK18 YK0j YP0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Lemma wvb_wvb : forall l X Y m,
with_vm_backing l X (with_vm_backing l Y m) = with_vm_backing l X m.
Proof. intros l X Y [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma wvb_collapse : forall l X Y m,
with_vm_backing (m_vm_lazy (with_vm_backing l Y m)) X (with_vm_backing l Y m)
= with_vm_backing l X m.
Proof. intros l X Y m. rewrite m_vm_lazy_wvb. apply wvb_wvb. Qed.
Lemma same_but_materialized_wvb : forall m m',
same_but_materialized m m' -> m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.
Proof. intros m m' H. exact H. Qed.
Section d.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma mrestrict_hsub : forall (H H' : word -> bool) m a b,
hsub H' H -> mrestrict H m a = Some b -> mrestrict H' m a = Some b.
Proof.
intros H H' m a b Hs Hb. unfold mrestrict in *.
destruct (H a) eqn:E; [discriminate|].
destruct (H' a) eqn:E'; [|exact Hb]. rewrite (Hs a E') in E. discriminate.
Qed.
Lemma mem_grows_mrestrict_hsub : forall (H H' : word -> bool) m,
hsub H' H -> mem_grows (mrestrict H m) (mrestrict H' m).
Proof.
intros H H' m Hs x Hx. destruct (mrestrict H m x) as [b|] eqn:E; [|exfalso; exact (Hx eq_refl)].
rewrite (mrestrict_hsub H H' m x b Hs E). discriminate.
Qed.
Lemma seg_rom_hidden : forall (H : word -> bool) a,
H_off_segments segs H -> H a = true -> seg_rom segs a = None.
Proof.
intros H a HH Ha. unfold seg_rom. unfold memory_read. cbn [Z.of_N].
rewrite (HH a Ha). reflexivity.
Qed.
Lemma mbyte_mrestrict_hsub : forall (H H' : word -> bool) m a b,
H_off_segments segs H -> hsub H' H ->
mbyte segs (mrestrict H m) a = Some b -> mbyte segs (mrestrict H' m) a = Some b.
Proof.
intros H H' m a b HH Hs Hb. unfold mbyte, mrestrict in *.
destruct (H' (Z_to_bv 64 a)) eqn:E'.
- rewrite (Hs _ E') in Hb. rewrite (seg_rom_hidden H _ HH (Hs _ E')) in Hb. discriminate.
- destruct (H (Z_to_bv 64 a)) eqn:E; [|exact Hb].
rewrite (seg_rom_hidden H _ HH E) in Hb. discriminate.
Qed.
Lemma mrestrict_visible_eq : forall (H : word -> bool) m a,
H a = false -> mrestrict H m a = m a.
Proof. intros H m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.
Lemma mbyte_mrestrict_visible : forall (H : word -> bool) m a,
H (Z_to_bv 64 a) = false -> mbyte segs (mrestrict H m) a = mbyte segs m a.
Proof. intros H m a Ha. unfold mbyte. rewrite (mrestrict_visible_eq H m _ Ha). reflexivity. Qed.
Lemma mbyte_mrestrict_some : forall (H : word -> bool) m a b,
H_off_segments segs H ->
mbyte segs (mrestrict H m) a = Some b -> mbyte segs m a = Some b /\ H (Z_to_bv 64 a) = false.
Proof.
intros H m a b HH Hb. destruct (H (Z_to_bv 64 a)) eqn:E.
- unfold mbyte, mrestrict in Hb. rewrite E, (seg_rom_hidden H _ HH E) in Hb. discriminate.
- rewrite (mbyte_mrestrict_visible H m a E) in Hb. auto.
Qed.
Lemma writable_at_mrestrict_hsub : forall (H H' : word -> bool) m a,
hsub H' H -> writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H' m) a.
Proof.
intros H H' m a Hs Hw. unfold writable_at in *.
eapply wview_grows; [apply (mem_grows_mrestrict_hsub H H' m Hs) | exact Hw].
Qed.
Lemma region_ok_mrestrict_hsub : forall (H H' : word -> bool) E m r,
H_off_segments segs H -> hsub H' H ->
region_ok segs E (mrestrict H m) r -> region_ok segs E (mrestrict H' m) r.
Proof.
intros H H' E m r HH Hs (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (writable_at_mrestrict_hsub H H'); [exact Hs | exact (H3 o Ho)].
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
exact (mbyte_mrestrict_hsub H H' m _ b HH Hs Hb2).
Qed.
Lemma mem_ok_mrestrict_hsub : forall (H H' : word -> bool) E m rs,
H_off_segments segs H -> hsub H' H ->
mem_ok segs E (mrestrict H m) rs -> mem_ok segs E (mrestrict H' m) rs.
Proof.
intros H H' E m rs HH Hs (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hr.
exact (region_ok_mrestrict_hsub H H' E m r HH Hs (Hok r Hr)).
Qed.
Lemma st_ok_hsub : forall (H H' : word -> bool) E ss ms,
H_off_segments segs H -> hsub H' H ->
st_ok segs E ss (restrict H ms) -> st_ok segs E ss (restrict H' ms).
Proof.
intros H H' E ss ms HH Hs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in *.
repeat (split; [assumption|]). split; [|exact H9].
exact (mem_ok_mrestrict_hsub H H' E (ms_mem ms) (ss_mem ss) HH Hs H8).
Qed.
Lemma st_ok_ecall_hsub : forall (H H' : word -> bool) E ss ms,
H_off_segments segs H -> hsub H' H ->
st_ok_ecall segs E ss (restrict H ms) -> st_ok_ecall segs E ss (restrict H' ms).
Proof.
intros H H' E ss ms HH Hs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok_ecall. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in *.
repeat (split; [assumption|]). split; [|exact H9].
exact (mem_ok_mrestrict_hsub H H' E (ms_mem ms) (ss_mem ss) HH Hs H8).
Qed.
Lemma st_ok_wle : forall (W W' : world segs) E ss ms,
wle W W' -> st_ok segs E ss (restrict (w_H W) ms) -> st_ok segs E ss (restrict (w_H W') ms).
Proof.
intros W W' E ss ms Hs HS. exact (st_ok_hsub (w_H W) (w_H W') E ss ms (w_Hoff W) Hs HS).
Qed.
Definition regions_visible (H : word -> bool) (E : env) (rs : smem) : Prop :=
forall r a, In r rs ->
base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
H (Z_to_bv 64 a) = false.
Lemma mem_ok_restrict_intro : forall (H : word -> bool) E m rs,
mem_ok segs E m rs -> regions_visible H E rs -> mem_ok segs E (mrestrict H m) rs.
Proof.
intros H E m rs (Hwf & Hok & Hpd) Hvis. split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hr. destruct (Hok r Hr) as (H1 & H2 & H3 & H4).
pose proof (regions_wf_In _ _ Hwf Hr) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hw & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. specialize (H3 o Ho). unfold writable_at, wview in *.
rewrite (mrestrict_visible_eq H m) by (apply (Hvis r); [exact Hr | lia]). exact H3.
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
rewrite (mbyte_mrestrict_visible H m) by (apply (Hvis r); [exact Hr | lia]). exact Hb2.
Qed.
Lemma st_ok_restrict_intro : forall (H : word -> bool) E ss ms,
st_ok segs E ss ms -> regions_visible H E (ss_mem ss) -> st_ok segs E ss (restrict H ms).
Proof.
intros H E ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hvis.
unfold st_ok. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
repeat (split; [assumption|]). split; [|exact H9].
exact (mem_ok_restrict_intro H E (ms_mem ms) (ss_mem ss) H8 Hvis).
Qed.
Lemma st_ok_restrict_reg : forall (H : word -> bool) E ss ms r,
st_ok segs E ss (restrict H ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros H E ss ms r HS. exact (st_ok_reg segs E ss (restrict H ms) r HS). Qed.
Lemma st_ok_restrict_pc : forall (H : word -> bool) E ss ms,
st_ok segs E ss (restrict H ms) -> ms_pc_val ms = Z_to_bv 64 (ss_pc ss).
Proof. intros H E ss ms HS. exact (st_ok_pc segs E ss (restrict H ms) HS). Qed.
Lemma st_ok_restrict_mkst : forall (H : word -> bool) E ss ms,
st_ok segs E ss (restrict H ms) -> ss_resv ss = None ->
ms = mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs).
Proof.
intros H E ss ms (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & _) Hrv.
destruct ms as [regs fregs pcv pend resv fcsr mem rom]; cbn in *.
rewrite Hrv in Hresv. cbn in Hresv. subst. reflexivity.
Qed.
Lemma frame_of_unrestrict : forall (H : word -> bool) E rs mem msr',
frame_of E rs (mrestrict H mem) (ms_mem msr') ->
frame_of E rs mem (munrestrict H mem (ms_mem msr')).
Proof.
intros H E rs mem msr' Hfr x Hx. unfold munrestrict.
destruct (H x) eqn:Ex; [reflexivity|].
rewrite (Hfr x Hx). unfold mrestrict. rewrite Ex. reflexivity.
Qed.
Definition rs_read_only (rs : smem) : bool := forallb (fun r => r_whi r <=? r_wlo r) rs.
Lemma frame_of_read_only : forall E rs (m m' : word -> option byte),
rs_read_only rs = true -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro HF. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Hx). unfold rs_read_only in Hro. rewrite forallb_forall in Hro.
specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Definition run_post (W : world segs) (E : env) (ss ss' : sstate) (st : run_status)
(ms : machine_state) (model : Model) (Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
match st with RS_ecall => st_ok_ecall segs E ss' (restrict (w_H W) ms')
| _ => st_ok segs E ss' (restrict (w_H W) ms') end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q.
Lemma SRr_of_restricted_chain : forall W E ss ss' st ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
match st with RS_ecall => st_ok_ecall segs E ss' msr' | _ => st_ok segs E ss' msr' end ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
run_post W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W E ss ss' st ms msr' model Q Hms HS' Hfr Hk.
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact Hfr.
Qed.
Lemma SRr_run_gen : forall W n E ss ss' st ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
run_post W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chain W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
Lemma SRr_run_stop : forall W n E ss ss' why ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', RS_stopped why) ->
run_post W E ss ss' (RS_stopped why) ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof. intros W n E ss ss' why. exact (SRr_run_gen W n E ss ss' (RS_stopped why)). Qed.
Lemma SRr_run_running : forall W n E ss ss' ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', RS_running) ->
run_post W E ss ss' RS_running ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof. intros W n E ss ss'. exact (SRr_run_gen W n E ss ss' RS_running). Qed.
Lemma SRr_run_ecall : forall W n E ss ss' ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
run_post W E ss ss' RS_ecall ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof. intros W n E ss ss'. exact (SRr_run_gen W n E ss ss' RS_ecall). Qed.
Lemma SRr_run_to_gen : forall W n stop E ss ss' st ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
run_post W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n stop E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chain W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
Lemma SRr_msteps_st : forall W E ss' ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
(forall ms' mat', st_ok segs E ss' (restrict (w_H W) ms') ->
(forall x, w_H W x = false -> ms_mem ms' x = ms_mem msr' x) ->
(forall x, w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
ms_regs ms' = ms_regs msr' ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q) ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W E ss' ms msr' model Q Hms HS' Hk.
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
apply Hk.
- rewrite Hrr. exact HS'.
- intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
- intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
- reflexivity.
Qed.
Lemma SRr_sym_branch : forall W E ss ms model Q c a b,
st_ok segs E ss (restrict (w_H W) ms) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) ->
SRr segs W (mkCfg ms model) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) ->
SRr segs W (mkCfg ms model) Q) ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W E ss ms model Q c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_ok_add_cond; [exact HS | exact Hb].
- apply Hf; [reflexivity|]. apply st_ok_add_cond_neg; [exact HS | exact Hb].
Qed.
Lemma SRr_st_ok_ret : forall W (Q : world segs -> config -> Prop) ms model,
Q W (mkCfg ms model) -> SRr segs W (mkCfg ms model) Q.
Proof. intros W Q ms model HQ. apply SRr_ret. exact HQ. Qed.
Lemma st_ok_ecall_shape_r : forall (H : word -> bool) E ss ms,
st_ok_ecall segs E ss (restrict H ms) -> ss_resv ss = None ->
exists regs mem,
ms = pend_at regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs)
/\ regs_ok E (ss_regs ss) regs
/\ mem_ok segs E (mrestrict H mem) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Proof.
intros H E ss ms HS Hrv.
destruct (st_ok_ecall_shape segs E ss (restrict H ms) HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
exists (ms_regs ms), (ms_mem ms).
assert (Hregs' : regs = ms_regs ms) by (apply (f_equal ms_regs) in Hms; exact (eq_sym Hms)).
assert (Hmem' : mem = mrestrict H (ms_mem ms)) by (apply (f_equal ms_mem) in Hms; exact (eq_sym Hms)).
subst regs mem. split; [|auto].
destruct ms as [rg fr pcv svc rsv fcsr mm rom]. unfold restrict, pend_at in Hms |- *. cbn in *.
pose proof (f_equal ms_fregs Hms) as E1. pose proof (f_equal ms_pc_val Hms) as E2.
pose proof (f_equal ms_svc_pending Hms) as E3. pose proof (f_equal ms_resv Hms) as E4.
pose proof (f_equal ms_fcsr Hms) as E5. pose proof (f_equal ms_rom Hms) as E6.
cbn in E1, E2, E3, E4, E5, E6. subst. reflexivity.
Qed.
Definition RET_WORD_r : Z := 0x00008067.
Lemma decode_ret_r : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma restrict_mkst_fx : forall (H : word -> bool) regs pc mem rom,
restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom.
Proof. reflexivity. Qed.
Lemma unrestrict_mkst_mrestrict : forall (H : word -> bool) regs pc mem rom,
unrestrict H mem (mkst regs pc (mrestrict H mem) rom) = mkst regs pc mem rom.
Proof.
intros H regs pc mem rom. unfold unrestrict, mkst. cbn. rewrite munrestrict_mrestrict. reflexivity.
Qed.
Lemma SRr_ret_raw : forall (W : world segs) regs pc mem md Q,
clookup tbl (bv_unsigned pc) = Some RET_WORD_r ->
(forall mat', Q W (mkCfg (mkst regs (v_jalr (getr regs 1) 0) mem (seg_rom segs))
(with_vm_backing (m_vm_lazy md) mat' md))) ->
SRr segs W (mkCfg (mkst regs pc mem (seg_rom segs)) md) Q.
Proof.
intros W regs pc mem md Q Hpc HQ.
eapply (SRr_step segs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. change 0 with (bv_signed (0%bv : bv 12)).
eapply (step_jalr_x0 segs _ _ _ _ (0x00008067%bv : bv 32) 1 (0%bv : bv 12)).
+ rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)), <- (Z_to_bv_bv_unsigned 64 pc).
apply tbl_ok. exact Hpc.
+ reflexivity.
+ exact decode_ret_r.
+ reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. apply SRr_ret. apply HQ.
Qed.
Lemma SRr_ret_at : forall W E ss ms md Q,
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
clookup tbl (ss_pc ss) = Some RET_WORD_r ->
(forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom segs))
(with_vm_backing (m_vm_lazy md) mat' md))) ->
SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q HS Hrv Hpc HQ.
pose proof (st_ok_restrict_mkst (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hshape.
eapply (SRr_step segs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. change 0 with (bv_signed (0%bv : bv 12)).
eapply (step_jalr_x0 segs _ _ _ _ (0x00008067%bv : bv 32) 1 (0%bv : bv 12)).
+ rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply tbl_ok. exact Hpc.
+ reflexivity.
+ exact decode_ret_r.
+ reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. apply SRr_ret. apply HQ.
Qed.
End d.
Ltac srr_norm_model :=
repeat rewrite wvb_collapse;
repeat match goal with
| mat : list word |- _ =>
lazymatch goal with
| |- context [mat] => fail
| _ => first [ clear mat | fail 1 ]
end
end.
Ltac srr_after_run HS :=
let ms' := fresh "ms" in let mat' := fresh "mat" in
let HF := fresh "HF" in let HFr := fresh "HFr" in
intros ms' mat' HS HF HFr;
cbn [ms_mem mkst pend_at] in HF, HFr;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac srr_run_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_with: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_gen segs tbl tblok HWX W FUEL E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
srr_after_run HS
end
end
| _ => fail "srr_run_with: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac srr_run_to_with tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_to_with: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_to_gen segs tbl tblok HWX W FUEL stop E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
cbv beta iota;
srr_after_run HS
end
end
| _ => fail "srr_run_to_with: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac srr_branch_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SRr_sym_branch segs W E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "srr_branch: state is not stuck at a branch:" why
end
end
end.
