(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_headamp/lib/Reusable/YL0n.v, with its module paths and module names changed; 34 of its 171 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/Reusable/YL0n_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Uaccess.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0a YL0k YL0p.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YM0b.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO03 YO0o YO04 YO0d_cf YO04_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL0n YL0d2_cfw YN34b_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YP0n2_cfw SymTac_cfw YL0k_cfw YL0p_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma room_m1 : room (RB 0 0 0 0) CAP0.
Proof using.
unfold room, CAP0. cbn -[Z.le Z.lt Z.add Z.mul Z.max Z.pow Z.div]. unfold MG_LIVE, MG_SLOTS, MG_REQ, MMAX, PGSZ, shcap, METAS_PER_AREA, page_round, IB, UNIT, PGSZ. cbn. lia.
Qed.
Lemma roomcf_malloc1 : roomcf SRC_LIM_MIN (malloc CAP0 init_state).
Proof using.
apply (roomcf_malloc_res init_state (RB 0 0 0 0) CAP0 SRC_LIM_MIN wf_init res_ok_init room_m1).
apply Z.leb_le. vm_compute. reflexivity.
Qed.
Section M1.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Variables (sp brk mbase tid : word) (lim : Z) (argv envp : list (list byte)) (rnd : EntryDraw).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk src0segs brk.
Hypothesis Hlim : SRC_LIM_MIN <= lim.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfits : entry_stack_fits sp argv envp.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
Hypothesis Hrclim : YM05.rc_lim = lim.
Theorem src0_malloc1_cf : forall ms md (K : option sptr * astate -> TSet),
m_vmmaps md = mkVmMapsFull (segments_reserved src0segs) [] [] brk brk lim mbase sp ->
m_halted md = None -> m_vm_lazy md = [] -> m_vm_materialized md = [] ->
st_ok src0segs (E_main sp argv envp tid rnd) ss_m1 ms ->
jinv K (malloc CAP0 init_state) ->
(forall res A' L' ms' md' g tr,
st_ok src0segs (E_m1 sp tid argv envp rnd (ms_regs ms') g) ss_m1_post ms' ->
stack_anchored (E_m1 sp tid argv envp rnd (ms_regs ms') g) (ss_facts ss_m1_post) ->
aa_MR API L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
cpath (malloc CAP0 init_state) tr (res, A') ->
(forall a, alloc_ceiling <= a -> bv_unsigned sp <= a -> a < 2 ^ 64 -> mbyte src0segs (ms_mem ms') a = mbyte src0segs (ms_mem ms) a) ->
match res with
| None => getr (ms_regs ms') 10%bv = Z_to_bv 64 0 /\ user_blocks A' = user_blocks init_state
| Some q => getr (ms_regs ms') 10%bv = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
exists b1 b2, user_blocks A' = b1 ++ (q, CAP0) :: b2 /\ user_blocks init_state = b1 ++ b2
end ->
crealizes src0_msyms (mkCfg ms' md') (K (res, A'))) ->
crealizes src0_msyms (mkCfg ms md) (tset (malloc CAP0 init_state) K).
Proof using AX MRC LIMLAW Hsp Hbrk Hlim Hva Hve Hceil Hrclim.
intros ms md K Hvm Hh Hlz Hmat HS Hj HK.
assert (HP : heap_pristine src0_msyms (ms_mem ms) md).
{ eapply (heap_pristine_intro src0_msyms _ (ms_mem ms) _ _ (st_ok_mem_ok src0segs _ _ _ HS) pristine_m1);
rewrite ?Hvm; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_limit].
- reflexivity. - reflexivity. - reflexivity.
- exact Hbrk.
- destruct Hbrk as (_ & Hb & _). revert Hb.
match goal with |- context [reserved_top ?x] => let v := eval vm_compute in (reserved_top x) in change (reserved_top x) with v end.
pose proof YM05.alloc_ceiling_val. unfold brk_aslr_max. lia.
- reflexivity.
- exact Hlim.
- exact (eq_sym Hrclim).
- unfold vm_backing_used. rewrite Hvm, Hlz, Hmat. vm_compute. discriminate.
- exact Hh. - exact Hlz. - exact Hmat.
- unfold alloc_top. cbn [vm_init_sp]. exact Hceil. }
assert (HAUX : exists sec, 0 <= sec < 2 ^ 64 /\ auxv_pre src0_msyms sec (bv_unsigned (ew (E_main sp argv envp tid rnd) 0) + MAIN_SP) (ms_mem ms)).
{ pose proof HS as HS'. destruct HS' as (_ & _ & _ & _ & _ & _ & _ & HM & HG).
apply (auxv_pre_intro src0_msyms _ (ms_mem ms) _ (ss_facts ss_m1) 5 6 _ HM HG auxv_m1).
+ change (bv_unsigned (ew (E_main sp argv envp tid rnd) 0)) with (bv_unsigned sp). rewrite (ewm5 sp argv envp Hsp Hva Hve rnd tid).
unfold z_auxv, z_envp, MAIN_SP. lia.
+ change (bv_unsigned (ew (E_main sp argv envp tid rnd) 0)) with (bv_unsigned sp).
unfold E_main. rewrite (ew6 sp argv envp Hsp Hva Hve (xw_main sp argv envp tid rnd) (xd_main rnd)). unfold z_rand, MAIN_SP. lia. }
destruct HAUX as (sec & Hsec & HAUX).
destruct (aa_init API (ms_mem ms) _ sec HP Hsec) as [L [HL HsecL]].
pose proof HS as HS0. sym_reg HS0 (10%bv:reg) as Ha0. clear HS0.
eapply (malloc_site_cf src0_msyms API AX (MRC _) LIMLAW _ ss_m1 ms md L init_state CAP0 MAIN_SP src0_keep [] K_M1 L_m1 RS_m1 RA_m1 K
HS (anchored_main sp argv envp rnd Hsp Hva Hve Hceil (ss_facts ss_m1) tid ltac:(vm_compute; reflexivity)) site_m1 statics_m1 HL (proj1 init_ok) (proj2 init_ok)).
- intros _. rewrite HsecL. exact HAUX.
- rewrite Ha0. reflexivity.
- unfold CAP0. lia.
- intros kb sz [].
- exact Hj.
- exact gtree_first_malloc.
- exact roomcf_malloc1.
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' Hvm' Hpath Hblk Hhi Hbk Hres.
apply (HK res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' Hvm' Hpath).
+ intros a Ha Hsp' Ha'. apply Hhi; [exact Ha| exact Ha' |].
change (bv_unsigned (ew (E_main sp argv envp tid rnd) 0)) with (bv_unsigned sp). unfold ALLOC_STACK, MAIN_SP. lia.
+ destruct res; exact Hres.
Qed.
Theorem src0_m1_oom_cf : forall regs' g ms' md' fs,
st_ok src0segs (E_m1 sp tid argv envp rnd regs' g) ss_m1_post ms' ->
getr regs' 10%bv = Z_to_bv 64 0 -> ms_regs ms' = regs' ->
m_halted md' = None -> m_vm_lazy md' = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md' -> m_fs md' = fs ->
crealizes src0_msyms (mkCfg ms' md') (diag msg_oom fs).
Proof using.
intros regs' g ms' md' fs HS Ha0 Hregs Hh Hlz Hch <-.
apply (st_ok_regs src0segs _ _ ms' (sr_set (ss_regs ss_m1_post) 10%bv (SLit 0))) in HS.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. change (sr_get (ss_regs ss_m1_post) 10%bv) with (SOff A_BUF 0).
cbn [sv_denot]. rewrite Z.add_0_r. change A_BUF with (K_M1 + 4)%nat. unfold E_m1. rewrite post_env_a0, Ha0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
change (mkSS _ _ _ _ _) with ss_m1_null in HS.
unfold diag, wr, ex, msg_oom.
csrc0_diag_exit_tac HS Hch (G_M1 + 1)%nat.
Qed.
Theorem src0_dir_after_m1_cf : forall a0 path regs' g ms' md' L' A' q,
argv = [a0; path] -> read_error_hyp_cf -> Z.of_nat (length path) <= 60 ->
0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_m1 sp tid argv envp rnd regs' g) ss_m1_post ms' -> ms_regs ms' = regs' ->
runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp [a0; path] envp rnd) ->
aa_MR API L' A' (ms_mem ms') md' -> In (q, CAP0) (user_blocks A') ->
getr regs' 10%bv = Z_to_bv 64 (ptr_addr L' q) ->
forall inp, (exists vm', md' = with_vmmaps vm' (MD_dir tid brk mbase sp lim inp)) ->
crealizes src0_msyms (mkCfg ms' md') (diag (msg_read_error path) (m_fs md')).
Proof using AX Hsp Hva Hve Hfits Hceil.
intros a0 path regs' g ms' md' L' A' q Hargv HRE Hlen60 Htid HS Hregs HR HMR Hin Ha0 inp [vm' Hmd].
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms') md' q CAP0) as Hblk.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + CAP0 <= alloc_ceiling).
{ destruct (Hblk 0 HMR Hin ltac:(unfold CAP0; lia)) as (_ & H1 & H2 & _). lia. }
unfold CAP0 in Hq. assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
pose proof (mr_blocks_aligned _ _ (aa_laws API) L' A' (ms_mem ms') md' q CAP0 HMR Hin) as Hal.
apply (st_ok_facts src0segs _ _ _ (ss_facts ss_m1_ok)) in HS.
2:{ pose proof HS as HS'. destruct HS' as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
change (ss_facts ss_m1_ok) with (mkFacts ((A_BUF, blk_fact) :: f_atoms (ss_facts ss_m1_post)) (f_conds (ss_facts ss_m1_post)) (f_alias (ss_facts ss_m1_post))).
apply facts_ok_add_atom; [exact HG|]. unfold afact_ok, blk_fact; cbn [af_lo af_hi af_al2].
change A_BUF with (K_M1 + 4)%nat. unfold E_m1. rewrite post_env_a0, Ha0.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
change (2 ^ 4) with 16. pose proof YM05.alloc_ceiling_val. lia. }
change (mkSS _ _ _ _ _) with ss_m1_ok in HS.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall src0segs (E_m1 sp tid argv envp rnd regs' g) ss_rd1 msx) in HS end.
drv_runs (E_m1 sp tid argv envp rnd regs' g) ss_m1_ok HS HF HR.
apply (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L' A' _ _ md' (E_m1 sp tid argv envp rnd regs' g) (ss_facts ss_rd1) src0_keep (ss_mem ss_m1_ok) HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0)
(anchored_m1 sp tid argv envp rnd Hsp Hva Hve Hceil (ss_facts ss_rd1) regs' g ltac:(vm_compute; reflexivity))
ltac:(vm_compute; reflexivity)) in HF.
clear HMR. rename HF into HMR.
sym_ecall_open HS.
repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
cbn [ms_mem pend_at] in HMR.
destruct ss_rd1_facts as (Hpc & H17 & H10 & H11 & H12 & Hrv).
eapply (crz_read_dir src0_msyms regs _ mem (seg_rom src0segs) md' (Z_to_bv 64 3) _ Hh Hlz).
- rewrite (Hregs0 17%bv), H17. reflexivity.
- rewrite (Hregs0 10%bv), H10. reflexivity.
- reflexivity.
- rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
-
rewrite (Hregs0 11%bv), (Hregs0 12%bv), H11, H12. vm_compute. reflexivity.
-
cresume_sv src0segs (SLit (2 ^ 64 - 21)). { apply bv_eq. vm_compute. reflexivity. }
change (resume _ _ _ _) with ss_rderr in HS.
rewrite Hargv in Hva, Hfits. apply (HRE sp a0 path envp tid rnd (E_m1 sp tid argv envp rnd regs' g) _ md' Hsp Hva Hve Hfits Htid Hlen60); try assumption.
+ unfold E_m1. rewrite Hargv. apply post_env_agree.
+ split; [| reflexivity]. rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
Qed.
End M1.
End b.
