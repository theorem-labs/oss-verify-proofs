(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the first malloc stated over the run's input with the launch premises in place of entry_stack_fits and over the CONFIG_RSEQ-indexed state, a reserved ledger of the image's reservations followed by the vDSO pair, the auxv walk over the run's own key table of 27 or 29 pairs, the directory model taking the entry draw, and the run's channel-reader fact for the reader conjunct of fdchan). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Uaccess.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH05 YH07 YH06 YO3p YO3k YO3q YO3r YO3j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 YL06 YL0b YL0c YL08 YL0g YL0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 YK0a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section M1.
Variable API : AllocAPI src2_msyms.
Hypothesis AX : AllocExtra src2_msyms (aa_MR API).
Variables (sp brk mbase tid : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk src2segs brk.
Hypothesis Hlim : SRC_LIM_MIN <= lim.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
(* #38: [entry_stack_fits] no longer fixes the stack image; the launch
   premises YO3p's Section f takes stand in its place, and every layout fact
   is stated over the run [inp]. *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
(* 727298f3: [fdchan] also asks that the channel still has a reader, which
   the initial model takes from the run ([Run.valid_input_channel_reader]). *)
Hypothesis Hcr : in_channel_reader inp = true.
Hypothesis Hceil : YN05.ceil_of_top (bv_unsigned sp - stack_max_size).
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
Local Notation efn := (in_execfn inp) (only parsing).
Local Notation rs := (kb_rseq (in_kernel inp)) (only parsing).
Definition ANCH_MAIN : list (nat * Z) :=
[(7%nat, 8388608); (0%nat, 8388608); (1%nat, 8388608); (2%nat, 8388608); (4%nat, 8388608); (5%nat, 8388608); (6%nat, 8388608)].
Lemma ew_main5 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. intros t. pose proof (ewm5 inp mbase sp brk rnd) as W. lfeed W. exact (W t). Qed.
Lemma ew_main6 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 6) = z_rand (bv_unsigned sp) rs argv envp.
Proof. intros t. unfold E_main. eapply ew6; eassumption. Qed.
Lemma anchored_main : forall G t,
anchored_atoms G = ANCH_MAIN -> stack_anchored (E_main sp inp argv envp efn t rnd) G.
Proof.
intros G t HG. unfold stack_anchored. rewrite HG. unfold ANCH_MAIN.
pose proof (YN05.ceil_le_top _ Hceil) as Hle. rewrite stack_max_size_val in Hle.
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. unfold SP_LO, SP_HI in L.
pose proof (proj1 Hva) as HA.
pose proof (z_argv_bounds inp rnd 0 ltac:(lia)) as B0.
pose proof (progname_off_le (nth 0 argv [])) as HP.
pose proof (ewm7 inp mbase sp brk rnd) as E7. lfeed E7. specialize (E7 t).
assert (E0' : bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 0) = bv_unsigned sp) by reflexivity.
pose proof (ewm1 inp mbase sp brk rnd) as E1. lfeed E1. specialize (E1 t).
pose proof (ewm2 inp mbase sp brk rnd) as E2. lfeed E2. specialize (E2 t).
pose proof (ewm4 inp mbase sp brk rnd) as E4. lfeed E4. specialize (E4 t).
pose proof (ew_main5 t) as E5. pose proof (ew_main6 t) as E6.
repeat constructor; cbn [fst snd]; lia.
Qed.
Lemma anchored_m1 : forall G regs' g,
anchored_atoms G = ANCH_MAIN -> stack_anchored (E_m1 sp tid inp argv envp rnd regs' g) G.
Proof.
intros G regs' g HG.
apply (stack_anchored_ext (E_main sp inp argv envp efn tid rnd) _ G G (anchored_main G tid HG) eq_refl).
rewrite HG. unfold ANCH_MAIN. intros a Ha. unfold E_m1.
pose proof (proj1 (post_env_agree (E_main sp inp argv envp efn tid rnd) K_M1 regs' g)) as AG.
cbn in Ha. destruct Ha as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst]; apply AG; unfold K_M1; lia.
Qed.
Theorem src2_malloc1 : forall ms md (rx : list (word * word)) (K : option sptr * astate -> TSet),
(* 08b1429: the reserved ledger is the image's reservations followed by the vDSO pair (State.init_reserved) *)
m_vmmaps md = mkVmMapsFull (segments_reserved src2segs ++ rx) [] [] brk brk lim mbase sp ->
Forall (fun e => bv_unsigned brk + 3 * 4096 <= bv_unsigned (fst e) /\ 0 < bv_unsigned (snd e) <= 0x14000) rx ->
(length rx <= 2)%nat ->
incl (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md))) (vm_reserved (m_vmmaps md)) ->
m_halted md = None -> m_vm_lazy md = [] -> m_vm_materialized md = [] ->
st_ok src2segs (E_main sp inp argv envp efn tid rnd) (ss_m1 rs) ms ->
jinv K (malloc CAP0 init_state) ->
(forall res A' L' ms' md' g tr,
st_ok src2segs (E_m1 sp tid inp argv envp rnd (ms_regs ms') g) ss_m1_post ms' ->
stack_anchored (E_m1 sp tid inp argv envp rnd (ms_regs ms') g) (ss_facts ss_m1_post) ->
aa_MR API L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
cpath (malloc CAP0 init_state) tr (res, A') ->
(forall a, alloc_ceiling <= a -> bv_unsigned sp <= a -> a < 2 ^ 64 -> mbyte src2segs (ms_mem ms') a = mbyte src2segs (ms_mem ms) a) ->
match res with
| None => getr (ms_regs ms') 10%bv = Z_to_bv 64 0 /\ user_blocks A' = user_blocks init_state
| Some q => getr (ms_regs ms') 10%bv = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
exists b1 b2, user_blocks A' = b1 ++ (q, CAP0) :: b2 /\ user_blocks init_state = b1 ++ b2
end ->
realizes src2segs (mkCfg ms' md') (K (res, A'))) ->
realizes src2segs (mkCfg ms md) (tset (malloc CAP0 init_state) K).
Proof.
intros ms md rx K Hvm Hrx Hrxl Hvin Hh Hlz Hmat HS Hj HK.
assert (HP : heap_pristine src2_msyms (ms_mem ms) md).
{ eapply (heap_pristine_intro src2_msyms _ (ms_mem ms) _ _ (st_ok_mem_ok src2segs _ _ _ HS) (pristine_m1 rs));
rewrite ?Hvm; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_limit].
- reflexivity. - reflexivity. - reflexivity.
- exact Hbrk.
- destruct Hbrk as (_ & Hb & _). revert Hb.
match goal with |- context [reserved_top ?x] => let v := eval vm_compute in (reserved_top x) in change (reserved_top x) with v end.
pose proof YN05.alloc_ceiling_val. unfold brk_aslr_max. lia.
- exists rx. split; [reflexivity|]. split; [exact Hrx | exact Hrxl].
- exact Hlim.
- unfold vm_backing_used. rewrite Hvm, Hlz, Hmat. vm_compute. discriminate.
- exact Hh. - exact Hlz. - exact Hmat.
- unfold alloc_top. cbn [vm_init_sp]. exact Hceil.
- rewrite Hvm in Hvin. exact Hvin. }
assert (HAUX : exists sec, 0 <= sec < 2 ^ 64 /\ auxv_pre src2_msyms sec (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0) + MAIN_SP) (ms_mem ms)).
{ pose proof HS as HS'. destruct HS' as (_ & _ & _ & _ & _ & _ & _ & HM & HG).
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L.
(* the walk reads the run's own key table, 27 or 29 pairs *)
apply (auxv_pre_intro src2_msyms _ (ms_mem ms) _ (ss_facts (ss_m1 rs)) 5 6 _ (APC.rseq_z rs)
ltac:(destruct (kb_rseq (in_kernel inp)); cbn; lia) HM HG (auxv_m1 rs)).
+ change (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0)) with (bv_unsigned sp). rewrite (ew_main5 tid).
unfold MAIN_SP. lia.
+ change (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0)) with (bv_unsigned sp).
rewrite (ew_main6 tid). unfold MAIN_SP. lia. }
destruct HAUX as (sec & Hsec & HAUX).
destruct (aa_init API (ms_mem ms) _ sec HP Hsec) as [L [HL HsecL]].
eapply (malloc_site src2_msyms API AX _ (ss_m1 rs) ms md L init_state CAP0 MAIN_SP src2_keep [] K_M1 L_m1 RS_m1 RA_m1 K
HS (anchored_main (ss_facts (ss_m1 rs)) tid ltac:(destruct (kb_rseq (in_kernel inp)); vm_compute; reflexivity))
(site_m1 rs) statics_m1 HL (proj1 init_ok) (proj2 init_ok)).
- intros _. rewrite HsecL. exact HAUX.
- rewrite (st_ok_reg src2segs _ (ss_m1 rs) ms 10 HS). destruct (kb_rseq (in_kernel inp)); reflexivity.
- unfold CAP0. lia.
- intros kb sz [].
- exact Hj.
- exact gtree_first_malloc.
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' Hvm' Hpath Hblk Hhi Hbk Hres.
(* after the call the two flags' runs are the same state (YL0g.post_m1) *)
rewrite post_m1 in HS'.
replace (ss_facts (ss_m1 rs)) with (ss_facts ss_m1_post) in HSA'
by (destruct (kb_rseq (in_kernel inp)); vm_compute; reflexivity).
apply (HK res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' Hvm' Hpath).
+ intros a Ha Hsp' Ha'. apply Hhi; [exact Ha| exact Ha' |].
change (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0)) with (bv_unsigned sp). unfold ALLOC_STACK, MAIN_SP. lia.
+ destruct res; exact Hres.
Qed.
Theorem src2_m1_oom : forall regs' g ms' md' fs,
st_ok src2segs (E_m1 sp tid inp argv envp rnd regs' g) ss_m1_post ms' ->
getr regs' 10%bv = Z_to_bv 64 0 -> ms_regs ms' = regs' ->
m_halted md' = None -> m_vm_lazy md' = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md' -> m_fs md' = fs ->
realizes src2segs (mkCfg ms' md') (diag msg_oom fs).
Proof.
intros regs' g ms' md' fs HS Ha0 Hregs Hh Hlz Hch <-.
apply (st_ok_regs src2segs _ _ ms' (sr_set (ss_regs ss_m1_post) 10%bv (SLit 0))) in HS.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. change (sr_get (ss_regs ss_m1_post) 10%bv) with (SOff A_BUF 0).
cbn [sv_denot]. rewrite Z.add_0_r. change A_BUF with (K_M1 + 4)%nat. unfold E_m1. rewrite post_env_a0, Ha0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
change (mkSS _ _ _ _ _) with ss_m1_null in HS.
unfold diag, wr, ex, msg_oom.
src2_diag_exit_tac HS Hch (G_M1 + 1)%nat.
Qed.
Theorem src2_dir_after_m1 : forall a0 path regs' g ms' md' L' A' q,
in_argv inp = [a0; path] -> read_error_hyp -> Z.of_nat (length path) <= 60 ->
0 < bv_unsigned tid < 4194304 ->
st_ok src2segs (E_m1 sp tid inp argv envp rnd regs' g) ss_m1_post ms' -> ms_regs ms' = regs' ->
runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
aa_MR API L' A' (ms_mem ms') md' -> In (q, CAP0) (user_blocks A') ->
getr regs' 10%bv = Z_to_bv 64 (ptr_addr L' q) ->
(exists vm', md' = with_vmmaps vm' (MD_dir tid brk mbase sp lim inp rnd)) ->
realizes src2segs (mkCfg ms' md') (diag (msg_read_error path) (m_fs md')).
Proof.
intros a0 path regs' g ms' md' L' A' q Hargv HRE Hlen60 Htid HS Hregs HR HMR Hin Ha0 [vm' Hmd].
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms') md' q CAP0) as Hblk.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + CAP0 <= alloc_ceiling).
{ destruct (Hblk 0 HMR Hin ltac:(unfold CAP0; lia)) as (_ & H1 & H2 & _). lia. }
unfold CAP0 in Hq. assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YN05.alloc_ceiling_val; lia).
pose proof (mr_blocks_aligned _ _ (aa_laws API) L' A' (ms_mem ms') md' q CAP0 HMR Hin) as Hal.
apply (st_ok_facts src2segs _ _ _ (ss_facts ss_m1_ok)) in HS.
2:{ pose proof HS as HS'. destruct HS' as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
change (ss_facts ss_m1_ok) with (mkFacts ((A_BUF, blk_fact) :: f_atoms (ss_facts ss_m1_post)) (f_conds (ss_facts ss_m1_post)) (f_alias (ss_facts ss_m1_post))).
apply facts_ok_add_atom; [exact HG|]. unfold afact_ok, blk_fact; cbn [af_lo af_hi af_al2].
change A_BUF with (K_M1 + 4)%nat. unfold E_m1. rewrite post_env_a0, Ha0.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
change (2 ^ 4) with 16. pose proof YN05.alloc_ceiling_val. lia. }
change (mkSS _ _ _ _ _) with ss_m1_ok in HS.
drv_run_with src2tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall src2segs (E_m1 sp tid inp argv envp rnd regs' g) ss_rd1 msx) in HS end.
drv_runs (E_m1 sp tid inp argv envp rnd regs' g) ss_m1_ok HS HF HR.
apply (MR_after_frame src2_msyms (aa_MR API) (aa_laws API) AX L' A' _ _ md' (E_m1 sp tid inp argv envp rnd regs' g) (ss_facts ss_rd1) src2_keep (ss_mem ss_m1_ok) HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0)
(anchored_m1 (ss_facts ss_rd1) regs' g ltac:(vm_compute; reflexivity))
ltac:(vm_compute; reflexivity)) in HF.
clear HMR. rename HF into HMR.
sym_ecall_open HS.
repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
cbn [ms_mem pend_at] in HMR.
destruct ss_rd1_facts as (Hpc & H17 & H10 & H11 & H12 & Hrv).
eapply (rz_read_dir src2segs regs _ mem (seg_rom src2segs) md' (Z_to_bv 64 3) _ Hh Hlz).
- rewrite (Hregs0 17%bv), H17. reflexivity.
- rewrite (Hregs0 10%bv), H10. reflexivity.
- reflexivity.
- rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
-
rewrite (Hregs0 11%bv), (Hregs0 12%bv), H11, H12. vm_compute. reflexivity.
-
resume_sv src2segs (SLit (2 ^ 64 - 21)). { apply bv_eq. vm_compute. reflexivity. }
change (resume _ _ _ _) with ss_rderr in HS.
apply (HRE sp brk mbase inp a0 path tid rnd (E_m1 sp tid inp argv envp rnd regs' g) _ md' Hsp Hargv Hva Hve Hvl Hlau Htid Hlen60); try assumption.
+ unfold E_m1. rewrite Hargv. apply post_env_agree.
+ split; [| split; [reflexivity | rewrite Hmd; exact Hcr]]. rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
Qed.
End M1.
End b.
