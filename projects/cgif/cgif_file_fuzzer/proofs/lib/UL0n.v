(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the vDSO's mappings and steps; the launch's channel-reader and SIGPIPE fields): changed AX, Hva, Hve, anchored_main, anchored_m1, ubs0_malloc1, ubs0_m1_oom, ubs0_dir_after_m1; added word_mem_le8, Hvl, Hlau, Hvi, argv, envp, efn; removed Hfits. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Uaccess.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH01 UH03 UH02 UN3e UN35 UN3f UN3g UN34.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0a UL0k UL0p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* A run of the eight little-endian bytes of [v] is the word [v] in [word_mem]'s terms. *)
Lemma word_mem_le8 : forall m a v, 0 <= v < 2 ^ 64 ->
YP08.bytes_at m a (word_le8 (Z_to_bv 64 v)) -> word_mem ubs0segs m a v.
Proof.
intros m a v Hv Hb k Hk.
rewrite (bytes_at_mbyte ubs0segs m a _ k Hb) by (rewrite length_n_to_le_8; lia).
rewrite word_le8_nth by lia. f_equal. unfold byte_of_word, le_byte.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Section M1.
Variable API : AllocAPI ubs0_msyms.
Hypothesis AX : AllocExtra ubs0_msyms (aa_MR API).
Variables (sp brk mbase tid : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ubs0segs brk.
Hypothesis Hlim : SRC_LIM_MIN <= lim.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
(* [entry_stack_fits] no longer determines the stack image: REPLACED by the three premises
   UN3e's Section f takes (UN3e.v:189-194).  [argv] and [envp] are no longer free either --
   every layout fact is stated over [inp] now (YP08.v:494-496). *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Definition ANCH_MAIN : list (nat * Z) :=
[(7%nat, 8388608); (0%nat, 8388608); (1%nat, 8388608); (2%nat, 8388608); (4%nat, 8388608); (5%nat, 8388608); (6%nat, 8388608)].
Lemma anchored_main : forall G t,
anchored_atoms G = ANCH_MAIN -> stack_anchored (E_main sp inp argv envp efn t rnd) G.
Proof using Hceil Hlau Hsp Hva Hve Hvi Hvl.
intros G t HG. unfold stack_anchored. rewrite HG. unfold ANCH_MAIN.
pose proof (YM05.ceil_le_top _ Hceil) as Hle. rewrite stack_max_size_val in Hle.
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi) as L. unfold SP_LO, SP_HI in L.
(* [AUXV_BYTES] takes the run's rseq flag now (YP08.v:67), so it is an opaque application
   and [lia] needs its range; the gap term was always opaque the same way. *)
pose proof (YP08.auxv_bytes_range (kb_rseq (in_kernel inp))) as HAB.
pose proof (YP08.yp_gap_range argv envp) as HGP.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi 0 ltac:(lia)) as B0.
pose proof (progname_off_le (nth 0 argv [])) as HP.
pose proof (ewm7 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi t) as E7.
assert (E0' : bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 0) = bv_unsigned sp)
by reflexivity.
pose proof (ewm1 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi t) as E1.
pose proof (ewm2 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi t) as E2.
pose proof (ewm4 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi t) as E4.
pose proof (ewm5 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi t) as E5.
pose proof (ewm6 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi t) as E6.
repeat constructor; cbn [fst snd]; lia.
Qed.
Lemma anchored_m1 : forall G regs' g,
anchored_atoms G = ANCH_MAIN -> stack_anchored (E_m1 sp tid inp argv envp rnd regs' g) G.
Proof using Hceil Hlau Hsp Hva Hve Hvi Hvl.
intros G regs' g HG.
apply (stack_anchored_ext (E_main sp inp argv envp efn tid rnd) _ G G (anchored_main G tid HG) eq_refl).
rewrite HG. unfold ANCH_MAIN. intros a Ha. unfold E_m1.
pose proof (proj1 (post_env_agree (E_main sp inp argv envp efn tid rnd) K_M1 regs' g)) as AG.
cbn in Ha. destruct Ha as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst]; apply AG; unfold K_M1; lia.
Qed.
Theorem ubs0_malloc1 : forall ms md (rx : list (word * word)) (K : option sptr * astate -> TSet),
(* the reserved ledger is the image's reservations followed by the vDSO pair
   ([State.init_reserved]); [rx] is that pair, placed clear of the heap ([YO0d.rx_ok]) *)
m_vmmaps md = mkVmMapsFull (segments_reserved ubs0segs ++ rx) [] [] brk brk lim mbase sp ->
rx_ok (bv_unsigned brk) rx ->
incl (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md))) (vm_reserved (m_vmmaps md)) ->
m_halted md = None -> m_vm_lazy md = [] -> m_vm_materialized md = [] ->
st_ok ubs0segs (E_main sp inp argv envp efn tid rnd) ss_m1 ms ->
(* the keys of auxv pairs 26.. at the run's own CONFIG_RSEQ flag, which [ss_m1] (shared by
   both flags) does not hold: musl's [get_random_secret] reads every key up to AT_NULL *)
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) argv envp efn) ->
jinv K (malloc CAP0 init_state) ->
(forall res A' L' ms' md' g tr,
st_ok ubs0segs (E_m1 sp tid inp argv envp rnd (ms_regs ms') g) ss_m1_post ms' ->
stack_anchored (E_m1 sp tid inp argv envp rnd (ms_regs ms') g) (ss_facts ss_m1_post) ->
aa_MR API L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
(exists vm', md' = with_vmmaps vm' md) ->
cpath (malloc CAP0 init_state) tr (res, A') ->
(forall a, alloc_ceiling <= a -> bv_unsigned sp <= a -> a < 2 ^ 64 -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs (ms_mem ms) a) ->
match res with
| None => getr (ms_regs ms') 10%bv = Z_to_bv 64 0 /\ user_blocks A' = user_blocks init_state
| Some q => getr (ms_regs ms') 10%bv = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
exists b1 b2, user_blocks A' = b1 ++ (q, CAP0) :: b2 /\ user_blocks init_state = b1 ++ b2
end ->
realizes ubs0segs (mkCfg ms' md') (K (res, A'))) ->
realizes ubs0segs (mkCfg ms md) (tset (malloc CAP0 init_state) K).
Proof using AX Hbrk Hceil Hlau Hlim Hsp Hva Hve Hvi Hvl.
intros ms md rx K Hvm Hrx Hvin Hh Hlz Hmat HS HRt Hj HK.
assert (HP : heap_pristine ubs0_msyms (ms_mem ms) md).
{ eapply (heap_pristine_intro ubs0_msyms _ (ms_mem ms) _ _ (st_ok_mem_ok ubs0segs _ _ _ HS) pristine_m1);
rewrite ?Hvm; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_limit].
- reflexivity. - reflexivity. - reflexivity.
- exact Hbrk.
- destruct Hbrk as (_ & Hb & _). revert Hb.
match goal with |- context [reserved_top ?x] => let v := eval vm_compute in (reserved_top x) in change (reserved_top x) with v end.
pose proof YM05.alloc_ceiling_val. unfold brk_aslr_max. lia.
- exists rx. split; [reflexivity | exact Hrx].
- exact Hlim.
- unfold vm_backing_used. rewrite Hvm, Hlz, Hmat. vm_compute. discriminate.
- exact Hh. - exact Hlz. - exact Hmat.
- unfold alloc_top. cbn [vm_init_sp]. exact Hceil.
- rewrite Hvm in Hvin. exact Hvin. }
assert (HAUX : exists sec, 0 <= sec < 2 ^ 64 /\ auxv_pre ubs0_msyms sec (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0) + MAIN_SP) (ms_mem ms)).
{ pose proof HS as HS'. destruct HS' as (_ & _ & _ & _ & _ & _ & _ & HM & HG).
apply (auxv_pre_intro_head ubs0_msyms (kb_rseq (in_kernel inp)) _ (ms_mem ms) _ (ss_facts ss_m1) 5 6 _ HM HG auxv_m1).
+ intros k Hk. rewrite (ewm5 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi tid).
unfold runs_at, runs_main in HRt. cbn [app] in HRt. do 4 apply Forall_inv_tail in HRt. rewrite Forall_forall in HRt.
revert Hk HRt. destruct (kb_rseq (in_kernel inp)); intros Hk HRt; cbn [AUXV_N auxv_tail_runs In] in Hk, HRt.
* assert (Hk3 : k = 26%nat \/ k = 27%nat \/ k = 28%nat) by lia.
destruct Hk3 as [-> | [-> | ->]].
-- change (nth 26 AUXV_OFFS 0) with 416. change (nth 26 (AUXV_TYPES_r true) 0) with 27.
apply word_mem_le8; [lia|]. exact (proj2 (proj2 (HRt _ (or_introl eq_refl)))).
-- change (nth 27 AUXV_OFFS 0) with 432. change (nth 27 (AUXV_TYPES_r true) 0) with 28.
apply word_mem_le8; [lia|]. exact (proj2 (proj2 (HRt _ (or_intror (or_introl eq_refl))))).
-- change (nth 28 AUXV_OFFS 0) with 448. change (nth 28 (AUXV_TYPES_r true) 0) with 0.
apply word_mem_le8; [lia|]. exact (proj2 (proj2 (HRt _ (or_intror (or_intror (or_introl eq_refl)))))).
* replace k with 26%nat by lia.
change (nth 26 AUXV_OFFS 0) with 416. change (nth 26 (AUXV_TYPES_r false) 0) with 0.
apply word_mem_le8; [lia|]. exact (proj2 (proj2 (HRt _ (or_introl eq_refl)))).
+ change (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0)) with (bv_unsigned sp).
rewrite (ewm5 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi tid).
unfold z_auxv, z_envp, MAIN_SP. lia.
+ change (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0)) with (bv_unsigned sp).
rewrite (ewm6 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi tid). unfold z_rand, MAIN_SP. lia. }
destruct HAUX as (sec & Hsec & HAUX).
destruct (aa_init API (ms_mem ms) _ sec HP Hsec) as [L [HL HsecL]].
pose proof HS as HS0. sym_reg HS0 (10%bv:reg) as Ha0. clear HS0.
eapply (malloc_site ubs0_msyms API AX _ ss_m1 ms md L init_state CAP0 MAIN_SP ubs0_keep [] K_M1 L_m1 RS_m1 RA_m1 K
HS (anchored_main (ss_facts ss_m1) tid ltac:(vm_compute; reflexivity)) site_m1 statics_m1 HL (proj1 init_ok) (proj2 init_ok)).
- intros _. rewrite HsecL. exact HAUX.
- rewrite Ha0. reflexivity.
- unfold CAP0. lia.
- intros kb sz [].
- exact Hj.
- exact gtree_first_malloc.
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' Hvm' Hpath Hblk Hhi Hbk Hres.
apply (HK res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' Hvm' Hpath).
+ intros a Ha Hsp' Ha'. apply Hhi; [exact Ha| exact Ha' |].
change (bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0)) with (bv_unsigned sp). unfold ALLOC_STACK, MAIN_SP. lia.
+ destruct res; exact Hres.
Qed.
Theorem ubs0_m1_oom : forall regs' g ms' md' fs,
st_ok ubs0segs (E_m1 sp tid inp argv envp rnd regs' g) ss_m1_post ms' ->
getr regs' 10%bv = Z_to_bv 64 0 -> ms_regs ms' = regs' ->
m_halted md' = None -> m_vm_lazy md' = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md' -> m_fs md' = fs ->
realizes ubs0segs (mkCfg ms' md') (diag msg_oom fs).
Proof using.
intros regs' g ms' md' fs HS Ha0 Hregs Hh Hlz Hch <-.
apply (st_ok_regs ubs0segs _ _ ms' (sr_set (ss_regs ss_m1_post) 10%bv (SLit 0))) in HS.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. change (sr_get (ss_regs ss_m1_post) 10%bv) with (SOff A_BUF 0).
cbn [sv_denot]. rewrite Z.add_0_r. change A_BUF with (K_M1 + 4)%nat. unfold E_m1. rewrite post_env_a0, Ha0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
change (mkSS _ _ _ _ _) with ss_m1_null in HS.
unfold diag, wr, ex, msg_oom.
ubs0_diag_exit_tac HS Hch (G_M1 + 1)%nat.
Qed.
Theorem ubs0_dir_after_m1 : forall a0 path regs' g ms' md' L' A' q,
in_argv inp = [a0; path] -> read_error_hyp -> Z.of_nat (length path) <= 60 ->
0 < bv_unsigned tid < 4194304 ->
st_ok ubs0segs (E_m1 sp tid inp argv envp rnd regs' g) ss_m1_post ms' -> ms_regs ms' = regs' ->
runs_at (bv_unsigned sp) (ms_mem ms') (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) argv envp efn) ->
aa_MR API L' A' (ms_mem ms') md' -> In (q, CAP0) (user_blocks A') ->
getr regs' 10%bv = Z_to_bv 64 (ptr_addr L' q) ->
(exists vm', md' = with_vmmaps vm' (MD_dir tid brk mbase sp lim inp rnd)) ->
realizes ubs0segs (mkCfg ms' md') (diag (msg_read_error path) (m_fs md')).
Proof using AX Hceil Hlau Hsp Hva Hve Hvi Hvl.
intros a0 path regs' g ms' md' L' A' q Hargv HRE Hlen60 Htid HS Hregs HR HMR Hin Ha0 [vm' Hmd].
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms') md' q CAP0) as Hblk.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + CAP0 <= alloc_ceiling).
{ destruct (Hblk 0 HMR Hin ltac:(unfold CAP0; lia)) as (_ & H1 & H2 & _). lia. }
unfold CAP0 in Hq. assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
pose proof (mr_blocks_aligned _ _ (aa_laws API) L' A' (ms_mem ms') md' q CAP0 HMR Hin) as Hal.
apply (st_ok_facts ubs0segs _ _ _ (ss_facts ss_m1_ok)) in HS.
2:{ pose proof HS as HS'. destruct HS' as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
change (ss_facts ss_m1_ok) with (mkFacts ((A_BUF, blk_fact) :: f_atoms (ss_facts ss_m1_post)) (f_conds (ss_facts ss_m1_post)) (f_alias (ss_facts ss_m1_post))).
apply facts_ok_add_atom; [exact HG|]. unfold afact_ok, blk_fact; cbn [af_lo af_hi af_al2].
change A_BUF with (K_M1 + 4)%nat. unfold E_m1. rewrite post_env_a0, Ha0.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
change (2 ^ 4) with 16. pose proof YM05.alloc_ceiling_val. lia. }
change (mkSS _ _ _ _ _) with ss_m1_ok in HS.
drv_run_with ubs0tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall ubs0segs (E_m1 sp tid inp argv envp rnd regs' g) ss_rd1 msx) in HS end.
drv_runs (E_m1 sp tid inp argv envp rnd regs' g) ss_m1_ok HS HF HR.
apply (MR_after_frame ubs0_msyms (aa_MR API) (aa_laws API) AX L' A' _ _ md' (E_m1 sp tid inp argv envp rnd regs' g) (ss_facts ss_rd1) ubs0_keep (ss_mem ss_m1_ok) HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0)
(anchored_m1 (ss_facts ss_rd1) regs' g ltac:(vm_compute; reflexivity))
ltac:(vm_compute; reflexivity)) in HF.
clear HMR. rename HF into HMR.
sym_ecall_open HS.
repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
cbn [ms_mem pend_at] in HMR.
destruct ss_rd1_facts as (Hpc & H17 & H10 & H11 & H12 & Hrv).
eapply (rz_read_dir ubs0segs regs _ mem (seg_rom ubs0segs) md' (Z_to_bv 64 3) _ Hh Hlz).
- rewrite (Hregs0 17%bv), H17. reflexivity.
- rewrite (Hregs0 10%bv), H10. reflexivity.
- reflexivity.
- rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
-
rewrite (Hregs0 11%bv), (Hregs0 12%bv), H11, H12. vm_compute. reflexivity.
-
resume_sv ubs0segs (SLit (2 ^ 64 - 21)). { apply bv_eq. vm_compute. reflexivity. }
change (resume _ _ _ _) with ss_rderr in HS.
apply (HRE sp brk mbase inp a0 path tid rnd (E_m1 sp tid inp argv envp rnd regs' g) _ md' Hsp Hargv Hva Hve Hvl Hlau Hvi Htid Hlen60); try assumption.
+ unfold E_m1. rewrite Hargv. apply post_env_agree.
+ rewrite <- Hargv. exact HR.
+ split; [| split; [reflexivity | rewrite Hmd; exact (reader_of_inp inp Hvi)]]. rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
Qed.
End M1.
End b.
