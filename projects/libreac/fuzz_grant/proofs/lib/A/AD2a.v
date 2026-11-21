(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2a.v, with its module paths changed, names TfibSyms -> GrantSyms. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed EL, HWXi, EL3, EL2, cstr_len_le, open_prefix and 10 more; added efn, ztop, Hva2, ztop_le, argv1_task_size); the channel reader that fdchan asks for at LPS 727298f3 carried beside the descriptor fact, from cs_ok's co_rdr. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_grant.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK00 YK14 YK15 YK18 YK0p YP0n YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB1v AB12 AB1h AB13 AF0m AD2j AD2i AD1t AD1v AD1y.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : asyms.
Hypothesis HB : GrantSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis HCO : cannot_open_tfa B.
Hypothesis HFILE : file_arm_tfa B.
Hypothesis HDIR : dir_arm_tfa B.
Variables (sp brk mbase : word) (inp : ProcInput) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
(* The entry stack is TOP-anchored at 75d69e00: [YP08.z_strs] counts DOWN from
   [bv_unsigned (ed_top rnd)], not up from [bv_unsigned sp] (YP08.v:200-203 against
   YP08.v:494-505, where [zsp] and [ztop] are two different abbreviations and
   [layout_facts]'s fourth and seventh conjuncts separate them, YP08.v:756-761).  So this
   section carries the entry draw, and with it the launch premises YP08's own section header
   now takes (YP08.v:477-493).  Premise order and names copied from the ported donor
   YL0q Section b / YL0p.v:39-45: [Hsp Hargv Hva Hve Hvl Hlau Hvi], with
   [entry_stack_fits] DROPPED -- [entry_launch_ok_va] implies it
   ([entry_launch_ok_va_fits], 75d69e00 Run.v:3718-3722) and nothing here consumed it as a
   fact ([argv1_task_size] below now derives its bound from [YP08.z_argv_fits] instead). *)
Hypothesis Hsp : valid_sp sp.
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
#[local] Notation EL := (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp))
[a0; p] (in_envp inp) (in_execfn inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation ztop := (bv_unsigned (ed_top rnd)).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
(* The entry-layout lemmas speak of [in_argv inp]; [Hargv] converts to the two-element
   spelling. The top bound pins the complete section prefix, including its image fields. *)
Let Hva2 : valid_argv [a0; p].
Proof. rewrite <- Hargv. exact Hva. Qed.
Lemma EL0 : bv_unsigned (ew EL 0) = usp. Proof. reflexivity. Qed.
Lemma EL3 : ew EL 3 = Z_to_bv 64 2. Proof. reflexivity. Qed.
Lemma EL2 : bv_unsigned (ew EL 2) = z_argv ztop [a0; p] envp efn 1.
Proof.
assert (H2 : bv_unsigned (ew (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp))
(in_argv inp) (in_envp inp) (in_execfn inp) xw xd) 2)
= z_argv ztop (in_argv inp) envp efn 1)
by (exact (YP08.ew2' TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd
  Hsp Hva Hve Hvl Hlau 1 ltac:(lia) xw xd ltac:(rewrite Hargv; cbn; lia))).
rewrite Hargv in H2. exact H2.
Qed.
Lemma usp_lo : sp_window_lo <= usp. Proof. exact (proj1 Hsp). Qed.
Lemma ztop_le : ztop <= kHighMemEnd.
Proof.
assert (H : ztop <= SP_HI) by exact (YP08.top_le TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
unfold SP_HI, kHighMemEnd in *. lia.
Qed.
(* Bound argv[1]'s terminating byte with the run's top-anchored layout. *)
Lemma argv1_task_size : z_argv ztop [a0; p] envp efn 1 + Z.of_nat (length p) < TASK_SIZE.
Proof.
assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
assert (Hal : (2 <= length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
assert (Z1 : z_argv ztop (in_argv inp) envp efn 1
+ Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 <= SP_HI - 9)
by (exact (YP08.z_argv_fits TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd
  Hsp Hva Hve Hvl Hlau 1 ltac:(lia))).
rewrite Hargv in Z1. cbn [nth] in Z1. unfold SP_HI in Z1. lia.
Qed.
Definition at_open (W : world tfibsegs) (ms : machine_state) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok_ecall tfibsegs EL ss_open (restrict (w_H W) ms')
/\ frame_of EL (smem_main true) (ms_mem ms) (ms_mem ms')
/\ frame_of EL (smem_main true) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')).
Lemma open_run : forall (W : world tfibsegs) ms md,
st_ok tfibsegs EL (ss_main true) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_open W ms md).
Proof.
intros W ms md HS. pose proof HWXi as HWX.
srr_run_with tfibtbl_drv_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibtbl_drv_ok HS.
{
exfalso. cbn [Sem.branch_taken sv_denot] in Hc. rewrite EL3 in Hc. cbn in Hc. discriminate Hc. }
srr_run_with tfibtbl_drv_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split.
- eapply frame_of_trans; [| exact HF1 | exact HF]. vm_compute. reflexivity.
- eapply frame_of_trans; [| exact HFr1 | exact HFr]. vm_compute. reflexivity.
Qed.
Lemma openat_errnos_small : forall e, In e openat_errnos -> 0 < e < 4096.
Proof.
intros e H. unfold openat_errnos in H. cbn in H. unfold ENOMEM, EACCES, EMFILE, ENFILE in H.
destruct H as [<-|[<-|[<-|[<-|[]]]]]; lia.
Qed.
Lemma mrestrict_some : forall (H : word -> bool) (m : word -> option byte) a b, mrestrict H m a = Some b -> m a = Some b /\ H a = false.
Proof. intros H m a b X. unfold mrestrict in X. destruct (H a); [discriminate X | split; [exact X | reflexivity]]. Qed.
Lemma bytes_at_unrestrict : forall (H : word -> bool) m a bs, YP03.bytes_at (mrestrict H m) a bs -> YP03.bytes_at m a bs.
Proof.
intros H m a bs X j Hj. pose proof (X j Hj) as Y. destruct (nth_error bs j) as [b|] eqn:En.
- exact (proj1 (mrestrict_some H m _ _ Y)).
- exfalso. apply nth_error_None in En. lia.
Qed.
Lemma cstr_len_le : forall mp fuel (a : word) n,
mp (woff a n) = Some (Z_to_bv 8 0) -> (cstr_access_len_aux mp a fuel <= S n)%nat.
Proof.
intros mp fuel. induction fuel as [|fuel IH]; intros a n Hn; cbn [cstr_access_len_aux]; [lia|].
(* [State.cstr_access_len_aux] gained [strncpy_from_user]'s clamp at this revision
   (75d69e00:theories/LinuxProcessSem/State.v:1493): the fuel-successor case now tests
   [negb (access_okb a 1)] BEFORE it looks at [mp a], and returns 0 there, so the walk
   stops without counting.  That arm bounds the count by 0, which is below [S n].  The
   None arm below returns 1 now rather than 0, and [lia] closes it either way. *)
destruct (negb (access_okb a 1)); [lia|].
destruct (mp a) as [b|] eqn:Ha; [|lia].
destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Hb; [lia|].
destruct n as [|n].
- exfalso. rewrite woff_0, Ha in Hn. injection Hn as ->. rewrite bv_eqb_refl in Hb. discriminate Hb.
- rewrite <- woff_succ in Hn. specialize (IH _ _ Hn). lia.
Qed.
Lemma open_copyins_avoid : forall (H : word -> bool) regs pc mem z,
getr regs 11%bv = Z_to_bv 64 z -> 0 <= z -> z + Z.of_nat (length p) + 1 <= 2 ^ 64 ->
YP03.bytes_at (mrestrict H mem) z (p ++ [NUL]) ->
ranges_avoid H (open_copyins (pend_at regs pc mem (seg_rom tfibsegs))).
Proof.
intros H regs pc mem z H11 Hz0 Hz1 HBy a n Hin. unfold open_copyins in Hin. rewrite pend_gpr1, pend_read_byte_mrb, H11 in Hin.
assert (HU : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite u64_lit by lia; reflexivity).
assert (HBk : forall k, (k <= length p)%nat ->
mem (woff (Z_to_bv 64 z) k) = nth_error (p ++ [NUL]) k /\ H (woff (Z_to_bv 64 z) k) = false).
{ intros k Hk. pose proof (HBy k ltac:(rewrite length_app; cbn; lia)) as X. unfold woff. rewrite HU.
destruct (nth_error (p ++ [NUL]) k) as [b|] eqn:En; [exact (mrestrict_some H mem _ _ X)|].
exfalso. apply nth_error_None in En. rewrite length_app in En. cbn in En. lia. }
assert (Hlen : (cstr_access_len_aux (mrb tfibsegs mem) (Z_to_bv 64 z) path_max <= S (length p))%nat).
{ apply cstr_len_le. unfold mrb. rewrite (proj1 (HBk (length p) ltac:(lia))).
rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
revert Hin Hlen. generalize (cstr_access_len_aux (mrb tfibsegs mem) (Z_to_bv 64 z) path_max). intros L Hin Hlen.
destruct Hin as [Heq|[]]. injection Heq as <- <-.
intros k Hk. exact (proj2 (HBk k ltac:(lia))).
Qed.
Lemma fd_insert_std3 : forall e, fd_insert APSG.fds_std (Z_to_bv 64 3) e = APSG.fds3 e.
Proof. intros e. unfold fd_insert, APSG.fds3. f_equal. Qed.
Lemma alloc_fd_fds_std : alloc_fd APSG.fds_std = Z_to_bv 64 3.
Proof. unfold APSG.fds_std. apply alloc_fd_std3. Qed.
Lemma fd_lookup_fds_std3 : fd_lookup APSG.fds_std (Z_to_bv 64 3) = None.
Proof. reflexivity. Qed.
Lemma wvb_fs : forall l mat (md : Model), m_fs (with_vm_backing l mat md) = m_fs md.
Proof. intros l mat md. destruct md; reflexivity. Qed.
Lemma wvb_fds : forall l mat (md : Model), m_fds (with_vm_backing l mat md) = m_fds md.
Proof. intros l mat md. destruct md; reflexivity. Qed.
(* The channel-reader twins of [wvb_fds] / [sbm_fds]: [fdchan] at LPS 727298f3 asks for the
   model's channel reader beside the descriptor, and neither a backing ledger nor a
   materialization touches the process state. *)
Lemma wvb_rdr : forall l mat (md : Model), m_channel_reader (with_vm_backing l mat md) = m_channel_reader md.
Proof. intros l mat md. destruct md; reflexivity. Qed.
Lemma sbm_fs : forall md md', same_but_materialized md md' -> m_fs md' = m_fs md.
Proof. intros md md' Hs. rewrite Hs. apply wvb_fs. Qed.
Lemma sbm_fds : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md.
Proof. intros md md' Hs. rewrite Hs. apply wvb_fds. Qed.
Lemma sbm_rdr : forall md md', same_but_materialized md md' -> m_channel_reader md' = m_channel_reader md.
Proof. intros md md' Hs. rewrite Hs. apply wvb_rdr. Qed.
Definition stk_win (rs : smem) : bool :=
existsb (fun r => match r_base r with Some 0%nat => (r_wlo r <=? -65536) && (0 <=? r_whi r) | _ => false end)%bool rs.
Lemma wview_off_hull : forall m a, APC.img_hi TFIB <= a < 2 ^ 64 -> wview TSEGS m (Z_to_bv 64 a) <> None -> m (Z_to_bv 64 a) <> None.
Proof.
intros m a Ha Hw. cbn in Ha. unfold wview in Hw. destruct (m (Z_to_bv 64 a)); [discriminate|].
rewrite (find_segment1_none_outside TSEGS (APC.img_lo TFIB) (APC.img_hi TFIB)) in Hw; [exact Hw | exact tfib_segs_in_hull |].
right. rewrite u64_lit by lia. cbn. lia.
Qed.
Lemma stk_present : forall (H : word -> bool) mem rs,
mem_ok tfibsegs EL (mrestrict H mem) rs -> stk_win rs = true ->
forall a, usp - 65536 <= a < usp -> mem (Z_to_bv 64 a) <> None.
Proof.
intros H mem rs (_ & HR & _) Hs a Ha. unfold stk_win in Hs. apply existsb_exists in Hs as (r & Hin & Hr).
pose proof (proj1 (Forall_forall _ _) HR r Hin) as (B1 & B2 & W & _).
destruct (r_base r) as [[|n]|]; try discriminate Hr. apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [base_val] in W. rewrite EL0 in W.
specialize (W (a - usp) ltac:(lia)). replace (usp + (a - usp)) with a in W by lia. unfold writable_at in W.
pose proof usp_lo as L. unfold sp_window_lo in L.
assert (Hm : mrestrict H mem (Z_to_bv 64 a) <> None).
{ apply (wview_off_hull (mrestrict H mem) a); [cbn; pose proof (u64_range sp); lia | exact W]. }
unfold mrestrict in Hm. destruct (H (Z_to_bv 64 a)); [exfalso; exact (Hm eq_refl) | exact Hm].
Qed.
Lemma frame_of_skel : forall E rs rs' (m m' : word -> option byte),
skeleton rs = skeleton rs' -> frame_of E rs' m m' -> frame_of E rs m m'.
Proof. intros E rs rs' m m' Hsk HF. eapply frame_of_trans; [exact Hsk | apply frame_of_refl | exact HF]. Qed.
Lemma ss_open_win_ok : forallb drv_win_ok (ss_mem ss_open) = true. Proof. reflexivity. Qed.
Lemma ss_open_stk : stk_win (ss_mem ss_open) = true. Proof. reflexivity. Qed.
Lemma ss_m1_stk : stk_win (ss_mem ss_m1) = true. Proof. reflexivity. Qed.
Lemma wbs_open : wr_below_sp (ss_facts ss_open) (smem_main true) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wbs_m1 : wr_below_sp (ss_facts ss_m1) (ss_mem ss_open) = true. Proof. vm_compute. reflexivity. Qed.
Lemma open_prefix : forall (W : world tfibsegs) ms md ly T,
st_ok tfibsegs EL (ss_main true) (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md -> top_ok usp ly ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> m_channel_reader md = true ->
(forall regs mem md',
regs_ok EL (ss_regs ss_open) regs ->
mem_ok tfibsegs EL (mrestrict (w_H W) mem) (ss_mem ss_open) ->
facts_ok EL (ss_facts ss_open) ->
runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn) ->
AI tfibsegs (w_H W) (w_A W) md' -> AR tfibsegs B ly init_state W mem md' -> FINV ly (w_H W) mem ->
m_fs md' = in_fs inp -> m_fds md' = APSG.fds_std -> m_channel_reader md' = true ->
bv_unsigned (getr regs 17%bv) = 56 ->
getr regs 10%bv = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12%bv)) open_ignored_flags = 0 ->
modeled_open_flags (getr regs 12%bv) = true ->
getr regs 11%bv = Z_to_bv 64 (z_argv ztop [a0; p] envp efn 1) ->
bv_unsigned (Z_to_bv 64 (z_argv ztop [a0; p] envp efn 1)) + Z.of_nat (length p) < TASK_SIZE ->
rdn tfibsegs mem (Z_to_bv 64 (z_argv ztop [a0; p] envp efn 1)) (length (p ++ [NUL])) = Some (p ++ [NUL]) ->
ranges_avoid (w_H W) (open_copyins (pend_at regs (Z_to_bv 64 (ss_pc ss_open)) mem (seg_rom tfibsegs))) ->
srealizes tfibsegs (mkCfg (pend_at regs (Z_to_bv 64 (ss_pc ss_open)) mem (seg_rom tfibsegs)) md') T) ->
srealizes tfibsegs (mkCfg ms md) T.
Proof.
intros W ms md ly T HS0 HR0 HAI0 HAR0 HTOP HFI0 Hfs Hfds Hcr K. pose proof (top_ok_ceil _ _ HTOP) as HCT.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) (at_open W ms md) T (open_run W ms md HS0) HAI0).
intros W' c' _ HAI' (-> & ms' & mat & -> & HS' & HF & HFr). cbn [cfg_model] in HAI'.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) EL ss_open ms' HS' eq_refl) as (regs & mem & Ems & Hregs & Hmem & HG).
rewrite Ems in HF, HFr |- *. cbn [ms_mem pend_at] in HF, HFr.
assert (HR : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn)).
{ eapply (runs_at_frame EL (ss_facts ss_open) (smem_main true)); [exact HG | exact wbs_open | exact HFr | rewrite EL0; lia | exact HR0]. }
assert (H11 : getr regs 11%bv = Z_to_bv 64 (z_argv ztop [a0; p] envp efn 1)).
{ rewrite (Hregs (11%bv:reg)); eval_sr_get; cbn [sv_denot]. rewrite Z.add_0_r, EL2. reflexivity. }
pose proof (runs_at_nth _ _ _ 2 _ _ HR eq_refl) as HBr. cbn [nth] in HBr.
pose proof (runs_at_bounds _ _ _ 2 _ _ HR eq_refl) as HBb. cbn [nth fst snd] in HBb. rewrite length_app in HBb. cbn [length] in HBb.
apply (K regs mem _ Hregs Hmem HG HR HAI').
- apply (AR_after_run B HB ARL ly init_state W EL (smem_main true) (ms_mem ms) mem md mat HAR0 (smem_main_win_ok true)).
+ rewrite EL0. exact usp_lo.
+ rewrite EL0. exact HCT.
+ exact HF.
+ rewrite EL0. exact (stk_present (w_H W) mem (ss_mem ss_open) Hmem ss_open_stk).
- exact (finv_run B ly init_state W (ms_mem ms) md (w_H W) EL (smem_main true) _ _ usp HAR0 HFr (smem_main_win_ok true) EL0 usp_lo (proj1 (proj2 Hsp)) HTOP HFI0).
- rewrite wvb_fs. exact Hfs.
- rewrite wvb_fds. exact Hfds.
- rewrite wvb_rdr. exact Hcr.
- rewrite (Hregs (17%bv:reg)); eval_sr_get; cbn [sv_denot]. reflexivity.
- rewrite (Hregs (10%bv:reg)); eval_sr_get; cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- exact H11.
- (* 75d69e00's TASK_SIZE premise, in the [bv_unsigned] form the four call sites need.
     The lower bound is [HBb]'s, the upper [argv1_task_size]'s. *)
pose proof argv1_task_size as Hub. pose proof (proj1 HBb) as Hlb.
pose proof usp_lo as Hul. unfold sp_window_lo in Hul.
assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
- exact (YP08.bytes_at_rdn tfibsegs mem _ _ (bytes_at_unrestrict _ _ _ _ HBr)).
- apply (open_copyins_avoid (w_H W) regs _ mem (z_argv ztop [a0; p] envp efn 1) H11); [pose proof usp_lo; pose proof (proj1 HBb); unfold sp_window_lo in *; lia | lia | exact HBr].
Qed.
Lemma errno_branch : forall (W : world tfibsegs) regs mem md' md'' ly e,
regs_ok EL (ss_regs ss_open) regs ->
mem_ok tfibsegs EL (mrestrict (w_H W) mem) (ss_mem ss_open) ->
facts_ok EL (ss_facts ss_open) ->
runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn) ->
AR tfibsegs B ly init_state W mem md' -> top_ok usp ly -> m_fs md' = in_fs inp -> m_fds md' = APSG.fds_std -> m_channel_reader md' = true ->
AI tfibsegs (w_H W) (w_A W) md'' -> same_but_materialized md' md'' ->
0 < e < 4096 ->
srealizes tfibsegs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)) md'')
(diag (msg_cannot_open p) (in_fs inp)).
Proof.
intros W regs mem md' md'' ly e Hregs Hmem HG HR HAR HTOP Hfs Hfds Hcr HAI Hs He.
apply (HCO sp brk mbase inp xw xd W regs mem md'' ly a0 p rnd e Hsp Hargv Hva Hve Hvl Hlau Hvi Hregs Hmem HG HR HAI);
[exact (AR_same_but_materialized B ly init_state W mem md' md'' HAR Hs) | exact HTOP | rewrite (sbm_fs _ _ Hs); exact Hfs
| rewrite (sbm_fds _ _ Hs); exact Hfds | rewrite (sbm_rdr _ _ Hs); exact Hcr | exact He].
Qed.
Definition ss_open3 : sstate := resume ss_open (SLit 3) (ss_mem ss_open) (ss_facts ss_open).
Definition at_m1 (W : world tfibsegs) (mem : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms')
/\ frame_of EL (ss_mem ss_open) mem (ms_mem ms')
/\ frame_of EL (ss_mem ss_open) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms')).
Lemma m1_run : forall (W : world tfibsegs) regs mem md,
st_ok tfibsegs EL ss_open3 (restrict (w_H W) (mkst regs (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)) md) (at_m1 W mem md).
Proof.
intros W regs mem md HS. pose proof HWXi as HWX.
let pc := eval vm_compute in A_m1_call in srr_run_to_with tfibtbl_drv_ok HS pc.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma success_branch : forall (W : world tfibsegs) regs mem md' md'' ly (e3 : FdEntry) T,
regs_ok EL (ss_regs ss_open) regs ->
mem_ok tfibsegs EL (mrestrict (w_H W) mem) (ss_mem ss_open) ->
facts_ok EL (ss_facts ss_open) ->
runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn) ->
AR tfibsegs B ly init_state W mem md' -> FINV ly (w_H W) mem -> top_ok usp ly -> m_fs md' = in_fs inp -> m_fds md' = APSG.fds_std -> m_channel_reader md' = true ->
AI tfibsegs (w_H W) (w_A W) md'' -> same_but_materialized (with_fds (APSG.fds3 e3) md') md'' ->
(forall ms1 md1,
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms1) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms1)) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn) ->
AI tfibsegs (w_H W) (w_A W) md1 -> AR tfibsegs B ly init_state W (ms_mem ms1) md1 ->
top_ok usp ly -> FINV ly (w_H W) (ms_mem ms1) -> m_fs md1 = in_fs inp -> m_fds md1 = APSG.fds3 e3 -> m_channel_reader md1 = true ->
srealizes tfibsegs (mkCfg ms1 md1) T) ->
srealizes tfibsegs
(mkCfg (mkst (regupd regs 10%bv (Z_to_bv 64 3)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)) md'') T.
Proof.
intros W regs mem md' md'' ly e3 T Hregs Hmem HG HR HAR HFI HTOP Hfs Hfds Hcr HAI Hs K. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof (st_ok_resume_sv tfibsegs EL ss_open regs (mrestrict (w_H W) mem) (SLit 3) (Z_to_bv 64 3) Hregs Hmem HG eq_refl) as HS.
rewrite <- restrict_mkst_fx in HS. change (resume _ _ _ _) with ss_open3 in HS.
apply (SRr_srealizes tfibsegs W _ (at_m1 W mem md'') T (m1_run W _ mem md'' HS) HAI).
intros W' c' _ HAI' (-> & ms1 & mat & -> & HS1 & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (AR_same_but_materialized B ly init_state W mem _ md'' (AR_with_fds B ly init_state W mem md' (APSG.fds3 e3) HAR) Hs) as HAR''.
apply (K ms1 _ HS1).
- eapply (runs_at_frame EL (ss_facts ss_m1) (ss_mem ss_open)); [exact (st_ok_facts_ok tfibsegs EL ss_m1 _ HS1) | exact wbs_m1 | exact HFr | rewrite EL0; lia | exact HR].
- exact HAI'.
- apply (AR_after_run B HB ARL ly init_state W EL (ss_mem ss_open) mem (ms_mem ms1) md'' mat HAR'' ss_open_win_ok).
+ rewrite EL0. exact usp_lo.
+ rewrite EL0. exact HCT.
+ exact HF.
+ rewrite EL0. pose proof HS1 as X. apply (st_ok_mem_ok tfibsegs EL ss_m1) in X. cbn [restrict ms_mem] in X.
exact (stk_present (w_H W) (ms_mem ms1) (ss_mem ss_m1) X ss_m1_stk).
- exact HTOP.
- exact (finv_run B ly init_state W mem md'' (w_H W) EL (ss_mem ss_open) _ _ usp HAR'' HFr ss_open_win_ok EL0 usp_lo (proj1 (proj2 Hsp)) HTOP HFI).
- rewrite wvb_fs, (sbm_fs _ _ Hs), with_fds_fs. exact Hfs.
- rewrite wvb_fds, (sbm_fds _ _ Hs), with_fds_fds. reflexivity.
- rewrite wvb_rdr, (sbm_rdr _ _ Hs). exact Hcr.
Qed.
Section f.
Variables (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout).
Hypothesis HS0 : st_ok tfibsegs EL (ss_main true) (restrict (w_H W) ms).
Hypothesis HR0 : runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn).
Hypothesis HAI0 : AI tfibsegs (w_H W) (w_A W) md.
Hypothesis HAR0 : AR tfibsegs B ly init_state W (ms_mem ms) md.
Hypothesis HTOP0 : top_ok usp ly.
Hypothesis HFI0 : FINV ly (w_H W) (ms_mem ms).
Hypothesis Hfs0 : m_fs md = in_fs inp.
Hypothesis Hfds0 : m_fds md = APSG.fds_std.
(* Beside [Hfds0]: the channel reader [fdchan] asks for at LPS 727298f3, from the hand-off
   ([cs_ok]'s [co_rdr]); never assumed above a top theorem. *)
Hypothesis Hcr0 : m_channel_reader md = true.
(* Convert the local input-list spelling after selecting the complete layout prefix. *)
Let Hnul1 : ~ In NUL p.
Proof.
assert (H : ~ In NUL (nth 1 (in_argv inp) []))
by (exact (YP08.argv_no_nul TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd
  Hsp Hva Hve Hvl Hlau 1 ltac:(rewrite Hargv; cbn; lia))).
rewrite Hargv in H. cbn [nth] in H. exact H.
Qed.
Let plain_name_of_argv : p <> dot_path -> openat_plain_name p = true.
Proof.
intros Hnd. pose proof Hva2 as (_ & _ & _ & _ & HF). cbn [tl] in HF. apply Forall_inv in HF. destruct HF as [Hs Hdd].
unfold openat_plain_name, path_is_dirref. rewrite Hs, Hdd.
destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; contradiction | reflexivity].
Qed.
Theorem tfib_open_file : forall data,
valid_fs (in_fs inp) -> (length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
srealizes tfibsegs (mkCfg ms md) (t_alt2 (diag (msg_cannot_open p) (in_fs inp)) (CLOSEDX_loaded data (in_fs inp))).
Proof.
intros data Hvfs Hlen Hne Hnd Hlk.
apply (open_prefix W ms md ly _ HS0 HR0 HAI0 HAR0 HTOP0 HFI0 Hfs0 Hfds0 Hcr0).
intros regs mem md' Hregs Hmem HG HR HAI HAR HFI Hfs Hfds Hcr H17 H10 H12 H12' H11 Hts Hrd Hav.
eapply (srz_openat_file_lazy tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) md' p data _ _ HAI H17 H10 H12).
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn tfibsegs mem _ p); [lia | exact Hnul1 | exact Hts |].
replace (length p + 1)%nat with (length (p ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact (plain_name_of_argv Hnd).
- rewrite Hfs. exact Hlk.
- rewrite Hfds, alloc_fd_fds_std. exact fd_lookup_fds_std3.
- exact Hav.
- intros e md'' He HAI'' Hs. exact (errno_branch W regs mem md' md'' ly e Hregs Hmem HG HR HAR HTOP0 Hfs Hfds Hcr HAI'' Hs (openat_errnos_small e He)).
- intros md'' HAI'' Hs. rewrite Hfds, alloc_fd_fds_std, fd_insert_std3 in Hs. rewrite Hfds, alloc_fd_fds_std.
apply (success_branch W regs mem md' md'' ly (FdFile p (Z_to_bv 64 0)) _ Hregs Hmem HG HR HAR HFI HTOP0 Hfs Hfds Hcr HAI'' Hs).
intros ms1 md1 HS1 HR1 HAI1 HAR1 HTOP1 HFI1 Hfs1 Hfds1 Hcr1.
(* [eapply] + [eassumption]: [file_arm_tfa] gained the entry draw and the launch premises
   (AD1v.v:140-155), so no call hard-codes its order (rule 25j). *)
eapply HFILE; eassumption.
Qed.
Theorem tfib_open_dir :
p = dot_path ->
srealizes tfibsegs (mkCfg ms md) (t_alt2 (diag (msg_cannot_open p) (in_fs inp)) (CLOSEDX_dir p (in_fs inp))).
Proof.
intros Hdot.
apply (open_prefix W ms md ly _ HS0 HR0 HAI0 HAR0 HTOP0 HFI0 Hfs0 Hfds0 Hcr0).
intros regs mem md' Hregs Hmem HG HR HAI HAR HFI Hfs Hfds Hcr H17 H10 H12 H12' H11 Hts Hrd Hav.
eapply (srz_openat_dir_lazy tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) md' _ _ HAI H17 H10 H12).
- rewrite pend_read_byte_mrb, H11, <- Hdot. apply (read_cstr_of_rdn tfibsegs mem _ p); [rewrite Hdot; cbn; lia | exact Hnul1 | exact Hts |].
replace (length p + 1)%nat with (length (p ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- rewrite Hfds, alloc_fd_fds_std. exact fd_lookup_fds_std3.
- exact Hav.
- intros e md'' He HAI'' Hs. exact (errno_branch W regs mem md' md'' ly e Hregs Hmem HG HR HAR HTOP0 Hfs Hfds Hcr HAI'' Hs (openat_errnos_small e He)).
- intros md'' HAI'' Hs. rewrite Hfds, alloc_fd_fds_std, fd_insert_std3 in Hs. rewrite Hfds, alloc_fd_fds_std.
apply (success_branch W regs mem md' md'' ly FdDir _ Hregs Hmem HG HR HAR HFI HTOP0 Hfs Hfds Hcr HAI'' Hs).
intros ms1 md1 HS1 HR1 HAI1 HAR1 HTOP1 HFI1 Hfs1 Hfds1 Hcr1.
eapply HDIR; eassumption.
Qed.
Theorem tfib_open_empty : p = [] -> srealizes tfibsegs (mkCfg ms md) (diag (msg_cannot_open p) (in_fs inp)).
Proof.
intros Hnil.
apply (open_prefix W ms md ly _ HS0 HR0 HAI0 HAR0 HTOP0 HFI0 Hfs0 Hfds0 Hcr0).
intros regs mem md' Hregs Hmem HG HR HAI HAR HFI Hfs Hfds Hcr H17 H10 H12 H12' H11 Hts Hrd Hav.
eapply (srz_openat_empty_lazy tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) md' _ HAI H17 H12').
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn tfibsegs mem _ []); [cbn; lia | intros [] | cbn [length]; lia |].
rewrite Hnil in Hrd |- *. cbn [length app Nat.add] in Hrd |- *. exact Hrd.
- exact Hav.
- intros md'' HAI'' Hs. apply (errno_branch W regs mem md' md'' ly ENOENT Hregs Hmem HG HR HAR HTOP0 Hfs Hfds Hcr HAI'' Hs). unfold ENOENT. lia.
Qed.
Theorem tfib_open_absent :
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = None ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_cannot_open p) (in_fs inp)).
Proof.
intros Hlen Hne Hnd Hlk.
apply (open_prefix W ms md ly _ HS0 HR0 HAI0 HAR0 HTOP0 HFI0 Hfs0 Hfds0 Hcr0).
intros regs mem md' Hregs Hmem HG HR HAI HAR HFI Hfs Hfds Hcr H17 H10 H12 H12' H11 Hts Hrd Hav.
eapply (srz_openat_absent_lazy tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) md' p _ HAI H17 H10 H12).
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn tfibsegs mem _ p); [lia | exact Hnul1 | exact Hts |].
replace (length p + 1)%nat with (length (p ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact (plain_name_of_argv Hnd).
- rewrite Hfs. exact Hlk.
- exact Hav.
- intros md'' HAI'' Hs. apply (errno_branch W regs mem md' md'' ly ENOENT Hregs Hmem HG HR HAR HTOP0 Hfs Hfds Hcr HAI'' Hs). unfold ENOENT. lia.
Qed.
Theorem tfib_open_toolong : (4096 <= length p)%nat -> srealizes tfibsegs (mkCfg ms md) (diag (msg_cannot_open p) (in_fs inp)).
Proof.
intros Hlen.
apply (open_prefix W ms md ly _ HS0 HR0 HAI0 HAR0 HTOP0 HFI0 Hfs0 Hfds0 Hcr0).
intros regs mem md' Hregs Hmem HG HR HAI HAR HFI Hfs Hfds Hcr H17 H10 H12 H12' H11 Hts Hrd Hav.
eapply (srz_openat_toolong_lazy tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) md' _ HAI H17 H12').
- rewrite pend_read_byte_mrb, H11.
assert (Hlenf : length (firstn 4096 p) = 4096%nat) by (rewrite length_firstn; lia).
apply (read_cstr_toolong_of_rdn tfibsegs mem _ (firstn 4096 p) Hlenf).
+ intros Hin. apply Hnul1. rewrite <- (firstn_skipn 4096 p). apply in_app_iff. left. exact Hin.
+ (* 75d69e00's TASK_SIZE premise on [read_cstr_toolong_of_rdn] (YK0p.v:340); this branch
     has [4096 <= length p], so [Hts] gives it. *)
lia.
+ pose proof (rdn_firstn tfibsegs mem (length (p ++ [NUL])) _ (p ++ [NUL]) 4096 Hrd ltac:(rewrite length_app; cbn; lia)) as Hf.
rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) in Hf by lia. cbn [firstn] in Hf. rewrite app_nil_r in Hf.
exact Hf.
- exact Hav.
- intros md'' HAI'' Hs. apply (errno_branch W regs mem md' md'' ly ENAMETOOLONG Hregs Hmem HG HR HAR HTOP0 Hfs Hfds Hcr HAI'' Hs). unfold ENAMETOOLONG. lia.
Qed.
Theorem tfib_open_all : valid_fs (in_fs inp) -> srealizes tfibsegs (mkCfg ms md) (CLOSEDX_args [a0; p] (in_fs inp)).
Proof.
intros Hvfs. unfold CLOSEDX_args, classify_open.
destruct (Nat.leb_spec path_max (length p)) as [Hl|Hl]; [apply tfib_open_toolong; exact Hl|].
change path_max with 4096%nat in Hl.
destruct (path_eqb p []) eqn:E1.
{ apply path_eqb_eq in E1. apply tfib_open_empty. exact E1. }
assert (Hne : p <> []) by (intros X; rewrite X in E1; discriminate E1).
destruct (path_eqb p dot_path) eqn:E2.
{ apply path_eqb_eq in E2. apply tfib_open_dir. exact E2. }
assert (Hnd : p <> dot_path) by (intros X; rewrite X in E2; discriminate E2).
destruct (fs_lookup (in_fs inp) p) as [data|] eqn:Hlk.
- apply (tfib_open_file data Hvfs Hl Hne Hnd Hlk).
- apply (tfib_open_absent Hl Hne Hnd Hlk).
Qed.
End f.
End d.
Theorem tfib_arm_argv2 (B : asyms) (HB : GrantSyms B) (ARL : AR_laws tfibsegs B)
(HCO : cannot_open_tfa B) (HFILE : file_arm_tfa B) (HDIR : dir_arm_tfa B) :
forall (sp brk mbase : word) (inp : ProcInput) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p : list byte),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
st_ok tfibsegs (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp))
(in_argv inp) (in_envp inp) (in_execfn inp) xw xd) (ss_main true) (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> m_channel_reader md = true ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_args [a0; p] (in_fs inp)).
Proof.
intros sp brk mbase inp rnd xw xd W ms md ly a0 p Hsp Hargv Hva Hve Hvl Hlau Hvi Hvfs HS HR HAI HAR HTOP HFI Hfs Hfds Hcr.
rewrite Hargv in HS, HR.
(* [eapply] + [eassumption]: [tfib_open_all] is discharged over Section d's variable list,
   so no call here hard-codes its order (rule 25j). *)
eapply (tfib_open_all B HB ARL HCO HFILE HDIR); eassumption.
Qed.
End c.
