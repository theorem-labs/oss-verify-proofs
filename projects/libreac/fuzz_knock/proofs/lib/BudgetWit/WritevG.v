(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3g.v, with its module paths and addresses changed. *)
(* Modified by Rares Buhai, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YL0v.v, with its module paths, addresses and numbers changed; 9 of its 714 lines of code are new or changed and 9 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YN3g.v and Reusable/YL0v.v: their realizes lemmas and the tactics that build realizes goals restated over BudgetWit.Rzb.rzb. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO05 YO00.
From OSSVerify.libreac.fuzz_knock.images Require Import Plain.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YL0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit Require Import Rzb RunB WritevF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(** * The [writev] lemmas of [YN3g] and [YL0v] over [rzb]

    Each lemma below is the lemma of [Reusable/YN3g.v] or [Reusable/YL0v.v]
    that concludes [YK15.realizes], with [realizes] written [rzb]
    ([BudgetWit.Rzb]), the same binders in the same order, and the released
    proof with each mirrored name renamed:
    - [YN3g]: [rz_writev_empty] -> [rzb_writev_empty],
      [rz_sym_stdio_writev2] -> [rzb_sym_stdio_writev2],
      [rz_sym_stdio_writev1] -> [rzb_sym_stdio_writev1],
      [rz_sym_writev_empty] -> [rzb_sym_writev_empty];
    - [YL0v]: [wl2_sound] -> [wl2_sound_b], [wl1_sound] -> [wl1_sound_b],
      [wl0_sound] -> [wl0_sound_b].
    No statement changes.  One proof step differs: [RunB.rzb_ret_only_copyins_silent]
    asks for [grant_ok] at its pending syscall right after its [check_syscall]
    premise; [rzb_writev_empty] gives it by [grant_ok_no], from its premise that
    the syscall number is 66 (writev, off the allocation numbers).

    The [YL0v] tactics that match a [realizes] goal or name a mirrored lemma are
    copied under their own names, bodies changed only by the renames, so that a
    file importing this module after [YL0v] runs them on [rzb] goals:
    [wl_writev2], [wl_writev1], [wl_writev0], [fpf_memchr], [fpf_lbu_nul],
    [fpf_memcpy_str], [fpf_memcpy_lit].  The [fpf_] copies call
    [sym_splice_havoc] and [sym_step_manual], which resolve to the copies in
    [BudgetWit.RunB].  The other [YL0v] tactics ([wl_transport],
    [fpf_split_window], [fpf_mem_window], [rdn_buf]) build no [realizes] goal and
    are used from [YL0v].  Declarations that do not mention [realizes] are the
    released ones, used by import. *)

(** ** Mirrors of [YN3g] *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Section e.
Variable segs : list Segment.
Lemma rzb_writev_empty : forall regs pc mem rom model fd ch (b0 : word) T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some (Z_to_bv 64 0) ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 0 = true ->
rzb segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) model) T ->
rzb segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd ch b0 T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hiok Hok0 Hc.
eapply (rzb_ret_only_copyins_silent segs regs pc mem rom model [(getr regs 11, 16%nat)]
(Z_to_bv 64 0) model T Hh Hlz);
[| eapply grant_ok_no; [reflexivity | exact Hno | reflexivity] |exact Hh|exact Hlz|exact Hc].
intros eff. rewrite (chk66 segs) by exact Hno. rewrite Hfd, H32.
destruct Hfdc as [Hlk Hch].
unfold check_writev. cbn [in_mem sys_input]. rewrite Hlk, Hch, Hcnt.
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Hiok. cbn [negb].
rewrite (read_iovec_entry_of (pend_at regs pc mem rom) (getr regs 11) b0 (Z_to_bv 64 0) Hb0 Hl0)
by (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia).
change (Z.min (bv_unsigned (Z_to_bv 64 0)) MAX_RW_COUNT) with 0%Z. rewrite Hok0. cbn [negb].
cbv zeta.
replace (iovs_total (cap_iovecs [(b0, Z_to_bv 64 0)]) =? 0)%Z with true by reflexivity.
reflexivity.
Qed.
End e.
Theorem rzb_sym_stdio_writev2 :
forall E ss ms model fd ch (i b : nat) (K F : Z) r vb0 vl0 vb1 vl1 bs0 bs1 fdbs (k : nat) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = WL_ECALL1 ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd -> bv_unsigned fd < 2^31 ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 2 -> sv_denot E (sr_get (ss_regs ss) 18) = Z_to_bv 64 2 ->
sr_get (ss_regs ss) 2 = SOff b K ->
sr_get (ss_regs ss) 19 = SOff b (K + 8) -> sr_get (ss_regs ss) 11 = SOff b (K + 8) ->
U E (sr_get (ss_regs ss) 22) = U E vl0 + U E vl1 ->
U E (sr_get (ss_regs ss) 9) = F ->
nth_error (ss_mem ss) i = Some r -> r_base r = Some b ->
r_lo r <= K + 8 -> K + 40 <= r_hi r -> r_wlo r <= K + 8 -> K + 40 <= r_whi r ->
iov_read2 (ss_mem ss) (Some b) (K + 8) = Some (vb0, vl0, vb1, vl1) ->
rdn src0segs (ms_mem ms) (sv_denot E vb0) (word_to_nat (sv_denot E vl0)) = Some bs0 ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl0 + U E vl1 <= 2^25 ->
U E vb0 + U E vl0 <= 2^47 ->
(U E vb0 + U E vl0 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb0) ->
U E vb1 + U E vl1 <= 2^47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 (F + 120)) 4 = Some fdbs -> bytes_le_to_Z fdbs = bv_unsigned fd ->
0 <= F -> F + 124 <= 2^64 ->
(F + 124 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= F + 120) ->
0 <= bv_unsigned (ew E b) + K -> bv_unsigned (ew E b) + K + 40 <= 2^47 ->
ss_atoms_lt k ss = true ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb src0segs (mkCfg ms' model) T) ->
rzb src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros E ss ms model fd ch i b K F r vb0 vl0 vb1 vl1 bs0 bs1 fdbs k T
Hh Hlz HS Hrv Hpc H17 H10 Hfdc H32 Hfd31 H12 H18 H2 H19 H11 H22 H9 Hi Hb Hrlo Hrhi Hwlo Hwhi
Hiov Hbs0 Hbs1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hfd Hfdv HF0 HF1 HFW HSP0 HSP1 Hat Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
rewrite Hpc. cbn [ms_mem pend_at] in Hbs0, Hbs1, Hfd, Hk.
set (SP := bv_unsigned (ew E b) + K).
pose proof (U_range E vb0) as R0. pose proof (U_range E vl0) as R1.
pose proof (U_range E vb1) as R2. pose proof (U_range E vl1) as R3. unfold M64 in R0, R1, R2, R3.
unfold iov_read2 in Hiov.
destruct (iov_read1 (ss_mem ss) (Some b) (K + 8)) as [[x0 y0]|] eqn:Hi0; [|discriminate].
destruct (iov_read1 (ss_mem ss) (Some b) (K + 8 + 16)) as [[x1 y1]|] eqn:Hi1; [|discriminate].
injection Hiov as -> -> -> ->.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hi0) as [M0 L0].
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hi1) as [M1 L1].
cbn [base_val] in M0, L0, M1, L1.
rewrite (denot_lit_U E vb0) in M0, Hbs0. rewrite (denot_lit_U E vl0) in L0.
rewrite (denot_lit_U E vb1) in M1, Hbs1. rewrite (denot_lit_U E vl1) in L1.
rewrite word_to_nat_U in Hbs0, Hbs1.
pose proof (rdn_length _ _ _ _ _ Hbs0) as Hl0. pose proof (rdn_length _ _ _ _ _ Hbs1) as Hl1.
apply (wl_entry_pend_b model Hh Hlz fd ch Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfd Hfdv)
with (c := 2) (b0 := U E vb0) (l0 := U E vl0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' Hkept H17' Hout Hst'.
apply (Hk (mkst regs' (Z_to_bv 64 0x15c9c) mem' (seg_rom src0segs)) (map (getr regs') WL_CLOB)).
+ set (E' := havoc E k (map (getr regs') WL_CLOB)).
assert (HA : env_agree k E E') by apply env_agree_havoc.
unfold ss_atoms_lt in Hat. rewrite Hrv in Hat.
apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat HGa]. apply andb_prop in Hat as [Hra Hma].
unfold st_ok, wl_after. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [|split].
*
apply (regs_ok_sets E' (ss_regs ss) regs regs').
-- eapply regs_ok_agree; eauto.
-- apply reg_nodup_sound. vm_compute. reflexivity.
-- intros r0 Hr0. destruct (wl_kept_of_reg_in r0 Hr0) as [_ Hk0]. apply Hkept. exact Hk0.
-- constructor.
++ cbn [fst snd]. split; [reflexivity|]. cbn [sv_denot]. rewrite H17'. reflexivity.
++ subst E'. apply junk_upd_ok0. vm_compute. reflexivity.
*
eapply mem_ok_agree; [exact HA| |].
{ apply (mem_atoms_lt_submem k _ (ss_mem ss)); [apply submem_forget_win | exact Hma]. }
apply (mem_ok_window_change src0segs E mem mem' _ i (keep_chunks (chunk_out (K + 8) (K + 40)) r) (K + 8) (K + 40)).
-- apply mem_ok_forget_win. exact Hmem.
-- apply nth_error_forget_win. exact Hi.
-- cbn. lia. -- lia. -- cbn. lia.
-- apply keep_chunks_out.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx. apply Hout. unfold inW. subst SP. lia.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx.
apply (store_ok_all src0segs mem' 32 (Z_to_bv 64 (SP + 8))); [rewrite u_Z2bv by lia; subst SP; lia| exact Hst'|].
rewrite u_Z2bv by (subst SP; lia). subst SP. cbn. lia.
* eapply facts_ok_agree; eauto.
+
cbn [ms_mem mkst]. intros x Hnw. apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
-
unfold wl_inv. cbn [Z.eqb Pos.eqb].
assert (G : forall rr : reg, getr regs rr = sv_denot E (sr_get (ss_regs ss) rr)) by (intros rr; apply Hregs).
repeat match goal with |- _ /\ _ => split end; try lia.
+ rewrite G, H2. cbn [sv_denot]. reflexivity.
+ rewrite G, denot_lit_U, H9. reflexivity.
+ rewrite G. exact H18.
+ rewrite G. exact H12.
+ rewrite G, H19. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, H11. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, denot_lit_U, H22. reflexivity.
+ rewrite G. exact H10.
+ rewrite G, H17. reflexivity.
+ intros rr _. reflexivity.
+ intros a _. reflexivity.
+ replace (Z_to_bv 64 (SP + 8)) with (Z_to_bv 64 (base_val E (r_base r) + (K + 8))) by (rewrite Hb; cbn [base_val]; f_equal; subst SP; lia).
apply (store_ok_of_region src0segs E mem (ss_mem ss) i r (K + 8) 32 Hmem Hi); try (cbn; lia);
rewrite Hb; cbn [base_val]; subst SP; lia.
+ unfold iov_mem. split; [intros _; split|split].
* replace (SP + 8) with (bv_unsigned (ew E b) + (K + 8)) by (subst SP; lia). exact M0.
* replace (SP + 16) with (bv_unsigned (ew E b) + (K + 8) + 8) by (subst SP; lia). exact L0.
* replace (SP + 24) with (bv_unsigned (ew E b) + (K + 8 + 16)) by (subst SP; lia). exact M1.
* replace (SP + 32) with (bv_unsigned (ew E b) + (K + 8 + 16) + 8) by (subst SP; lia). exact L1.
+ intros _. exact Hbs0.
+ exact Hbs1.
Qed.
Theorem rzb_sym_stdio_writev1 :
forall E ss ms model fd ch (i b : nat) (K F : Z) r vb1 vl1 bs1 fdbs (k : nat) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = WL_ECALL1 ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd -> bv_unsigned fd < 2^31 ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 -> sv_denot E (sr_get (ss_regs ss) 18) = Z_to_bv 64 1 ->
sr_get (ss_regs ss) 2 = SOff b K ->
sr_get (ss_regs ss) 19 = SOff b (K + 24) -> sr_get (ss_regs ss) 11 = SOff b (K + 24) ->
U E (sr_get (ss_regs ss) 22) = U E vl1 ->
U E (sr_get (ss_regs ss) 9) = F ->
nth_error (ss_mem ss) i = Some r -> r_base r = Some b ->
r_lo r <= K + 8 -> K + 40 <= r_hi r -> r_wlo r <= K + 8 -> K + 40 <= r_whi r ->
iov_read1 (ss_mem ss) (Some b) (K + 24) = Some (vb1, vl1) ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl1 <= 2^25 ->
U E vb1 + U E vl1 <= 2^47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 (F + 120)) 4 = Some fdbs -> bytes_le_to_Z fdbs = bv_unsigned fd ->
0 <= F -> F + 124 <= 2^64 ->
(F + 124 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= F + 120) ->
0 <= bv_unsigned (ew E b) + K -> bv_unsigned (ew E b) + K + 40 <= 2^47 ->
ss_atoms_lt k ss = true ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb src0segs (mkCfg ms' model) T) ->
rzb src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) bs1) T).
Proof.
intros E ss ms model fd ch i b K F r vb1 vl1 bs1 fdbs k T
Hh Hlz HS Hrv Hpc H17 H10 Hfdc H32 Hfd31 H12 H18 H2 H19 H11 H22 H9 Hi Hb Hrlo Hrhi Hwlo Hwhi
Hiov Hbs1 Hlen Hnw1 Hd1 Hfd Hfdv HF0 HF1 HFW HSP0 HSP1 Hat Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
rewrite Hpc. cbn [ms_mem pend_at] in Hbs1, Hfd, Hk.
set (SP := bv_unsigned (ew E b) + K).
pose proof (U_range E vb1) as R2. pose proof (U_range E vl1) as R3. unfold M64 in R2, R3.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hiov) as [M1 L1].
cbn [base_val] in M1, L1.
rewrite (denot_lit_U E vb1) in M1, Hbs1. rewrite (denot_lit_U E vl1) in L1.
rewrite word_to_nat_U in Hbs1.
pose proof (rdn_length _ _ _ _ _ Hbs1) as Hl1.
change bs1 with ([] ++ bs1).
apply (wl_entry_pend_b model Hh Hlz fd ch Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfd Hfdv)
with (c := 1) (b0 := 0) (l0 := 0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' Hkept H17' Hout Hst'.
apply (Hk (mkst regs' (Z_to_bv 64 0x15c9c) mem' (seg_rom src0segs)) (map (getr regs') WL_CLOB)).
+ set (E' := havoc E k (map (getr regs') WL_CLOB)).
assert (HA : env_agree k E E') by apply env_agree_havoc.
unfold ss_atoms_lt in Hat. rewrite Hrv in Hat.
apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat HGa]. apply andb_prop in Hat as [Hra Hma].
unfold st_ok, wl_after. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [|split].
*
apply (regs_ok_sets E' (ss_regs ss) regs regs').
-- eapply regs_ok_agree; eauto.
-- apply reg_nodup_sound. vm_compute. reflexivity.
-- intros r0 Hr0. destruct (wl_kept_of_reg_in r0 Hr0) as [_ Hk0]. apply Hkept. exact Hk0.
-- constructor.
++ cbn [fst snd]. split; [reflexivity|]. cbn [sv_denot]. rewrite H17'. reflexivity.
++ subst E'. apply junk_upd_ok0. vm_compute. reflexivity.
*
eapply mem_ok_agree; [exact HA| |].
{ apply (mem_atoms_lt_submem k _ (ss_mem ss)); [apply submem_forget_win | exact Hma]. }
apply (mem_ok_window_change src0segs E mem mem' _ i (keep_chunks (chunk_out (K + 8) (K + 40)) r) (K + 8) (K + 40)).
-- apply mem_ok_forget_win. exact Hmem.
-- apply nth_error_forget_win. exact Hi.
-- cbn. lia. -- lia. -- cbn. lia.
-- apply keep_chunks_out.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx. apply Hout. unfold inW. subst SP. lia.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx.
apply (store_ok_all src0segs mem' 32 (Z_to_bv 64 (SP + 8))); [rewrite u_Z2bv by lia; subst SP; lia| exact Hst'|].
rewrite u_Z2bv by (subst SP; lia). subst SP. cbn. lia.
* eapply facts_ok_agree; eauto.
+
cbn [ms_mem mkst]. intros x Hnw. apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
-
unfold wl_inv. cbn [Z.eqb Pos.eqb].
assert (G : forall rr : reg, getr regs rr = sv_denot E (sr_get (ss_regs ss) rr)) by (intros rr; apply Hregs).
repeat match goal with |- _ /\ _ => split end; try lia.
+ rewrite G, H2. cbn [sv_denot]. reflexivity.
+ rewrite G, denot_lit_U, H9. reflexivity.
+ rewrite G. exact H18.
+ rewrite G. exact H12.
+ rewrite G, H19. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, H11. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, denot_lit_U, H22. reflexivity.
+ rewrite G. exact H10.
+ rewrite G, H17. reflexivity.
+ intros rr _. reflexivity.
+ intros a _. reflexivity.
+ replace (Z_to_bv 64 (SP + 8)) with (Z_to_bv 64 (base_val E (r_base r) + (K + 8))) by (rewrite Hb; cbn [base_val]; f_equal; subst SP; lia).
apply (store_ok_of_region src0segs E mem (ss_mem ss) i r (K + 8) 32 Hmem Hi); try (cbn; lia);
rewrite Hb; cbn [base_val]; subst SP; lia.
+ unfold iov_mem. split; [intros HX; lia|split].
* replace (SP + 24) with (bv_unsigned (ew E b) + (K + 24)) by (subst SP; lia). exact M1.
* replace (SP + 32) with (bv_unsigned (ew E b) + (K + 24) + 8) by (subst SP; lia). exact L1.
+ exact Hbs1.
+ reflexivity.
Qed.
Theorem rzb_sym_writev_empty : forall E ss ms model fd ch b off vb0 vl0 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
sr_get (ss_regs ss) 12 = SLit 1 ->
U E (sr_get (ss_regs ss) 11) = base_val E b + off ->
iov_read1 (ss_mem ss) b off = Some (vb0, vl0) -> U E vl0 = 0 ->
base_val E b + off + 16 <= 2^47 -> U E vb0 <= 2^47 ->
(forall ms', st_ok src0segs E (resume ss (SLit 0) (ss_mem ss) (ss_facts ss)) ms' -> ms_mem ms' = ms_mem ms ->
rzb src0segs (mkCfg ms' model) T) ->
rzb src0segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd ch b off vb0 vl0 T Hh Hlz HS Hrv H17 H10 Hfdc H32 H12 H11 Hiov Hvl0 Hiok Hok0 Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hiov) as [M0 L0].
assert (Ha11 : getr regs 11 = Z_to_bv 64 (base_val E b + off)).
{ rewrite (Hregs 11%bv), denot_lit_U, H11. reflexivity. }
eapply (rzb_writev_empty src0segs regs _ mem (seg_rom src0segs) model fd ch (sv_denot E vb0) T Hh Hlz).
- rewrite (Hregs 17%bv), H17. reflexivity.
- exact Hfdc. - exact H32.
- rewrite (Hregs 10%bv). exact H10.
- rewrite (Hregs 12%bv), H12. reflexivity.
- apply ms_read_u64_of_rdn. rewrite Ha11. exact M0.
- apply ms_read_u64_of_rdn.
pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11, u_Z2bv by lia.
rewrite (denot_lit_U E vl0), Hvl0 in L0. exact L0.
- pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11. unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- pose proof (U_range E vb0) as R0. unfold M64 in R0.
rewrite (denot_lit_U E vb0). unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- apply Hk; [|reflexivity].
change (Z_to_bv 64 0) with (sv_denot E (SLit 0)).
apply st_ok_resume_sv; auto.
Qed.
End d.

(** ** Mirrors of [YL0v] *)
Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Theorem wl2_sound_b : forall E ss ms model ch k i b K F fd vb0 vl0 vb1 vl1 bs0 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms ->
wl_site2 k ss = Some (i, b, K, F, fd, (vb0, vl0, vb1, vl1)) ->
fdchan (Z_to_bv 64 fd) ch model ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 2 ->
U E (sr_get (ss_regs ss) 22) = U E vl0 + U E vl1 ->
rdn src0segs (ms_mem ms) (sv_denot E vb0) (word_to_nat (sv_denot E vl0)) = Some bs0 ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl0 + U E vl1 <= 2 ^ 25 ->
U E vb0 + U E vl0 <= 2 ^ 47 ->
(U E vb0 + U E vl0 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb0) ->
U E vb1 + U E vl1 <= 2 ^ 47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb src0segs (mkCfg ms' model) T) ->
rzb src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros E ss ms model ch k i b K F fd vb0 vl0 vb1 vl1 bs0 bs1 T Hh Hlz HS Hck Hch H12 H22 Hb0 Hb1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hk.
unfold wl_site2 in Hck.
destruct (wl_site_common k ss) as [[[[[i' b'] K'] F'] fd']|] eqn:Hc; [|discriminate].
destruct (sv_eqb (sr_get (ss_regs ss) 19) (SOff b' (K' + 8))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (iov_read2 (ss_mem ss) (Some b') (K' + 8)) as [[[[x0 y0] x1] y1]|] eqn:Hiov; [|discriminate].
injection Hck as -> -> -> -> -> -> -> -> ->.
destruct (wl_site_common_sound E ss ms k i b K F fd HS Hc)
as (Hpc & H17 & D10 & Hfd12 & H2 & H9 & Hrv & Hat & H18 & H11 & (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi) & B1 & B2 & B3 & B4 & B5 & Hfdrd).
destruct (fd_facts fd Hfd12) as (H32 & Hfd31 & HfdB).
eapply (rzb_sym_stdio_writev2 E ss ms model (Z_to_bv 64 fd) ch i b K F r vb0 vl0 vb1 vl1 bs0 bs1 _ k T Hh Hlz HS Hrv Hpc
H17 D10 Hch H32 Hfd31 H12 (eq_trans H18 H12) H2 H19 ltac:(rewrite H11; exact H19) H22 H9
Hi Hrb Hrlo Hrhi Hwlo Hwhi Hiov Hb0 Hb1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hfdrd HfdB B3 B4 (or_introl B5) B1 B2 Hat Hk).
Qed.
Theorem wl1_sound_b : forall E ss ms model ch k i b K F fd vb1 vl1 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms ->
wl_site1 k ss = Some (i, b, K, F, fd, (vb1, vl1)) ->
fdchan (Z_to_bv 64 fd) ch model ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 ->
U E (sr_get (ss_regs ss) 22) = U E vl1 ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl1 <= 2 ^ 25 ->
U E vb1 + U E vl1 <= 2 ^ 47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb src0segs (mkCfg ms' model) T) ->
rzb src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) bs1) T).
Proof.
intros E ss ms model ch k i b K F fd vb1 vl1 bs1 T Hh Hlz HS Hck Hch H12 H22 Hb1 Hlen Hnw1 Hd1 Hk.
unfold wl_site1 in Hck.
destruct (wl_site_common k ss) as [[[[[i' b'] K'] F'] fd']|] eqn:Hc; [|discriminate].
destruct (sv_eqb (sr_get (ss_regs ss) 19) (SOff b' (K' + 24))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (iov_read1 (ss_mem ss) (Some b') (K' + 24)) as [[x1 y1]|] eqn:Hiov; [|discriminate].
injection Hck as -> -> -> -> -> -> ->.
destruct (wl_site_common_sound E ss ms k i b K F fd HS Hc)
as (Hpc & H17 & D10 & Hfd12 & H2 & H9 & Hrv & Hat & H18 & H11 & (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi) & B1 & B2 & B3 & B4 & B5 & Hfdrd).
destruct (fd_facts fd Hfd12) as (H32 & Hfd31 & HfdB).
eapply (rzb_sym_stdio_writev1 E ss ms model (Z_to_bv 64 fd) ch i b K F r vb1 vl1 bs1 _ k T Hh Hlz HS Hrv Hpc
H17 D10 Hch H32 Hfd31 H12 (eq_trans H18 H12) H2 H19 ltac:(rewrite H11; exact H19) H22 H9
Hi Hrb Hrlo Hrhi Hwlo Hwhi Hiov Hb1 Hlen Hnw1 Hd1 Hfdrd HfdB B3 B4 (or_introl B5) B1 B2 Hat Hk).
Qed.
End e2.
Ltac wl_writev2 HS Hch k :=
lazymatch type of HS with st_ok_ecall _ ?E ?ss ?ms =>
lazymatch goal with |- rzb _ (mkCfg _ ?model) _ =>
let r := eval vm_compute in (wl_site2 k ss) in
lazymatch r with
| Some (?i, ?b, ?K, ?F, ?fd, (?vb0, ?vl0, ?vb1, ?vl1)) =>
let Hck := fresh "Hck" in
assert (Hck : wl_site2 k ss = Some (i, b, K, F, fd, (vb0, vl0, vb1, vl1))) by (vm_compute; reflexivity);
eapply (wl2_sound_b E ss ms model _ k i b K F fd vb0 vl0 vb1 vl1 _ _ _ ltac:(assumption) ltac:(assumption) HS Hck Hch);
clear Hck;
[ eval_sr_get | eval_sr_get | | | | | | |
| let ms' := fresh "ms" in let ws := fresh "ws" in let HS' := fresh "HS'" in let HF := fresh "HF" in
let HGf := fresh "HGf" in
intros ms' ws HS' HF;
pose proof (st_ok_ecall_facts E ss ms HS) as HGf;
wl_transport E ss ms ms' HGf HF;
env_transport (havoc E k ws) (env_agree_havoc E k ws);
clear HF HGf HS; try clear ms; rename HS' into HS; sym_norm HS ]
| _ => fail "wl_writev2: site check failed"
end
end end.
Ltac wl_writev1 HS Hch k :=
lazymatch type of HS with st_ok_ecall _ ?E ?ss ?ms =>
lazymatch goal with |- rzb _ (mkCfg _ ?model) _ =>
let r := eval vm_compute in (wl_site1 k ss) in
lazymatch r with
| Some (?i, ?b, ?K, ?F, ?fd, (?vb1, ?vl1)) =>
let Hck := fresh "Hck" in
assert (Hck : wl_site1 k ss = Some (i, b, K, F, fd, (vb1, vl1))) by (vm_compute; reflexivity);
eapply (wl1_sound_b E ss ms model _ k i b K F fd vb1 vl1 _ _ ltac:(assumption) ltac:(assumption) HS Hck Hch);
clear Hck;
[ eval_sr_get | eval_sr_get | | | |
| let ms' := fresh "ms" in let ws := fresh "ws" in let HS' := fresh "HS'" in let HF := fresh "HF" in
let HGf := fresh "HGf" in
intros ms' ws HS' HF;
pose proof (st_ok_ecall_facts E ss ms HS) as HGf;
wl_transport E ss ms ms' HGf HF;
env_transport (havoc E k ws) (env_agree_havoc E k ws);
clear HF HGf HS; try clear ms; rename HS' into HS; sym_norm HS ]
| _ => fail "wl_writev1: site check failed"
end
end end.
Ltac fpf_memchr HS HR si bi n k s :=
let H10 := fresh "H10" in let H11 := fresh "H11" in let H12 := fresh "H12" in let Hra := fresh "Hra" in
let HBs := fresh "HBs" in let HBb := fresh "HBb" in let Hp := fresh "Hp" in
let Hover := fresh "Hover" in let Hrom := fresh "Hrom" in
reg_of HS (10%bv:reg) H10; reg_of HS (11%bv:reg) H11; reg_of HS (12%bv:reg) H12; reg_of HS (1%bv:reg) Hra;
lazymatch goal with |- rzb _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E ?ss _ =>
pose proof (runs_at_nth _ (ms_mem ms) _ si _ _ HR eq_refl) as HBs;
pose proof (runs_at_nth _ (ms_mem ms) _ bi _ _ HR eq_refl) as HBb;
cbn [nth_error runs_main app] in HBs, HBb;
lazymatch type of HBs with YP03.bytes_at _ ?a _ =>
assert (Hp : bv_unsigned (ew E n) = a) by (evalE; lia);
assert (Hover : forall x,
bv_unsigned (ew E n) + Z.of_nat (length s) < x <
bv_unsigned (ew E n) + Z.of_nat (length s) - (bv_unsigned (ew E n) + Z.of_nat (length s)) mod 8 + 8 ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 x) 1 <> None)
by (rewrite Hp; refine (bsb_over_read _ _ _ _ (ms_mem ms) a (Z.of_nat (length s)) _ HBb _ _); [assumption| lia| lia]);
pose proof (rom_reads _ _ _ HS ltac:(vm_compute; reflexivity)) as Hrom;
let Hnul := lazymatch goal with H : ~ In _ s |- _ => H end in
let Hrd := constr:(fun j (Hj : (j <= length s)%nat) =>
eq_trans (f_equal (fun z => rdn src0segs (ms_mem ms) (Z_to_bv 64 (z + Z.of_nat j)) 1) Hp)
(str_reads (ms_mem ms) a s HBs j Hj)) in
let regs1 := fresh "regs" in let Hms := fresh "Hms" in
let R10 := fresh "R10" in let R11 := fresh "R11" in let R12 := fresh "R12" in let R13 := fresh "R13" in
let Rfr := fresh "Rfr" in
destruct (src0_memchr s (ew E n) (Z_to_bv 64 0x7fffffff) (ms_mem ms) (seg_rom src0segs) (ms_regs ms) Hnul
ltac:(rewrite Hp; lia)
ltac:(rewrite unsigned_lit_small by lia; lia)
Hrd Hover Hrom H10 H11 H12)
as (regs1 & Hms & R10 & R11 & R12 & R13 & Rfr);
rewrite Hra in Hms; change (v_jalr (Z_to_bv 64 109856) 0) with (Z_to_bv 64 0x1ad20) in Hms;
clear Hover Hrom H10 H11 H12 Hra HBs HBb;
sym_new_atom HS k (Z_to_bv 64 (Z.of_nat (length s)));
let k1 := eval cbv in (k + 1)%nat in
sym_splice_havoc HS Hms k1 (upd_memchr n k) junk_memchr;
[ sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot]; rewrite ?ew_ewset_same, ?ew_ewset_other by lia;
rewrite ?Z.add_0_r;
[ rewrite R10, zalu64_sound; apply Z_to_bv64_eq_mod; unfold zalu64, zcanon, M64; cbn [zalu_raw];
rewrite (unsigned_lit_small (Z.of_nat _)) by lia; pose proof (u64_range (ew E n));
rewrite !(Z.mod_small _ (2^64)) by lia; reflexivity
| exact R11
| exact R12
| rewrite R13, zalu64_sound; apply Z_to_bv64_eq_mod; unfold zalu64, zcanon, M64; cbn [zalu_raw];
rewrite !unsigned_lit_small by lia; rewrite !(Z.mod_small _ (2^64)) by lia; reflexivity ]
| lazymatch goal with H : st_ok _ _ _ _ |- _ => exact (st_ok_mem_ok src0segs _ _ _ H) end
| clear R10 R11 R12 R13 Rfr Hp;
sym_add_fact HS k (mkAF 0 131071 0); [atom_fact_lit|] ]
end end end.
Ltac fpf_lbu_nul HS HR si n k s :=
let H11 := fresh "H11" in let HBs := fresh "HBs" in let Hstep := fresh "Hstep" in
lazymatch type of HS with st_ok _ ?E ?ss ?ms => pose proof (st_ok_reg src0segs E ss ms 11 HS) as H11 end;
eval_sr_get_in H11;
rewrite denot_lit_U, U_add_off_atom in H11 by (evalE; unfold M64; lia);
rewrite !Z.add_0_r in H11;
lazymatch goal with |- rzb _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E _ _ =>
pose proof (runs_at_nth _ (ms_mem ms) _ si _ _ HR eq_refl) as HBs; cbn [nth_error runs_main app] in HBs;
assert (Hstep : RiscvSemantics.step src0segs (mkst (ms_regs ms) (Z_to_bv 64 0x16610) (ms_mem ms) (seg_rom src0segs))
= MachineOk (mkst (regupd (ms_regs ms) 12 (Z_to_bv 64 0)) (Z_to_bv 64 0x16614) (ms_mem ms) (seg_rom src0segs)));
[ rewrite (step_lbu src0segs _ (Z_to_bv 64 0x16610) _ (seg_rom src0segs) (Z_to_bv 32 0x5c603) 12 11 0 (Z_to_bv 8 0));
[ reflexivity
| apply fetch_lit; vm_compute; reflexivity
| vm_compute; reflexivity
| vm_refl_bv
| rewrite H11;
match goal with |- context [bv_signed ?i] => let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end;
rewrite v_addi_0;
lazymatch type of HBs with YP03.bytes_at _ ?a _ =>
replace (bv_unsigned (ew E n) + bv_unsigned (ew E k)) with (a + Z.of_nat (length s)) by (evalE; lia) end;
rewrite (str_reads _ _ s HBs (length s) ltac:(lia)), nth_middle; reflexivity ]
| sym_step_manual HS Hstep [(12%bv:reg, SLit 0)];
[ intros r Hr; apply getr_other; intros ->; vm_compute in Hr; discriminate Hr
| repeat constructor; cbn [fst snd sv_denot]; apply getr_same; intros Heq; discriminate Heq
| clear H11 HBs ] ]
end end.
Ltac fpf_memcpy_str HS HR HW si k kj s woff :=
let H10 := fresh "H10" in let H11 := fresh "H11" in let H12 := fresh "H12" in let Hra := fresh "Hra" in
let HBs := fresh "HBs" in let Hst := fresh "Hst" in let Hu0 := fresh "Hu0" in
reg_of HS (10%bv:reg) H10; reg_of HS (11%bv:reg) H11; reg_of HS (12%bv:reg) H12; reg_of HS (1%bv:reg) Hra;
lazymatch goal with |- rzb _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E ?ss _ =>
lazymatch type of HR with runs_at ?zsp _ _ =>
pose proof (runs_at_nth _ (ms_mem ms) _ si _ _ HR eq_refl) as HBs; cbn [nth_error runs_main app] in HBs;
lazymatch type of HBs with YP03.bytes_at _ ?a _ =>
assert (Hu0 : bv_unsigned (ew E 0) = zsp) by (evalE; reflexivity);
lazymatch type of H11 with _ = ?srcw =>
rewrite <- (Z_to_bv_bv_unsigned 64 srcw) in H11;
replace (bv_unsigned srcw) with a in H11 by (evalE; lia) end;
rewrite <- (Z_to_bv_bv_unsigned 64 (ew E k)) in H12;
replace (bv_unsigned (ew E k)) with (Z.of_nat (length s)) in H12 by (evalE; lia);
assert (Hst : store_ok src0segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (ew E 0) + woff)) (length s) = true)
by (apply (store_ok_of_win src0segs E _ _ _ _ _ HW); cbn [sv_denot]; rewrite !unsigned_lit_small by lia; lia);
let regs2 := fresh "regs" in let Hms := fresh "Hms" in let R10 := fresh "R10" in let Rfr := fresh "Rfr" in
destruct (src0_memcpy s _ _ _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms) H10 H11 H12
ltac:(rewrite unsigned_lit_small by lia; reflexivity)
(bytes_at_rdn src0segs _ _ _ (bytes_at_app_l _ _ _ _ HBs))
Hst
ltac:(rewrite unsigned_lit_small by lia; lia)
ltac:(rewrite unsigned_lit_small by lia; lia)
ltac:(left; rewrite !unsigned_lit_small by lia; lia))
as (regs2 & Hms & R10 & Rfr); clear Hst;
rewrite Hra in Hms; change (v_jalr (Z_to_bv 64 88248) 0) with (Z_to_bv 64 0x158b8) in Hms;
clear H10 H11 H12 Hra HBs;
sym_splice_havoc HS Hms kj (@nil (reg * sv)) junk_memcpy;
[ sym_splice_frame Rfr
| constructor
| fpf_mem_window HS
| clear Rfr R10;
lazymatch goal with |- rzb _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes ?m ?d ?bs =>
lazymatch type of HS with st_ok _ ?E' _ _ =>
apply (runs_at_wbytes_below _ _ _ d bs) in HR; [| rewrite unsigned_lit_small by lia; lia];
apply (win_ok_wbytes src0segs _ _ _ _ d bs) in HW;
replace d with (Z_to_bv 64 (zsp + woff)) in * by (f_equal; lia);
assert (HK : runs_ok E' (wbytes m (Z_to_bv 64 (zsp + woff)) bs) [(SOff 0 woff, SOff 0 (-480), zsp + woff, s)]);
[ apply runs_ok_single;
[ cbn [sv_denot]; evalE; lia
| cbn [sv_denot]; evalE; lia
| apply bytes_at_wbytes_same; lia ]
| clear Hu0 ]
end end end ]
end end end end.
Ltac fpf_memcpy_lit HS HR HW HK k kj lit lem woff :=
let H10 := fresh "H10" in let H11 := fresh "H11" in let H12 := fresh "H12" in let Hra := fresh "Hra" in
let Hsrc := fresh "Hsrc" in let Hst := fresh "Hst" in let Hu0 := fresh "Hu0" in let Huk := fresh "Huk" in
let Hlen := fresh "Hlen" in
lazymatch type of HS with st_ok _ ?E ?ss ?ms => pose proof (st_ok_reg src0segs E ss ms 10 HS) as H10 end;
eval_sr_get_in H10; rewrite denot_lit_U, U_add_off_atom in H10 by (evalE; unfold M64; lia);
reg_of HS (11%bv:reg) H11; reg_of HS (12%bv:reg) H12; reg_of HS (1%bv:reg) Hra;
lazymatch goal with |- rzb _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E ?ss _ =>
lazymatch type of HR with runs_at ?zsp _ _ =>
assert (Huk : bv_unsigned (ew E k) = Z.of_nat (length lit) - Z.of_nat (length lit) + (bv_unsigned (ew E k))) by lia;
clear Huk;
assert (Hu0 : bv_unsigned (ew E 0) = zsp) by (evalE; reflexivity);
assert (Hlen : Z.of_nat (length lit) = Z.of_nat (length lit)) by reflexivity;
let n := eval compute in (Z.of_nat (length lit)) in
change (Z.of_nat (length lit) = Z.of_nat (length lit)) with (Z.of_nat (length lit) = n) in Hlen;
lazymatch type of H11 with _ = Z_to_bv 64 ?srcaddr =>
eassert (Hsrc : rdn src0segs (ms_mem ms) (sv_denot E (SLit srcaddr)) (word_to_nat (sv_denot E (SLit n))) = Some _)
by (rdn_of_chunk HS);
cbn [sv_denot base_val] in Hsrc;
let wn := eval compute in (Z.to_nat n) in
change (word_to_nat (Z_to_bv 64 n)) with wn in Hsrc;
match type of Hsrc with _ = Some ?cb => replace cb with lit in Hsrc by (symmetry; apply (lem E)) end;
lazymatch type of H10 with _ = ?d =>
lazymatch type of HK with runs_ok _ _ [(_, _, _, ?s)] =>
assert (Hst : store_ok src0segs (ms_mem ms) d wn = true)
by (apply (store_ok_of_win src0segs E _ _ _ _ _ HW); cbn [sv_denot]; evalE; lia);
let regs3 := fresh "regs" in let Hms := fresh "Hms" in let R10 := fresh "R10" in let Rfr := fresh "Rfr" in
destruct (src0_memcpy lit _ _ _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms) H10 H11 H12
ltac:(rewrite unsigned_lit_small by lia; exact (eq_sym Hlen))
Hsrc Hst
ltac:(rewrite Hlen; evalE; lia)
ltac:(rewrite Hlen; evalE; lia)
ltac:(right; rewrite Hlen; evalE; lia))
as (regs3 & Hms & R10 & Rfr); clear Hst Hsrc;
rewrite Hra in Hms; change (v_jalr (Z_to_bv 64 88248) 0) with (Z_to_bv 64 0x158b8) in Hms;
clear H10 H11 H12 Hra;
sym_splice_havoc HS Hms kj (@nil (reg * sv)) junk_memcpy;
[ sym_splice_frame Rfr
| constructor
| lazymatch type of HS with st_ok _ ?E0 ?ss0 _ =>
let m := eval vm_compute in (ss_mem ss0) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
eapply (st_ok_mem_wbytes_inside src0segs E0 ss0 _ _ _ [r0] r1 rest);
[ exact HS | reflexivity | reflexivity | cbn [base_val r_base r_lo]; evalE; lia
| cbn [base_val r_base r_hi]; rewrite Hlen; evalE; lia ] end end
| clear Rfr R10;
lazymatch goal with |- rzb _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes ?m ?d2 ?bs =>
lazymatch type of HS with st_ok _ ?E' _ _ =>
apply (runs_at_wbytes_below _ _ _ d2 bs) in HR; [| rewrite Hlen; evalE; lia];
apply (win_ok_wbytes src0segs _ _ _ _ d2 bs) in HW;
apply runs_ok_single_inv in HK;
let HKb := fresh "HKb" in
destruct HK as (_ & _ & HKb);
apply (bytes_at_wbytes_out m (zsp + woff + Z.of_nat (length s)) bs) in HKb;
[| lia | rewrite Hlen; lia | lia | lia | left; lia ];
replace d2 with (Z_to_bv 64 (zsp + woff + Z.of_nat (length s))) in * by (f_equal; evalE; lia);
let HK' := fresh "HK'" in
pose proof (bytes_at_app _ _ _ _ HKb (bytes_at_wbytes_same m (zsp + woff + Z.of_nat (length s)) bs
ltac:(lia) ltac:(rewrite Hlen; lia))) as HK';
clear HKb;
assert (HK : runs_ok E' (wbytes m (Z_to_bv 64 (zsp + woff + Z.of_nat (length s))) bs)
[(SOff 0 woff, SOff 0 (-480), zsp + woff, s ++ bs)]);
[ apply runs_ok_single;
[ cbn [sv_denot]; evalE; lia
| rewrite length_app, Nat2Z.inj_add, Hlen; cbn [sv_denot]; evalE; lia
| exact HK' ]
| clear HK' Hu0 Hlen ]
end end end ]
end end end end end end.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Theorem wl0_sound_b : forall E ss ms model fd ch b off vb0 vl0 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 ->
U E (sr_get (ss_regs ss) 11) = base_val E b + off ->
iov_read1 (ss_mem ss) b off = Some (vb0, vl0) -> U E vl0 = 0 ->
base_val E b + off + 16 <= 2 ^ 47 -> U E vb0 <= 2 ^ 47 ->
(forall ms', st_ok src0segs E (resume ss (SLit 0) (ss_mem ss) (ss_facts ss)) ms' -> ms_mem ms' = ms_mem ms ->
rzb src0segs (mkCfg ms' model) T) ->
rzb src0segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd ch b off vb0 vl0 T Hh Hlz HS Hrv H17 H10 Hfdc H32 H12 H11 Hiov Hvl0 Hiok Hok0 Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hiov) as [M0 L0].
assert (Ha11 : getr regs 11 = Z_to_bv 64 (base_val E b + off)).
{ rewrite (Hregs 11%bv), denot_lit_U, H11. reflexivity. }
eapply (rzb_writev_empty src0segs regs _ mem (seg_rom src0segs) model fd ch (sv_denot E vb0) T Hh Hlz).
- rewrite (Hregs 17%bv), H17. reflexivity.
- exact Hfdc. - exact H32.
- rewrite (Hregs 10%bv). exact H10.
- rewrite (Hregs 12%bv). exact H12.
- apply ms_read_u64_of_rdn. rewrite Ha11. exact M0.
- apply ms_read_u64_of_rdn.
pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11, u_Z2bv by lia.
rewrite (denot_lit_U E vl0), Hvl0 in L0. exact L0.
- pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11. unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- pose proof (U_range E vb0) as R0. unfold M64 in R0.
rewrite (denot_lit_U E vb0). unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- apply Hk; [|reflexivity].
change (Z_to_bv 64 0) with (sv_denot E (SLit 0)).
apply st_ok_resume_sv; auto.
Qed.
End h.
Ltac wl_writev0 HS Hch :=
lazymatch type of HS with st_ok_ecall _ ?E ?ss ?ms =>
lazymatch goal with |- rzb _ (mkCfg _ ?model) _ =>
lazymatch type of Hch with fdchan ?fd ?ch _ =>
let r := eval vm_compute in (sr_get (ss_regs ss) 11) in
lazymatch r with
| SOff ?b ?off =>
let io := eval vm_compute in (iov_read1 (ss_mem ss) (Some b) off) in
lazymatch io with
| Some (?vb0, ?vl0) =>
eapply (wl0_sound_b E ss ms model fd ch (Some b) off vb0 vl0 _ ltac:(assumption) ltac:(assumption) HS);
[ reflexivity
| vm_compute; reflexivity
| eval_sr_get; rewrite denot_lit_U, U_SLit; reflexivity
| exact Hch
| reflexivity
| eval_sr_get; first [ rewrite denot_lit_U, U_SLit; reflexivity
| rewrite iovcnt_val, Z.eqb_refl; reflexivity
| rewrite iovcnt_val'', Z.eqb_refl; reflexivity
| rewrite denot_add0, iovcnt_val'', Z.eqb_refl; reflexivity   ]
| eval_sr_get; cbn [base_val]; apply U_off; evalE; unfold M64; lia
| vm_compute; reflexivity
| rewrite ?U_SLit; reflexivity
|   cbn [base_val]; first [ solve [evalE; unfold M64 in *; lia] | idtac ]
|   first [ solve [rewrite U_SLit, zcanon_id by (unfold M64; lia); lia] | solve [rewrite U_off by (evalE; unfold M64; lia); evalE; lia] | idtac ]
| clear HS;
let ms' := fresh "ms" in let Hmm := fresh "Hmm" in
intros ms' HS Hmm;
repeat match goal with
| HR : runs_at _ (ms_mem ms) _ |- _ => rewrite <- Hmm in HR
| HK : runs_ok _ (ms_mem ms) _ |- _ => rewrite <- Hmm in HK
| HW : win_ok _ _ (ms_mem ms) _ _ |- _ => rewrite <- Hmm in HW
end;
clear Hmm; try clear ms; sym_norm HS ]
| _ => fail "wl_writev0: iovec not found"
end
| _ => fail "wl_writev0: a1 is not an offset"
end
end end end.
