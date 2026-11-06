(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3g.v, with its module paths and addresses changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_pin/lib/Reusable/YN3g.v, with its module paths and module names changed; 12 of its 234 lines of code are new or changed and 231 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YH00 YN3f YN3g.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YO0d YH02 YK15_cfw YN3f_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem crz_sym_stdio_writev2 :
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
crealizes src0_msyms (mkCfg ms' model) T) ->
crealizes src0_msyms (mkCfg ms model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof using.
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
apply (wl_entry_pend_cf model Hh Hlz fd ch Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfd Hfdv)
with (c := 2) (b0 := U E vb0) (l0 := U E vl0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' Hkept H17' Hout Hst'.
apply (Hk (mkst regs' (Z_to_bv 64 0x15ec0) mem' (seg_rom src0segs)) (map (getr regs') WL_CLOB)).
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
Theorem crz_sym_stdio_writev1 :
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
crealizes src0_msyms (mkCfg ms' model) T) ->
crealizes src0_msyms (mkCfg ms model) (t_emit (map (WriteEv ch) bs1) T).
Proof using.
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
apply (wl_entry_pend_cf model Hh Hlz fd ch Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfd Hfdv)
with (c := 1) (b0 := 0) (l0 := 0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' Hkept H17' Hout Hst'.
apply (Hk (mkst regs' (Z_to_bv 64 0x15ec0) mem' (seg_rom src0segs)) (map (getr regs') WL_CLOB)).
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
End d.
