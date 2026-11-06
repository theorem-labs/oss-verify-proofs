(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK01.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p
YK15 YK0y YK1b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK00.
Unset Lia Cache. Unset Nia Cache.
Local Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Import ListNotations.
Open Scope bv_scope.
Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
(x8 : word) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Lemma step_ecall_epend : forall segs regs pc mem rom w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step segs (mkst regs pc mem rom)
= MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.
Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof. reflexivity. Qed.
Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_read_byte_epend : forall segs regs pc mem x8,
ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof. reflexivity. Qed.
Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof. reflexivity. Qed.
Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof. reflexivity. Qed.
Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof. reflexivity. Qed.
Lemma adv_set_epend : forall regs pc mem rom x8 v,
advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
= mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_set. Qed.
Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.
Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.
Lemma rz_sys : forall segs regs pc mem rom model w T,
m_halted model = None ->
m_vm_lazy model = [] ->
fetch_word segs pc = Some w -> is_ecall w = true ->
realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.
Lemma rz_write_chan : forall segs regs pc mem model fd ch n bs T,
m_halted model = None ->
m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 64%Z ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some (FdChannel ch) -> w_is0 ch = false ->
getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
(1 <= n)%nat -> (Z.of_nat n <= rw_bytes_max)%Z -> (Z.of_nat n < 2 ^ 64)%Z ->
rdn segs mem (getr regs 11) n = Some bs ->
(forall k, (1 <= k)%nat -> (k <= n)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) T) ->
realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
(t_write_ch ch bs T).
Proof.
intros segs regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hcnt Hn1 Hmax Hn64 Hrd Hc.
pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
eapply (rz_write_ch segs _ model fd ch (getr regs 17) bs T Hh Hlazy).
- unfold fdchan. split; [exact Hlk | exact Hch].
- apply fd32_id. exact Hfd32.
- reflexivity.
- exact Hno.
- rewrite ms_gpr_epend0. exact Hfd.
- rewrite ms_gpr_epend1, ms_gpr_epend2, Hcnt.
rewrite (ms_read_bytes_rdn segs) by reflexivity. cbn [ms_mem epend].
unfold word_to_nat. rewrite u64_lit by lia. rewrite Nat2Z.id. exact Hrd.
- unfold buf_modeled. rewrite Hlen. exact Hmax.
- rewrite Hlen. exact Hn1.
- intros k Hk1 Hk2. rewrite adv_set_epend.
replace (len_word (firstn k bs)) with (Z_to_bv 64 (Z.of_nat k)); [apply Hc; lia|].
unfold len_word. rewrite length_firstn, Hlen. f_equal. lia.
Qed.
Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma rz_exit_lit : forall segs regs pc mem rom model code,
m_halted model = None -> is_exit_no (getr regs 17) ->
getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model)
(t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros segs regs pc mem rom model code Hh Hx8 Ha0 Hc.
rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply rz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.
