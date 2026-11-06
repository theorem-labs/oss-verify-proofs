(** The checking segment of reac-pw/fuzz_role's LLVMFuzzerTestOneInput (plain), [0x13f4c, 0x14158):
    role_check_contract (Prog/LLVMFuzzerTestOneInput_c.v) from the contracts of the callees it calls, by the walk of
    Prog/RoleCheck/Walk.v. The record is pod_build's of the input; the parse's answer on it agrees with expect_role's
    (Pod/Role.v parse_model_build), so no check aborts. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require memcpy_c reac_role_prop_parse_c strcmp_c pod_nearest_c
  check_absent_c check_role_c check_malformed_c reac_role_cfg_changes_c reac_role_cfg_apply_state_c check_answer_c
  reac_role_refuse_code_c check_code_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Spa Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleCheck Require Import Facts Walk.
Import ListNotations.
Open Scope Z_scope.

Theorem role_check_holds : memcpy_c.memcpy_contract -> reac_role_prop_parse_c.reac_role_prop_parse_contract ->
  strcmp_c.strcmp_contract -> pod_nearest_c.pod_nearest_contract -> check_absent_c.check_absent_contract ->
  check_role_c.check_role_contract -> check_malformed_c.check_malformed_contract ->
  reac_role_cfg_changes_c.reac_role_cfg_changes_contract ->
  reac_role_cfg_apply_state_c.reac_role_cfg_apply_state_contract -> check_answer_c.check_answer_contract ->
  reac_role_refuse_code_c.reac_role_refuse_code_contract -> check_code_c.check_code_contract -> role_check_contract.
Proof.
  intros MCPY PARSE STRC NEAR CKAB CKR CKM CHG APS CKA RFC CKC. unfold role_check_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m inp junk
    fl pp pod lo -> Hpod0 HPODA -> -> -> -> HFL H50 H80 HPPB HPC _ HSEP HPODLO HPPLO HST HLO HSPA HROM HF HMI HTM.
  set (r := fst (pod_build inp)) in *.
  assert (HB : pod_build inp = (r, snd (pod_build inp))) by apply surjective_pairing.
  pose proof (pod_build_wf inp r _ HB) as HWF.
  assert (HPM : corrupt r = false -> parse_model (buf r) = expect_model false r)
    by (intros Hc; exact (parse_model_build inp r _ HB Hc)).
  assert (HLEN : role_len inp = Z.of_nat (length (buf r))) by reflexivity.
  assert (HSEP' : or_h (pod + role_len inp <= pp) (pp + 19744 <= pod)) by exact HSEP.
  destruct (bytes_at_bound rsegs m pp _ HPPB) as [HPP0 _].
  destruct (rw_cells_bound rsegs m pod _ HPC) as [HP0 _].
  pose proof HST as (HLO0 & HSPT & _).
  unfold MID_STACK, FRAME_LOCALS, POD_PROPS, POD_LEN_OFF, POD_NENT_OFF in *.
  eapply head_ok with (r := r) (fl := fl) (lo := lo) (len := role_len inp) (junk := junk);
    first [ assumption | lia | (unfold role_len; lia) ].
Qed.
