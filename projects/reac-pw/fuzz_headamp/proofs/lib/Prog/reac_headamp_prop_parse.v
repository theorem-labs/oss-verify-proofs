(** reac_headamp_prop_parse (plain image, 0x14874, 2 instructions) against reac_headamp_prop_parse_contract
    (Prog/reac_headamp_prop_parse_c.v):
      0x14874 `mv a3,zero`; 0x14878 `j 0x1487c` (reac_headamp_prop_parse_result).
    A tail jump with res = NULL and ra kept: from 0x1487c the state is reac_headamp_prop_parse_result_contract's at
    R = 0, whose parse_args is this contract's premise, and whose post is this contract's post (parse_post at R = 0).
    So the walk is the two steps and that contract ([reac_headamp_prop_parse_of_result]); the closed result takes the
    three callee contracts of Prog/reac_headamp_prop_parse_result.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import
  reac_headamp_prop_parse_result_c reac_headamp_prop_parse_c strtol_c strncmp_c strcmp_c
  reac_headamp_prop_parse_result.
Import ListNotations.
Open Scope Z_scope.

Lemma reac_headamp_prop_parse_of_result :
  reac_headamp_prop_parse_result_contract -> reac_headamp_prop_parse_contract.
Proof.
  intros HR. unfold reac_headamp_prop_parse_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m null lo P O cap bs ev can E0 E1 E2 HARGS HSTK HLO HNOROM HFRM HMI.
  unfold HA_PARSE.
  step. (* 0x14874 mv a3,zero *)
  step. (* 0x14878 j 0x1487c *)
  exact (HR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m null lo P O cap 0 bs ev can E0 E1 E2 eq_refl HARGS HSTK HLO HNOROM HFRM HMI).
Qed.

Theorem reac_headamp_prop_parse_holds :
  strtol_contract -> strncmp_contract -> strcmp_contract -> reac_headamp_prop_parse_contract.
Proof.
  intros HTOL HNCMP HCMP.
  exact (reac_headamp_prop_parse_of_result (reac_headamp_prop_parse_result_holds HTOL HNCMP HCMP)).
Qed.
