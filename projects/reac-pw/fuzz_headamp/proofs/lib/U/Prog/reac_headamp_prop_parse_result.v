(** reac_headamp_prop_parse_result (UBSan image, 0x14cd0, 297 instructions, 17 trap branches to the `unimp` at
    0x15170) against reac_headamp_prop_parse_result_contract (U/Prog/reac_headamp_prop_parse_result_c.v), with
    strtol_contract, strncmp_contract and strcmp_contract (U/Prog/strtol_c.v, strncmp_c.v, strcmp_c.v: the three
    callees, by contract) as premises.

    The walk is five segment files under U/Prog/Seg/, one cut statement each (U/Prog/Seg/ParseCut.v states the cuts;
    each file shows the trap branches of its range not taken): ParseEntry.v (0x14cd0: prologue, res zeroed, the
    NULL return, spa_pod_is_object_type, the find loop, spa_pod_is_struct, the walk setup), ParseWalk.v (0x14e18:
    SPA_POD_STRUCT_FOREACH by induction on its fuel, the key slot, strncmp against the prefix, the advance),
    ParseKey.v (0x14ed4: keys + 1, strtol and the '.' test, the three strcmp, the channel range), ParseValue.v
    (0x14f9c: value_pod_to_byte with reac_float_nearest inlined, value_in_range, the n >= max break, the cell store;
    0x150ec: the first refusal), ParseExit.v (0x15150: the res stores; 0x15108: the epilogue). Each proves its
    statement from the statements of the cuts it reaches; this file makes the call record of the contract's
    quantities and joins them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import
  reac_headamp_prop_parse_result_c strtol_c strncmp_c strcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import
  ParseCut ParseExit ParseValue ParseKey ParseWalk ParseEntry.

Theorem reac_headamp_prop_parse_result_holds :
  strtol_contract -> strncmp_contract -> strcmp_contract -> reac_headamp_prop_parse_result_contract.
Proof.
  intros HTOL HNCMP HCMP. unfold reac_headamp_prop_parse_result_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m null lo P O cap R bs ev can E0 E1 E2 E3 HARGS HSTK HLO HNOROM HFRM HMI.
  subst a0 a1 a2 a3.
  pose (c := PCtx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo P O cap R bs ev can).
  assert (HC : pc_ok c) by exact (conj HARGS (conj HSTK (conj HLO (conj HNOROM HMI)))).
  pose proof (px_epi c HC) as HEPI.
  pose proof (px_exit c HC HEPI) as HEXIT.
  pose proof (pv_refuse c HC) as HREF.
  pose proof (pv_value c HC HEXIT HREF) as HVAL.
  pose proof (pk_key HTOL HCMP c HC HVAL HREF) as HKEY.
  pose proof (pw_walk HNCMP c HC HEXIT HKEY) as HWALK.
  exact (pn_entry c HC HWALK HEPI null F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HFRM).
Qed.
