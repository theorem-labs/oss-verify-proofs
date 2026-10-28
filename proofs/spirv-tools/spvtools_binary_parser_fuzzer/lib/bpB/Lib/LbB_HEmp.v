(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BsIface RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_HEmpStmt LbB_HRehStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HEmpE LbB_HRehA LbB_HXmpE LbB_HXehA.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HEmp () := "C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehA9reh_specAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpE9emp_specAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXehA9reh_specAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HXmpE9emp_specA".

Section Emp.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.

  Theorem emp_u32_okA : emp_stmt H EMP_U32.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmp ()) ["Emp"] "p;3p;4g0000j31Tg0010j40Tp,5HCEILR0p,1HR1p,3HHBR2A1012C0o"). Qed.

  Theorem emp_ext_okA : emp_stmt H EMP_EXT.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HEmp ()) ["Emp"] "p;3p;4g0020j31Tg0030j40Tp,5HCEILR0p,1HR1p,3HHBR2A1012C0o"). Qed.
End Emp.
