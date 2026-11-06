(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil AsIface RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_HEmpStmt LbA_HRehStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_HEmpE LbA_HRehA LbA_HXmpE LbA_HXehA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_HEmp () := "C69OSSVerify5KrLib3bpA3Lib9LbA_HRehA9reh_specAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_HEmpE9emp_specAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_HXehA9reh_specAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_HXmpE9emp_specAC1?~~~~~~~~~~~~~~~".

Section Emp.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.

  Theorem emp_u32_okA : emp_stmt H EMP_U32.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_HEmp ()) ["Emp"] "p;3p;4g0000j31Tg0010j40Tp,5HCEILR0p,1HR1p,3HHBR2A1012C0o"). Qed.

  Theorem emp_ext_okA : emp_stmt H EMP_EXT.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_HEmp ()) ["Emp"] "p;3p;4g0020j31Tg0030j40Tp,5HCEILR0p,1HR1p,3HHBR2A1012C0o"). Qed.
End Emp.
