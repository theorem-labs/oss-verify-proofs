(* The strcspn contract of lib/A/Rt/RtString.v (astrcspn_realizes, window 2 * ESTACK) at PC_strcspn = 0x4514c, the
   one-instruction trampoline `j 0x46c98` of ___interceptor_strcspn. The two halves meet at the contract of musl's
   strcspn (RtSStrcspnDef.amcspn_realizes, entry 0x9f2b4, window 80 + 16 + ESTACK):
   - the interceptor half, RtSStrcspnIW.cmd_strcspn_icpt, walks the interceptor from its trampoline to its return
     and takes musl's strcspn at its REAL call (sp0 - 2160, return address 0x46cf0);
   - the musl half, RtSStrcspnM.cmd_mcspn, is fuzz_command's released plain walk of musl strcspn 0x9f2b4 and
     strchrnul 0x9f0b4 (lib/Prog/strcspn.v, lib/R_strchr.v) moved to this image and lifted into the SRr form; it
     calls the strlen interceptor under RtSStrlen.cmd_strlen and the memset interceptor 0x57628 under
     aintrin_realizes OSet.
   The memset interceptor's contract is the core's relocation of cgif's memset walk (lib/A/AE32.v
   memset_icpt_realizes), read in the aintrin_realizes OSet form as lib/A/AD1o.v oset_of_icpt reads it: the two
   statements differ only in where amem_range stands among the premises. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI RtSStrcspnDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtSStrcspnIW RtSStrcspnM.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the memset interceptor 0x57628 in the aintrin_realizes OSet form (as A/AD1o.v oset_of_icpt) *)
Lemma cspn_oset : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B -> aintrin_realizes tfibsegs B OSet 0x57628.
Proof.
intros B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE32.memset_icpt_realizes B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Theorem cmd_strcspn : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B ->
astrcspn_realizes tfibsegs B PC_strcspn A_SSP_GOT A_SSP_GUARD.
Proof.
intros B LAWS TB.
exact (RtSStrcspnIW.cmd_strcspn_icpt B LAWS TB (RtSStrcspnM.cmd_mcspn B LAWS TB (cspn_oset B LAWS TB))).
Qed.

End c.
