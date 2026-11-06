(* reac-pw/fuzz_link, image A: the snprintf contract of lib/A/Rt/LinkSnpDef.v at LINK'S OWN INSTANCE, as one closed
   abbreviation the callers cite (a ruling of 2026-10-30): the walk of remember (the tail call at
   0x89ea8) and the slot of LLVMFuzzerTestOneInput (0x839c4 and 0x82b14) name `link_asnprintf_contract` and nothing
   else, so a change of the contract's premises is one edit here.

   Every argument is a named definition of link's tree:
   - segments: `tfibsegs` (lib/A/AB1v.v, Asan.M.loaded_segments);
   - asyms: `PcapB` (lib/A/AD2l.v);
   - the read-only window the walk invariant arodata_okP is stated over: `PCAP_RLO` / `PCAP_RHI`
     (lib/A/Prog/PcapRelro.v, 0xa1380 .. 0xa26c8; lib/A/Prog/PcapRelroA.v shows the window lies in one loaded
     segment of image A);
   - the entry: `LA_W_SNPRINTF` (lib/A/Rt/LinkMfDefs.v, 0x43088, the trampoline `j 0x46f20`);
   - the format family and the stack window are LinkSnpDef.v's `FF_link` (literal bytes, %d, %s, formats in
     [0x10000, 0xa2658)) and `LINK_SNP_STK` (2 * ESTACK = 8192), already fixed inside `asnprintf_link_realizes`.
   The FP state and the run ceiling stay implicit, as in every contract of this group: a caller gives its own.

   The contract itself (premises, the instruction that needs each, and the post) is LinkSnpDef.v's header.
   lk_asnprintf_realizes (lib/A/Rt/LinkSnDefs.v) is the donor's form with dest_off_globals and is NOT for
   link's callers: the call at 0x82b14 writes into the .bss object g_names, which that premise forbids.

   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkSnpDef.
Local Open Scope Z_scope.

Definition link_asnprintf_contract {fx : YK11.FPState} {rc : YM05.RunCeil} : Prop :=
  asnprintf_link_realizes tfibsegs PcapB PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
