(* link's instance of lib/A/Rt/LinkMallocDepotW.v amalloc04_rule_dw (the malloc rule with the depot step for a call
   whose trace may be wild) at segs := tfibsegs (lib/A/AB1v.v), B := PcapB (lib/A/AD2l.v) and the trivial meter
   (YCbp.v ameter_triv), for every sink head SK, passed by name; built as lib/A/Rt/LinkMallocDepotA.v
   PcapB_AMALLOC4_D builds amalloc04_rule_d: PcapB_segs_low, PcapB_env, PcapB_LAWS, PcapB_ML and the malloc
   interceptor's realization (lib/A/AF0w.v pcap_amalloc_realizes), given to amalloc04_rule_dw_triv.
   Proves no function (kind: kit lemma, an instance). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YI16 YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AF0w PcapBFacts.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepotW.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Definition PcapB_AMALLOC4_DW : amalloc04_rule_dw (SK := SK) tfibsegs PcapB ameter_triv :=
  amalloc04_rule_dw_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML
    (pcap_amalloc_realizes rc fx).
End b.

About PcapB_AMALLOC4_DW.
Print Assumptions PcapB_AMALLOC4_DW.
