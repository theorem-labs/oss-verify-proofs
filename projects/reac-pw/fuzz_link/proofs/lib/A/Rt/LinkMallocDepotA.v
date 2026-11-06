(* link's instances of lib/A/Rt/LinkMallocDepot.v amalloc04_rule_d, afree04_rule_d and afree_null04_rule_d (the
   allocator rules with the depot step of the call's trace) at segs := tfibsegs (lib/A/AB1v.v), B := PcapB
   (lib/A/AD2l.v) and the trivial meter (YCbp.v ameter_triv), for every sink head SK, passed by name. Built as
   lib/A/PcapBFacts.v PcapB_AMALLOC4 / PcapB_AFREE4 / PcapB_AFREEN4 build the frame rules there: the same
   PcapB_segs_low, PcapB_env, PcapB_LAWS, PcapB_ML and the interceptors' realizations (lib/A/AF0w.v
   pcap_amalloc_realizes, lib/A/AF0q.v pcap_afree_realizes), given to LinkMallocDepot.v's *_d_triv lemmas. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YI16 YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AF0w AF0q PcapBFacts.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Definition PcapB_AMALLOC4_D : amalloc04_rule_d (SK := SK) tfibsegs PcapB ameter_triv :=
  amalloc04_rule_d_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML (pcap_amalloc_realizes rc fx).
Definition PcapB_AFREE4_D : afree04_rule_d (SK := SK) tfibsegs PcapB ameter_triv :=
  afree04_rule_d_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML (pcap_afree_realizes rc fx).
Definition PcapB_AFREE_NULL4_D : afree_null04_rule_d (SK := SK) tfibsegs PcapB ameter_triv :=
  afree_null04_rule_d_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML (pcap_afree_realizes rc fx).
End b.

About PcapB_AMALLOC4_D.
Print Assumptions PcapB_AMALLOC4_D.
About PcapB_AFREE4_D.
Print Assumptions PcapB_AFREE4_D.
About PcapB_AFREE_NULL4_D.
Print Assumptions PcapB_AFREE_NULL4_D.
