(* reac-pw/fuzz_link, image A: model_write and model_read at link's image-A instance, every Section hypothesis
   discharged, in the shape the slot's closing (lib/A/Prog/LLVMFuzzerTestOneInputClose.v) applies:
   `forall fy, @<f>_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB`.
   The image instance is LinkImgInst.v PI_link (pi_link_vals : LinkVals, pi_link_segs : pa_segs = tfibsegs); the
   rest is LinkWalkKernInst.v's *_aproof_pcapb (AR's laws by YG0q.AR_laws_ok, PALib by LinkPaLibInst.v PcapB_palib,
   PcapSyms by AD2l.PcapB_syms, every runtime callee by its owner's closed lemma, index_of and talk by their walks).

   Proves no function (kind: instance of model_write's and model_read's walks). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkAddr LinkPa
  LinkPaLib LinkWalk PcapRelro LinkImgInst model_write_c model_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LinkWalkKernInst.
Open Scope Z_scope.

Section inst. Context {rc : YM05.RunCeil}.

Theorem model_write_aproof_pcapb : forall fy : YK11.FPState,
  @model_write_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof.
intros fy.
pose proof (@LinkWalkKernInst.model_write_aproof_pcapb fy rc link_asink_head PI_link pi_link_vals pi_link_segs
  PCAP_RLO PCAP_RHI) as H.
rewrite pi_link_segs in H. exact H.
Qed.

Theorem model_read_aproof_pcapb : forall fy : YK11.FPState,
  @model_read_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof.
intros fy.
pose proof (@LinkWalkKernInst.model_read_aproof_pcapb fy rc link_asink_head PI_link pi_link_vals pi_link_segs
  PCAP_RLO PCAP_RHI) as H.
rewrite pi_link_segs in H. exact H.
Qed.
End inst.

Print Assumptions model_write_aproof_pcapb.
Print Assumptions model_read_aproof_pcapb.
