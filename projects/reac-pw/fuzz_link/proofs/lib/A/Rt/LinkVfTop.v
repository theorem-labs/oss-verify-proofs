(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the two top lemmas of the print path's memory-FILE
   calls, at the closed forms of LinkVfInst.v:
   - link_vfprintf_mf: vfprintf (f, fmt, ap) at the wrapper 0x4307c (j 0x46a7c, ___interceptor_vfprintf) on link's
     memory FILE, window LVF_STK = 0x30 + 5552;
   - link_fprintf_mf: fprintf (f, fmt, ...) at the wrapper 0x43084 (j 0x46e48, ___interceptor_fprintf), window
     LFP_STK = 0x70 + 5552.
   Each composes the runtime body's walk (LinkVfBody.v / LinkFpBody.v, at link's PcapB: AR_laws by YG0q.AR_laws_ok,
   PcapSyms by AD2l.PcapB_syms, printf_common by LinkSnpPort.link_pcommon) with musl vfprintf 0x973e0 on the memory
   FILE (LinkVfSeam.v, the GXA walk LinkVfMfA.v carried into the A engine), at the callers' relro bounds
   PCAP_RLO / PCAP_RHI. Also the forms for every relro bound pair. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkVfBody LinkFpBody LinkVfSeam.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* vfprintf at 0x4307c on the memory FILE, for every relro bound pair *)
Theorem link_vfprintf_mf_rel : forall rlo rhi,
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_STK LA_GOT_GUARD LA_GUARD LA_W_VFPRINTF.
Proof.
  intros rlo rhi.
  exact (proj2 (LinkVfBody.vfi_mf_ok_stk_PcapB rlo rhi (LinkVfSeam.link_vfprintf_mf_musl_PcapB fx rc rlo rhi))).
Qed.

(* fprintf at 0x43084 on the memory FILE, for every relro bound pair *)
Theorem link_fprintf_mf_rel : forall rlo rhi,
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD LA_W_FPRINTF.
Proof.
  intros rlo rhi.
  exact (proj2 (LinkFpBody.fpi_mf_ok_stk_PcapB rlo rhi (LinkVfSeam.link_vfprintf_mf_musl_PcapB fx rc rlo rhi))).
Qed.

(* the closed forms the callers cite (reac_code_emit 0x89d00 / 0x89d1c, reac_served_mark 0x89aec / 0x89b5c) *)
Theorem link_vfprintf_mf : link_avfprintf_contract.
Proof. exact (link_vfprintf_mf_rel PCAP_RLO PCAP_RHI). Qed.

Theorem link_fprintf_mf : link_afprintf_contract.
Proof. exact (link_fprintf_mf_rel PCAP_RLO PCAP_RHI). Qed.

End t.
