(* on_data_cgW: Theorem transport_on_data_cg_holds : the statement transport_on_data_cg_holds_stmt of
   lib/A/Prog/on_data_cg.v, the image-A walk of on_data (fuzz_transport.asan 0x888d0, 1592 bytes), from the contract
   at the entry that the nine pieces give (lib/A/Prog/on_data_segs.v od_top, over the cuts of
   lib/A/Prog/on_data_seg_cut.v). od_holds_of_top reads the statement's premises as the cuts' record facts (od_laws:
   gx_ok and gx_noerrno of G from DgnTransportCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno), callee contracts
   (od_callees) and caller's facts (od_pre and trans_tf_off_g TF). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_data_seg_cut on_data_segs.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Lemma od_holds_of_top : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @od_top_at fx rc B MT -> @transport_on_data_cg_holds_stmt fx rc B MT.
Proof.
intros fx rc B MT TOP HPCS HCELLS HOC HGU HGNE HROU HRNE LAWS MTL MTF SMP ASF FFL ASM SC KA AI NT.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hnow HDF Htw Hfn Hm HTF HTFG HROM HAP HI1 HI4 HI3 Hcnt Hev.
refine (TOP _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' _ HTFG).
- exact (conj HPCS (conj HCELLS (conj HOC (conj HGU (conj HGNE (conj HROU (conj HRNE (conj LAWS (conj MTL
    (conj MTF (conj SMP (conj ASF (conj FFL (conj (G_HARNESS_gx_ok B HGU) (G_HARNESS_gx_noerrno B HGNE))))))))))))))).
- exact (conj ASM (conj SC (conj KA (conj AI NT)))).
- exact (conj HJ (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj Hsp16 (conj Hlo
    (conj Hhi (conj Hnow (conj HDF (conj Htw (conj Hfn (conj Hm (conj HTF (conj HROM (conj HAP (conj HI1 (conj HI4
    (conj HI3 (conj Hcnt Hev))))))))))))))))))))))).
Qed.

Theorem transport_on_data_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_on_data_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (od_holds_of_top fx rc B MT (od_top fx rc B MT)). Qed.

About transport_on_data_cg_holds.
Print Assumptions transport_on_data_cg_holds.
