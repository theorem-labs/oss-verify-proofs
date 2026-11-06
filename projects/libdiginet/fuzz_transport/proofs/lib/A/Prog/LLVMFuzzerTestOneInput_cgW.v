(* LLVMFuzzerTestOneInput_cgW: the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput, composed.
   transport_LLVMFuzzerTestOneInput_cg_holds proves transport_LLVMFuzzerTestOneInput_cg_holds_stmt of
   lib/A/Prog/LLVMFuzzerTestOneInput_cg.v, generic in {rc} B MT XL RLO RHI, as LLVMFuzzerTestOneInput_segs.v
   llvmf_of_segments applied to the record lc_segments of the 32 segment lemmas. Each segment lemma takes the kit
   lemmas it uses (segs.v section 8: K1 lc_rom_view_ok, K2 lc_src_ro_ok, K3 lc_strlen_facts_ok, K4 lc_pro_agree_ok,
   K5 lc_dn_each_ok, K6 lc_runinv_ok, K7 lc_chain_ok) as arguments, in K order; K2 and K3 take K1. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
(* the kit lemmas K1 .. K7 *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  LLVMFuzzerTestOneInput_kit_rom_view LLVMFuzzerTestOneInput_kit_src_ro LLVMFuzzerTestOneInput_kit_strlen_facts
  LLVMFuzzerTestOneInput_kit_pro_agree LLVMFuzzerTestOneInput_kit_dn_each LLVMFuzzerTestOneInput_kit_runinv
  LLVMFuzzerTestOneInput_kit_chain.
(* the segment lemmas *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  LLVMFuzzerTestOneInput_seg_entry LLVMFuzzerTestOneInput_seg_hdr LLVMFuzzerTestOneInput_seg_cfg
  LLVMFuzzerTestOneInput_seg_minit
  LLVMFuzzerTestOneInput_seg_pre LLVMFuzzerTestOneInput_seg_head
  LLVMFuzzerTestOneInput_seg_op0 LLVMFuzzerTestOneInput_seg_op8 LLVMFuzzerTestOneInput_seg_recv
  LLVMFuzzerTestOneInput_seg_op1 LLVMFuzzerTestOneInput_seg_bar1
  LLVMFuzzerTestOneInput_seg_op2a LLVMFuzzerTestOneInput_seg_op2b LLVMFuzzerTestOneInput_seg_bar2
  LLVMFuzzerTestOneInput_seg_op3a LLVMFuzzerTestOneInput_seg_op3b
  LLVMFuzzerTestOneInput_seg_op4a LLVMFuzzerTestOneInput_seg_op4r LLVMFuzzerTestOneInput_seg_op4t
  LLVMFuzzerTestOneInput_seg_op4sys
  LLVMFuzzerTestOneInput_seg_op4coal LLVMFuzzerTestOneInput_seg_op4find LLVMFuzzerTestOneInput_seg_op4sub
  LLVMFuzzerTestOneInput_seg_op4st LLVMFuzzerTestOneInput_seg_op4s LLVMFuzzerTestOneInput_seg_op5
  LLVMFuzzerTestOneInput_seg_op6a LLVMFuzzerTestOneInput_seg_op6b LLVMFuzzerTestOneInput_seg_set56
  LLVMFuzzerTestOneInput_seg_op7 LLVMFuzzerTestOneInput_seg_tail LLVMFuzzerTestOneInput_seg_exit.
Open Scope Z_scope.

Section holds. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem transport_LLVMFuzzerTestOneInput_cg_holds : @transport_LLVMFuzzerTestOneInput_cg_holds_stmt rc B MT XL RLO RHI.
Proof.
pose proof (@LLVMFuzzerTestOneInput_kit_rom_view.lc_rom_view_ok rc B MT XL RLO RHI) as K1.
pose proof (@LLVMFuzzerTestOneInput_kit_src_ro.lc_src_ro_ok rc B MT XL RLO RHI K1) as K2.
pose proof (@LLVMFuzzerTestOneInput_kit_strlen_facts.lc_strlen_facts_ok rc B MT XL RLO RHI K1) as K3.
pose proof LLVMFuzzerTestOneInput_kit_pro_agree.lc_pro_agree_ok as K4.
pose proof LLVMFuzzerTestOneInput_kit_dn_each.lc_dn_each_ok as K5.
pose proof LLVMFuzzerTestOneInput_kit_runinv.lc_runinv_ok as K6.
pose proof (@LLVMFuzzerTestOneInput_kit_chain.lc_chain_ok rc B MT XL RLO RHI) as K7.
apply llvmf_of_segments.
exact {|
  sg_entry := @LLVMFuzzerTestOneInput_seg_entry.lc_entry_ok rc B MT XL RLO RHI;
  sg_hdr := @LLVMFuzzerTestOneInput_seg_hdr.lc_hdr_ok rc B MT XL RLO RHI K1;
  sg_cfg := @LLVMFuzzerTestOneInput_seg_cfg.lc_cfg_ok rc B MT XL RLO RHI K1 K2;
  sg_minit := @LLVMFuzzerTestOneInput_seg_minit.lc_minit_ok rc B MT XL RLO RHI K1;
  sg_pre := @LLVMFuzzerTestOneInput_seg_pre.lc_pre_ok rc B MT XL RLO RHI K4;
  sg_head := @LLVMFuzzerTestOneInput_seg_head.lc_head_ok rc B MT XL RLO RHI K1;
  sg_op0 := @LLVMFuzzerTestOneInput_seg_op0.lc_op0_ok rc B MT XL RLO RHI;
  sg_op8 := @LLVMFuzzerTestOneInput_seg_op8.lc_op8_ok rc B MT XL RLO RHI;
  sg_recv := @LLVMFuzzerTestOneInput_seg_recv.lc_recv_ok rc B MT XL RLO RHI K1 K5 K6 K7;
  sg_op1 := @LLVMFuzzerTestOneInput_seg_op1.lc_op1_ok rc B MT XL RLO RHI K1;
  sg_bar1 := @LLVMFuzzerTestOneInput_seg_bar1.lc_bar1_ok rc B MT XL RLO RHI K1 K2 K5 K6 K7;
  sg_op2a := @LLVMFuzzerTestOneInput_seg_op2a.lc_op2a_ok rc B MT XL RLO RHI;
  sg_op2b := @LLVMFuzzerTestOneInput_seg_op2b.lc_op2b_ok rc B MT XL RLO RHI K1 K2 K3;
  sg_bar2 := @LLVMFuzzerTestOneInput_seg_bar2.lc_bar2_ok rc B MT XL RLO RHI K1 K2 K5 K6 K7;
  sg_op3a := @LLVMFuzzerTestOneInput_seg_op3a.lc_op3a_ok rc B MT XL RLO RHI K1;
  sg_op3b := @LLVMFuzzerTestOneInput_seg_op3b.lc_op3b_ok rc B MT XL RLO RHI K1 K6;
  sg_op4a := @LLVMFuzzerTestOneInput_seg_op4a.lc_op4a_ok rc B MT XL RLO RHI;
  sg_op4r := @LLVMFuzzerTestOneInput_seg_op4r.lc_op4r_ok rc B MT XL RLO RHI;
  sg_op4t := @LLVMFuzzerTestOneInput_seg_op4t.lc_op4t_ok rc B MT XL RLO RHI K1;
  sg_op4sys := @LLVMFuzzerTestOneInput_seg_op4sys.lc_op4sys_ok rc B MT XL RLO RHI;
  sg_op4coal := @LLVMFuzzerTestOneInput_seg_op4coal.lc_op4coal_ok rc B MT XL RLO RHI;
  sg_op4find := @LLVMFuzzerTestOneInput_seg_op4find.lc_op4find_ok rc B MT XL RLO RHI;
  sg_op4sub := @LLVMFuzzerTestOneInput_seg_op4sub.lc_op4sub_ok rc B MT XL RLO RHI;
  sg_op4st := @LLVMFuzzerTestOneInput_seg_op4st.lc_op4st_ok rc B MT XL RLO RHI;
  sg_op4s := @LLVMFuzzerTestOneInput_seg_op4s.lc_op4s_ok rc B MT XL RLO RHI;
  sg_op5 := @LLVMFuzzerTestOneInput_seg_op5.lc_op5_ok rc B MT XL RLO RHI K1 K6;
  sg_op6a := @LLVMFuzzerTestOneInput_seg_op6a.lc_op6a_ok rc B MT XL RLO RHI;
  sg_op6b := @LLVMFuzzerTestOneInput_seg_op6b.lc_op6b_ok rc B MT XL RLO RHI K1 K6;
  sg_set56 := @LLVMFuzzerTestOneInput_seg_set56.lc_set56_ok rc B MT XL RLO RHI K6;
  sg_op7 := @LLVMFuzzerTestOneInput_seg_op7.lc_op7_ok rc B MT XL RLO RHI;
  sg_tail := @LLVMFuzzerTestOneInput_seg_tail.lc_tail_ok rc B MT XL RLO RHI;
  sg_exit := @LLVMFuzzerTestOneInput_seg_exit.lc_exit_ok rc B MT XL RLO RHI |}.
Qed.

End holds.
