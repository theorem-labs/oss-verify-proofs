(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BExec () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_ri7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec6msteps00c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec5mstepk7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec6msteps02c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec:msteps_indI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic3and00k7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec6msteps01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtI47Corelib4Init5Logic2ex00c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec<msteps_transc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_donec7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec7evt_cutI47Corelib4Init5Logic2eq00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition mstep (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

Lemma msteps_trans : forall a b c, msteps a b -> msteps b c -> msteps a c.
Proof.
ltac2:(KReplay.run1 (kr_t_BExec ()) ["WithSegs"] "h01Hh11ah21bh32msh42H0h58IHmstepsh61ch73ms1h83ms2p;2p;5p;6p10000p4p7210p1000\p4p710p8g001:j20Tg0028j23Tg0033j52Tg0041j61Tg0051R0f2R1f1R2'0R3f0R4f3R5'0f4R6,01[X20X101041P4UX301312f6R7,01f7R8,06[1058P7f5f8P5P2P4O1D2UW5X43W0X80X70X30P5P1P4E1W0X60X20W1o"). Qed.

Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', msteps ms ms' /\ Q ms'.

Lemma evt_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BExec ()) ["WithSegs"] "h01Hh11Qh22msh33ms'p;2p;1p;4g001:j20Tg0068j24Tg006Sj12Tg007Qj41Tg007lj43Tg0051R0p-0[f1R1f0R2O1P0f2R3/02f3P2O1'4X30P11011P3P1O1%21P2C1C3W0X20W1o"). Qed.

Lemma evt_step : forall Q ms ms1, mstep ms ms1 -> evt Q ms1 -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BExec ()) ["WithSegs"] "p'0h03ms'h12H0h21Hh32HQh42Hsh51Qh62msh73ms1i001xp;2p;5p;4g0028j26Tg008Fj22Tg001:j20Tg0068R0j21Tg0033j55Tg007Qj44Tg007lj43Tg0051R1p-0[f1R2f0R3'6f3R4/22g009?P11043f5R5P3O1'1X01f4R6,25P31053f7P3O1'1P0f6/02f8R0P2O1f9R7/20P31004f;R0P6O1P1f<R6/03f=P3O1'1X01P51005P6P5O1P0f:P5P7P2D5P3C4C3W3W4P2P3O2n2001000000120000000W1X01P2P3O2n2001000000120100000W1W2X71X61W5o"). Qed.

Lemma evt_cut : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> evt Q ms') -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BExec ()) ["WithSegs"] "p'0h03ms'h11Hh22H1h32H2h42HPh52HQh61Kh71Ph81Qh91eh:2msh;3ms1h<3ms2i001xp;2p;5p;4g008Fj21Tg001:j20Tg0068R0j22Tg009?R1j23Tg009Yj56Tg007Qj45Tg007lj44Tg0051R2p-0[R3f2R4f0R5'1P1P21045f4R4P5O1'2X02f5R6P5O1f1R7,16[^02f3R8,14[P51045f6R9P5O1'2P01067f7R:P7O1f9R;P5O111;7[^02f8R;/1:[P510:8f:R<P4O1f<R=P5O1R>11=7[^02P5P9P7O210:5/2>X02,32P1P210;5f=R;P5O1'2X0211;=P510<5f?R<P5O1'2P0f;R0/07f@R=P7O1fA/1=P510;8fCR;P4O1P2fDR4/05fEP5O1'2X02P610;6P4P6O1P;P<P6P0P7D6P5C5C4W5W3P7P5O2n2001000000120000000W1X<2P7P5O2n2001000000120100000b9W6W4W2P7P5O2n2001000000120000000W1X;2P7P5O2n2001000000120100000W1X:2X83W7o"). Qed.

Lemma evt_mono : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> Q ms') -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BExec ()) ["WithSegs"] "h03ms'h11Hh22HPh31Kh41Ph51Qh62msp;2p;3p;5g008Fj22Tg00:[j31Tg00;Yj50Tg0051R0p-0[R1f2R2f0R3'2f4R4P3O1P4f1R5O1[^00P4f3P2P5f5R4P3O1P2P5P3O29145W2X00D0W3W1X60X51W4o"). Qed.

Lemma evt_eq : forall Q ms ms', ms = ms' -> evt Q ms' -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BExec ()) ["WithSegs"] "h02msh11Qh23ms'p;3p;2p;6g00<Vj32Tg008Fj20Tg000\j61Tg0051R0p-0[f1R1f0R2520f3R3/01P0f2f5/02X00P2P3P1E1UUX20X00W1o"). Qed.

End WithSegs.

Arguments mstep segs ms ms' /.
