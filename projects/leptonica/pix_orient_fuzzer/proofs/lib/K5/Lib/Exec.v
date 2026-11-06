(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Exec () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rc69OSSVerify5KrLib2K53Lib4Exec5mstepC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K53Lib4Exec6msteps01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K53Lib4Exec6msteps02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00i69OSSVerify5KrLib2K53Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib4Exec:msteps_indC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib2K53Lib4Exec<msteps_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition mstep (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

Lemma msteps_one : forall ms ms', mstep ms ms' -> msteps ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "h02msh13ms'p;2p;1p;5p10000p4p7210R0p1000\p4p710p8P0p10018p4p710p8P0p1001Vp4p7210p8P0p10023p4p710p8g002Qj22Tg003Gj11Tg004@j50Tg0059R0f1R1f0R2'2f2P1P1P2%11D0UX10W0o"). Qed.

Lemma msteps_trans : forall a b c, msteps a b -> msteps b c -> msteps a c.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "h01Hh11ah21bh32msh42H0h58IHmstepsh61ch73ms1h83ms2p;2p;5p;6g006@j20Tg002Qj23Tg004@j52Tg0079j61Tg0059R0f2R1f1R2'0R3f0R4f3R5'0f4R6,01[X20X101041P4UX301312f6R7,01f7R8,06[1058P7f5f8P5P2P4O1D2UW5X43W0X80X70X30P5P1P4E1W0X60X20W1o"). Qed.

(* [comment removed for export] *)
Lemma mstep_det : forall ms a b, mstep ms a -> mstep ms b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "p'0h01Hh12Hah22Hbh32_Hh43_H0h51ah61bh72msh81ti001mi016resultp;2p;1p;3p;4p;6g002Qj25Tg0084j11Tg008Yj18Tg0097j16Tg009Zj1>Tg00:<j14Tg00;Bj1;Tg00;dj30Tg00<>R0j17Tg00=Fj23Tg000\j49Tg0018j6:Tg001Vj6=Tg00>Bj2<Tg0059R1f0R2'<p=2f2R3f1R4'5g00?JR5g00?e#1#1#1#1#1#1#8#6R6#>R7f3R8#4%;6R630%71R9p,4segsR:/38%2330f4R;/53A01;8[P2f5R;#4=076f6R8,3:%2;509f7R3/5;P5f8R5#4=07613:5%28509A0153P2f:R5#4=076f;R6,3:f9#2509P9P1P0P1P1P2P2f<R0P0n1011000003101010000X89%26R6%25R5P9P613:0R0P5P9P0P6P;C9P2E:E=W2W4P4P2O2n2001000000120000000W0W1W3P4P2O2n2001000000120000000W0X61X51X71o"). Qed.

(* [comment removed for export] *)
Lemma mstep_not_svc : forall ms ms', mstep ms ms' -> ms_svc_pending ms = None.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "h01Hh12H0h22_Hh32msh43ms'p;2p;1p;3g002Qj2:Tg0084j10Tg008Yj17Tg0097j15Tg009Zj19Tg00:<j12Tg00;Bj18Tg00;dj31Tg00<>j16Tg00=Fj23Tg00>Bj24Tg0059R0f1R1f0R2':g00?Jg00?e#0#0#0#0#0#0#7#5R3#9R4f2R5#2%83R331%60R6p,4segsR7/35140131f3#2=143P2f4R5#2=143f5,371405516P1W2W0P1P2O2n2001000000120000000W1X40W3o"). Qed.

(* [comment removed for export] *)

Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', msteps ms ms' /\ Q ms'.

Lemma evt_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "h01Hh11Qh22msh33ms'p;2p;1p;4g006@j20Tg00?Jj24Tg003Gj12Tg00@Jj41Tg00@ej43Tg0059R0p-0[f1R1f0R2O1P0f2R3/02f3P2O1'4X30P11011P3P1O1%21P2C1C3W0X20W1o"). Qed.

Lemma evt_step : forall Q ms ms1, mstep ms ms1 -> evt Q ms1 -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "p'0h03ms'h12H0h21Hh32HQh42Hsh51Qh62msh73ms1i001xp;2p;5p;4g002Qj26Tg00A?j22Tg006@j20Tg00?JR0j21Tg004@j55Tg00@Jj44Tg00@ej43Tg0059R1p-0[f1R2f0R3'6f3R4/22g00B3P11043f5R5P3O1'1X01f4R6,25P31053f7P3O1'1P0f6/02f8R0P2O1f9R7/20P31004f;R0P6O1P1f<R6/03f=P3O1'1X01P51005P6P5O1P0f:P5P7P2D5P3C4C3W3W4P2P3O2n2001000000120000000W1X01P2P3O2n2001000000120100000W1W2X71X61W5o"). Qed.

(* [comment removed for export] *)
Lemma evt_cut : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> evt Q ms') -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "p'0h03ms'h11Hh22H1h32H2h42HPh52HQh61Kh71Ph81Qh91eh:2msh;3ms1h<3ms2i001xp;2p;5p;4g00A?j21Tg006@j20Tg00?JR0j22Tg00B3R1j23Tg00BMj56Tg00@Jj45Tg00@ej44Tg0059R2p-0[R3f2R4f0R5'1P1P21045f4R4P5O1'2X02f5R6P5O1f1R7,16[^02f3R8,14[P51045f6R9P5O1'2P01067f7R:P7O1f9R;P5O111;7[^02f8R;/1:[P510:8f:R<P4O1f<R=P5O1R>11=7[^02P5P9P7O210:5/2>X02,32P1P210;5f=R;P5O1'2X0211;=P510<5f?R<P5O1'2P0f;R0/07f@R=P7O1fA/1=P510;8fCR;P4O1P2fDR4/05fEP5O1'2X02P610;6P4P6O1P;P<P6P0P7D6P5C5C4W5W3P7P5O2n2001000000120000000W1X<2P7P5O2n2001000000120100000b9W6W4W2P7P5O2n2001000000120000000W1X;2P7P5O2n2001000000120100000W1X:2X83W7o"). Qed.

Lemma evt_mono : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> Q ms') -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "h03ms'h11Hh22HPh31Kh41Ph51Qh62msp;2p;3p;5g00A?j22Tg00CJj31Tg00DCj50Tg0059R0p-0[R1f2R2f0R3'2f4R4P3O1P4f1R5O1[^00P4f3P2P5f5R4P3O1P2P5P3O29145W2X00D0W3W1X60X51W4o"). Qed.

(* [comment removed for export] *)
Lemma evt_eq : forall Q ms ms', ms = ms' -> evt Q ms' -> evt Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Exec ()) ["WithSegs"] "h02msh11Qh23ms'p;3p;2p;6g00;dj32Tg00A?j20Tg0023j61Tg0059R0p-0[f1R1f0R2520f3R3/01P0f2f5/02X00P2P3P1E1UUX20X00W1o"). Qed.

End WithSegs.

Arguments mstep segs ms ms' /.
