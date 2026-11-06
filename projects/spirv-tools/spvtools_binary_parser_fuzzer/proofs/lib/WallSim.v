(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SimInv ExitSim CatSim PropExec SeqExec CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_WallSim () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~i49OSSVerify5KrLib7WallSim7to_wall10C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k49OSSVerify5KrLib7WallSim7to_wall13C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6CatSim:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03c49OSSVerify5KrLib7WallSim;to_wallexitC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K49OSSVerify5KrLib6CatSim8to_wexit03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00K47Corelib4Init5Logic3and01I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat01C49OSSVerify5KrLib6CatSim?msteps_to_wexitC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib7WallSimCmsteps_to_wall_tailC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithSegsCh.
Context {fx : FPState}.
Variable segs : list Segment.
Variable fd ch : word.

Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithSegsCh"] "h02msh11Hh23ms'h32H0h42H1h52Hwh68IHmstepsh71kh84ms''h94restp;1p;3p;2p;7g0000j10Tg000Uj14Tg0013j12Tg001Vj15Tg0026j3>Tg002jj31Tg003`j1;Tg004Bj17Tg005Hj16Tg005jj33Tg006Dj18Tg007Lj29Tg008Hj2:Tg009Pj7=Tg00:Fj7<Tg00;<R0g00<C#0#0#0R1#4#2#5p-0\0p,4segsR2f3R3f2R43>R5P2f0R6f4R7;13f5R8=147[X20X00A1634P6W1X00%01#0#0#4#2R1#;%74%6133%8019231:0433f8R4f7R2513f9R1=184[A1714P2f6f:P1P7P3f1P6O1F=W5W6X45W3W1X80X20X00P7P3P6F<W1W7W9X20W0o"). Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithSegsCh"] "p'0h02Hwh13Hnbh25Hsteph34Hsvch43bufh54bufsh64codeh72msh83ms'h94resti001lp;1p;3p;2p;8p;7p;4g0000j10Tg000Uj1:Tg0013j17Tg001VR0j16Tg003`j1ETg004Bj1@Tg005Hj1?Tg005jj38Tg006Dj1>Tg007Lj2=Tg008Hj2<Tg00<hj31j22Tg00=`j1;Tg00>@j8DTg00?6j39Tg00?Vj1CTg00@5j25Tg00@Uj23Tg002jj34Tg009Pj7ATg00@oj4BTg00;<R1g00<C#0#0#0R2#:#7R3#6R4#6R5%02#0#0#:#7R2%E2f3R6#@%?238%>1p,4segsR2f4R7'=1<1638f2R8=167P0P4f0R0f6R9717f1R:f5R;f8R<31]0P7%;4R=?16;P2f7R2P9P=P7P6P8P0GDW0A94:0f9R=712g00AJg00Ae#CR21538'3f:R>12:<748A9468f<R871=P01537,32f=f;R=,2774;1539,32f?R212;8R8749P:P2f>P9P8P=P>P0FACBW0W1P:P0O2n2001000000120000000W0X95X44P:P0O2n10110000020020100100P0O1W0W2W3W6W5X81W7o"). Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithSegsCh"] "p'0h02Hwh13Hmsh23Hnbh33bufh44bufsh54codeh62msh73ms'h84resti001lp;1p;3p;7p;2p;6p;4g0000j11Tg000Uj19Tg0013j18Tg001VR0j16Tg0026j3?Tg00<hj30j22Tg00=`j1<Tg00BDj7;Tg00?6j37Tg00?Vj1:Tg00@5j24Tg00@Uj23Tg002jj35Tg00C?j6>Tg00@oj4=Tg00;<R1g00<C#1#1#1R2#9#8R3#6R4#6R5%12#1#1#9#8p,4segsR2f3R6f2R73?f1R8=076P0P4f0R0f5R9706f4R:f7R;508]0P6%<4R<?07:P2f6R2P9P<P6P7P0F;W0A7480f8R<702g00AJg00Ae#:R=1437'3f9128;757A7467f;R770<P0143:,3=f<f:R<,2:7591432,3=f>R=1297R7752P8P=f=P2P7P<P0E>C=W0W2P8P0O2n2001000000120000000W0X85X34P8P0O2n10110000020020100100P0O1W0W1W5W4X71W6o"). Qed.

Definition wall_won_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   fdchan fd ch (cfg_model c) /\
   exists bufs code rest,
     buf_modeled rest /\ bufs_modeled bufs /\
     to_wall_tail (cfg_ms c) rest (to_wallexit bufs code))
  \/ m_halted (cfg_model c) <> None.

End WithSegsCh.

Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

