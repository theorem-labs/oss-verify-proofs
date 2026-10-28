(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSimInv BExitSim BPropExec BCatSim BCatExec BSeqExec BStreamExec BWallSim BStreamSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BDrainSim () := "C47Corelib4Init9Datatypes3appc6ARocqVerifyHarness?AgentSubmission3bpB2HF9BDrainSim8out_tailc6ARocqVerifyHarness?AgentSubmission3bpB2HF9BDrainSim5procsC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC46Stdlib5Lists4List8flat_mapI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00i6ARocqVerifyHarness?AgentSubmission3bpB2HF9BDrainSim5to_rd00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k6ARocqVerifyHarness?AgentSubmission3bpB2HF9BDrainSim5to_rd02C6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim:msteps_indI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4list00i6ARocqVerifyHarness?AgentSubmission3bpB2HF9BDrainSim6to_out00k6ARocqVerifyHarness?AgentSubmission3bpB2HF9BDrainSim6to_out03".

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

End Proc.

Definition block_ok (cnt : word) (bs : list byte) : Prop :=
  (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
  flat_map (fun bs => map (ReadEv rch) bs) blocks.

Definition reads (blocks : list (list byte)) : list event :=
  reads_ch (Z_to_bv 64 0) blocks.

Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.

Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

Definition drain_from_ch (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  (exists blocks s' a',
     chunks cnt s blocks s' /\
     procs f a (concat blocks) = Some a' /\
     is_prefix tr (reads_ch rch blocks ++ out_tail s' a' fs))
  \/ (exists blocks bs s' a',
     chunks cnt s (blocks ++ [bs]) s' /\
     procs f a (concat blocks) = Some a' /\
     procs f a' bs = None /\
     is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [ExitEv ec fs])).

Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  drain_from_ch (Z_to_bv 64 0) a fs s tr.

End Traces.

Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.

Definition lh_next (a : A) (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH a ms'.

Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

Definition ReadPend (a : A) (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
             = Some w) /\

  access_okb buf (bv_unsigned cnt) = true /\
  to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\

  buf_modeled (out a) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     match procs f a bs with
     | Some a' => lh_next a'
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     | None => to_exit segs ec
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     end).

Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

Lemma msteps_to_rd : forall a ms ms',
  msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BDrainSim ()) ["Drain"] "h02msh11Hh23ms'h32H0h42H1h53Hrdh68IHmstepsh71ah84ms''p;3p;2p;1p;6p;7p-1p10000p4p710R0p8p1000Mp6061000p1001Kp6061000R1p8p1002Fp4p70R2p10034p4p7210p8P2p1003Pp4p710p8P2P0p8P2p1004Fp4p7210p8p,1AR2p4p300P1p8g004cj33Tg005_j20Tg006\j11Tg007Aj14Tg007_j1=Tg008Bj1;Tg008dj1:Tg009jj15Tg00:Lj32Tg00:fj16Tg00;nj27Tg00<jj28Tg00>2j69Tg00>oj7<Tg00?mR1p,4segsR0f1R3f0R433P0f5R5/04f6R6f2R7'0[X21X01f4R8/04P4W1X01g00A4#1#1#1#1#1#1#4#=R9#;%:7%5932%61f3R9,70181732A3097f9/09f:R0/05[1008f;f7P6P8P9P3P4O1E9W5W6W4W3W1X81X21X01P7P3P4F<W1X21W0X72o"). Qed.

Lemma msteps_to_out : forall bs ms ms',
  msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BDrainSim ()) ["Drain"] "h02msh11Hh23ms'h32H0h42H1h52Hoh68IHmstepsh72bsh84ms''p;1p;3p;2p;6p;7g006\j11Tg007Aj14Tg007_j13Tg00AYj16Tg004cj35Tg00B9j20Tg008Bj1<Tg008dj1;Tg009jj1:Tg00:Lj32Tg00:fj17Tg00;nj28Tg00<jj29Tg00C7j6>Tg00>oj7=Tg00A4#1#1#1R0#4#3#6g00?mR1p,4segsR2f1R3f0R435P2f5R5/04f6R6f2R7'0[X21X01f4R8/04P4W1X01%10#1#1#4#3R0#<%;7%:032%71f3R0,82191732A5207f9/00f:R2/05[1028f;f7P6P8P0P3P4O1E>W5W6W4W3W1X81X21X01P7P3P4F=W1X21W0W7o"). Qed.

Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

Definition dinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
  \/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
      m_vm_lazy (cfg_model c) = [] /\
      exists rest, buf_modeled rest /\
        to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
          (to_exit segs (Z_to_bv 64 0)))
  \/ on_path segs (Z_to_bv 64 0) c
  \/ on_path segs ec c.

End Drain.

