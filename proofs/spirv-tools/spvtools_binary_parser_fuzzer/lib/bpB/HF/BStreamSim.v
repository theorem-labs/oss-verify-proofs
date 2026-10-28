(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSimInv BExitSim BCatSim BWallSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BStreamSim () := "C47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8flat_mapI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00i6ARocqVerifyHarness?AgentSubmission3bpB2HF:BStreamSim5to_wr00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k6ARocqVerifyHarness?AgentSubmission3bpB2HF:BStreamSim5to_wr02C6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim:msteps_indi6ARocqVerifyHarness?AgentSubmission3bpB2HF:BStreamSim5to_rd00k6ARocqVerifyHarness?AgentSubmission3bpB2HF:BStreamSim5to_rd02".

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma in_arg1_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof.
ltac2:(KReplay.run1 (kr_t_BStreamSim ()) [] "h02msh14segsh22x8p;1p;2p-1p10000p4p710p8g000Pj16Tg0010j10Tg001Uj12Tg0023j11Tg002Vj15Tg0035j24Tg0043j23Tg004M#6g005Lg006S#0#0#0#0#0#0#2#1R0f1g0078#5'4,30W2W0W1o"). Qed.

Definition M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  m_halted model = None /\
  m_vm_lazy model = [].

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
  map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

Definition iter_ev (bs : list byte) : list event :=
  iter_ev_ch (Z_to_bv 64 0) bs.

Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr : list event) : Prop :=
  exists blocks s',
    chunks cnt s blocks s' /\
    is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).

Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.

Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

Definition lh_next (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH ms'.

Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs lh_next.

Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

Definition ReadPend (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\

  access_okb buf (bv_unsigned cnt) = true /\
  to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z ->
     (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     to_wr bs (advance_past_svc (apply_effect ms
        (mkEffect (len_word bs) [(buf, bs)] [])))).

Lemma msteps_to_wr : forall bs ms ms',
  msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BStreamSim ()) ["Loop"] "h02msh11Hh23ms'h32H0h42H1h53Hwrh68IHmstepsh72bsh84ms''p;1p;3p;2p;6p;7p1007Wp4p70R0p1008Ep4p7210p8P0p1008ap4p710p8P0p1009Wp4p710p8P0p100:4p4p7210p8g0010j11Tg001Uj14Tg0023j13Tg000Pj16Tg00:Qj35Tg00;Mj20Tg00<Kj1<Tg00<mj1;Tg00>3j1:Tg00>Uj32Tg00>oj17Tg00@7j28Tg00A3j29Tg00B;j6>Tg00C9j7=Tg006S#1#1#1R0#4#3#6g005LR1p,4segsR2f1R3f0R435P2f5R5/04f6R6f2R7'0[X21X01f4R8/04P4W1X01%10#1#1#4#3R0#<%;7%:032%71f3R0,82191732A5207f9/00f:R2/05[1028f;f7P6P8P0P3P4O1E>W5W6W4W3W1X81X21X01P7P3P4F=W1X21W0W7o"). Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

Lemma msteps_to_rd : forall ms ms',
  msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BStreamSim ()) ["Loop"] "h02msh11Hh23ms'h32H0h42H1h53Hrdh68IHmstepsh74ms''p;3p;1p;2p;5p;7g00:Qj33Tg00D7j11Tg0010j10Tg001Uj14Tg0023j1=Tg00<Kj1;Tg00<mj1:Tg00>3j15Tg00>Uj32Tg00>oj16Tg00@7j27Tg00A3j28Tg00E5j59Tg00C9j7<Tg005LR0p,4segsR1f1R2f0R333P1%13R4f2R5#1[X20X00P3X14X00g006S#0#0#0#0#0#0#4#=R4#;%:5%5432%60f3R4,71180532A3145%14f5#1[f4R1#1f7f6P1P4P2P3O1D9W5W6W4W3W1X70X20X00P5P2P3F<W1X20W0o"). Qed.

Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

Definition sinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\
     (to_rd (cfg_ms c)
      \/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
           to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
  \/ on_path segs (Z_to_bv 64 0) c.

End Loop.

