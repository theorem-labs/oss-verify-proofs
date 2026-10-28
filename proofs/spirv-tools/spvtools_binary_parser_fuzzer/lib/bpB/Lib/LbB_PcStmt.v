(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own LbB_DiagStmt LbB_DStat LbB_DRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PcStmt () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4list00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblI6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep6ds_inv00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep6ds_blkC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7app_objC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep7sb_addrI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DRep8ds_repA0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PcStmt8ds_rep_wC47Corelib4Init5Logic3iffI47Corelib7Numbers7BinNums1Z00C4ARocqVerifyHarness?AgentSubmission8LibIface3memI5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4sbuf00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7DS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegs".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition APAD : Z := 0xf5f34.
Definition AXSP : Z := 0x124a88.
Definition AOVF : Z := 0x125ed0.

Definition OVF_STACK : Z := 80 + 64 + AOPNEW_STACK.
Definition XSP_STACK : Z := 64 + OVF_STACK.
Definition PAD_STACK : Z := 208 + AFS_STACK + XSP_STACK.

Definition blkof (ms : sbuf) : Z := match ms with SShort => 0 | SLong _ asz => asz end.

Definition sbx (ms : sbuf) : list (Z * Z) :=
  match ms with SShort => [] | SLong d asz => [(d, d + asz); (sh d, sh d + nsh asz)] end.

Definition dsdata (ds : Z) (ms : sbuf) : Z := str_data (ds + 72) ms.

Definition ds_rep_w (LB : list block) (m : mem) (ds err len : Z) (DB : list block) (ms : sbuf) (pp hm fl fill : Z) : Prop :=
  ds_inv (lbl LB) m ds err len (lbl DB) ms pp hm fl fill /\ ds_blk LB DB ms
  /\ addressable m ds DS_SIZE /\ wr_at asegs m ds DS_SIZE /\ app_obj ds DS_SIZE /\ sb_addr m ms.

Lemma ds_repA0_w : forall LB m ds err len DB,
  ds_repA0 LB m ds err len DB <-> exists ms pp hm fl fill, ds_rep_w LB m ds err len DB ms pp hm fl fill.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PcStmt ()) [] "h04fillh12flh22hmh31mh42msh52pph61Hh72DBh82LBh92dsh:3errh;3lenp;1p;;p;3p;4p;2p;6g0000R0p4p70R1p1000ip4p710p8P1p1001Tp4p710p8P1p10024p4p710p8g002Qj1?Tg0031j14Tg003jl;7Tg004hj35Tg005dj3:Tg006dj49Tg007^j28Tg008_j26Tg009\j22Tg00:7j21Tg00:Qj4;Tg00:lj6>Tg00;jl;=Tg00<jj2<Tf2R1f1R2f0R3'2'2p=3g00=CR4/13p=0%?0R0g00=ag00>RR5f:R6#4f9R7f8R8f7R9f6R:f5R;#4f4R<f3R=P1P2P3M;7A56;<g00?JR>9:78g00@KR?P7P8P>C9188>167<'23333X04#0X14#0X24#0X54#0R@X35'1RAf;RB#4P6P7P8P9%4:P<P=P1P2P3M;7A5B:<A:67>P?P6P7P>C9187>166<'23333X04#0X14#0X24#0X54#0R>X45,15[P@X45,15R@P>X35,15[P3X6AP3X6@C;P;P<P=P1P2P3E>P6P7P8P9P:P;P<P=P1P2P3M;=X04#0X14#0X24#0X54#0X45,15'<eX70X;4X:4X94W3W8o"). Qed.

Section PcStmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition pc_pre (entry : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
      (LF : list fframe) (stack lo B shi : Z) (errv : word) : Prop :=
       as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 entry) fc None m (seg_rom asegs)
    /\ as_RHEAP H s LB m /\ as_AKREL H s (mkCfg msF mo)
    /\ as_rauxv_ok H m B /\ bv_unsigned sp <= B /\ B < 2 ^ 64
    /\ bv_unsigned sp mod 16 = 0 /\ stk asegs m lo (bv_unsigned sp) /\ aceil <= lo /\ lo <= bv_unsigned sp - stack
    /\ rw_cells asegs m (errno_addr tp) [C4 errv] /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP /\ bv_unsigned ra mod 2 = 0
    /\ LINV_P5 m /\ ACONST m /\ as_RFS H LF m /\ stack0 m lo shi /\ bv_unsigned sp <= shi.

  Definition pc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (lo B shi : Z) (mo : Model) (res : word) (Q : as_St H -> list block -> mem -> Prop) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv']
      /\ as_rauxv_ok H m' B /\ as_RHEAP H s' LB' m' /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ LINV_P5 m'
      /\ Q s' LB' m'.

  Definition ds_in (LF : list fframe) (ds : Z) : Prop :=
    obj_inframe LF ds DS_SIZE /\ app_obj ds DS_SIZE /\ ds mod 8 = 0 /\ 0 < ds.

  Definition ovf_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBk DB : list block) (LF : list fframe) (lo B shi : Z) (errv : word)
           (ds err len c : Z) (ms : sbuf) (hm fl fill : Z),
      pc_pre AOVF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB LF OVF_STACK lo B shi errv ->
      a0 = Z_to_bv 64 (ds + 8) -> a1 = Z_to_bv 64 c -> 0 <= c <= 255 ->
      ds_rep_w LB m ds err len DB ms (dsdata ds ms + str_cap ms) hm fl fill -> Permutation LB (DB ++ LBk) ->
      lb_own DB m -> ds_in LF ds ->
      len + 1 <= DS_MAXLEN ->
      lb_small LB + 64512 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX -> nlarge LB + 1 <= RT_LARGE_MAX ->
      ICM (str_grow ms) <= as_AL H s ->
      trace_ok (as_TR H) APC0_FREE [0x1200e8] ->
      as_SR H (pc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo B shi mo (Z_to_bv 64 c)
                 (fun s' LB' m' => exists pid' d',
                     Permutation LB' ((pid', d', str_grow ms) :: LBk)
                  /\ ds_rep_w LB' m' ds err (len + 1) [(pid', d', str_grow ms)] (SLong d' (str_grow ms))
                              (d' + str_cap ms + 1) (d' + str_cap ms + 1) fl fill
                  /\ lb_own [(pid', d', str_grow ms)] m'
                  /\ xpres H LBk (bv_unsigned sp) ((ds, ds + DS_SIZE) :: sbx ms) m m'
                  /\ as_AL H s' >= as_AL H s - ICM (str_grow ms)))
              (mkCfg msF mo).

  Definition xsp_src (LBk : list block) (LF : list fframe) (DB : list block) (m : mem) (sp stack ds p n : Z) : Prop :=
    0 <= p /\ p + n <= 2 ^ 64 /\ srcx_keep H LBk LF sp [(ds, ds + DS_SIZE)] m p n /\ in_app_mem p (p + n)
    /\ (p + n <= sp - stack \/ sp <= p)
    /\ (forall a, p <= a < p + n -> ~ (ds <= a < ds + DS_SIZE) /\ ~ in_block DB a).

  Definition xsp_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBk DB : list block) (LF : list fframe) (lo B shi : Z) (errv : word)
           (ds err len p n : Z) (ms : sbuf) (pp hm fl fill : Z),
      pc_pre AXSP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB LF XSP_STACK lo B shi errv ->
      a0 = Z_to_bv 64 (ds + 8) -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 n -> 0 < n ->
      ds_rep_w LB m ds err len DB ms pp hm fl fill -> Permutation LB (DB ++ LBk) ->
      lb_own DB m -> ds_in LF ds ->
      xsp_src LBk LF DB m (bv_unsigned sp) XSP_STACK ds p n ->
      len + n <= DS_MAXLEN ->
      lb_small LB + 2 * 64512 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX -> nlarge LB + 2 <= RT_LARGE_MAX ->
      ds_cost (len + n) <= as_AL H s ->
      trace_ok (as_TR H) APC0_FREE [0x1200e8] ->
      as_SR H (pc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo B shi mo (Z_to_bv 64 n)
                 (fun s' LB' m' => exists DB' ms' pp' hm',
                     Permutation LB' (DB' ++ LBk)
                  /\ ds_rep_w LB' m' ds err (len + n) DB' ms' pp' hm' fl fill
                  /\ pp' - dsdata ds ms' = pp - dsdata ds ms + n
                  /\ lb_own DB' m'
                  /\ xpres H LBk (bv_unsigned sp) ((ds, ds + DS_SIZE) :: sbx ms) m m'
                  /\ as_AL H s' >= as_AL H s - 8 * (blkof ms' - blkof ms)))
              (mkCfg msF mo).
End PcStmts.
