(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup F_atexit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Malloc Monad Stdio Driver Adapter Harness Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RDriver_iface () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad9implM_retC5ARocqVerifyHarness?AgentSubmission4Spec6Driver>read_loop_bodyC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps4bptrC46Stdlib5Lists4List2hdI5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission4Spec4Prog:alloc_initC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5implMK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_ifaceBPTARGET_ALLOC_INITK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission4Spec4Prog;alloc_countc5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_ifaceCPTARGET_ALLOC_COUNTI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rclient_addrc5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_iface7rin_ivsC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_iface9pdrv_presC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks5blockc5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_iface;pstdout_ivsC47Corelib4Init5Logic8eq_transC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface:rheap_presC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree3memC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magree".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition PMAIN : Z := 0x12da0.
Definition PSTAGE2_RET : Z := 0x213e4.      (* [comment removed for export] *)
Definition PEXIT : Z := 0x2192c.
Definition PTARGET_ALLOC_INIT : Z := 0x13064.
Definition PTARGET_ALLOC_COUNT : Z := 0x13068.
Definition PTARGET_RUN : Z := 0x13070.
Definition PEMIT_PRINTF : Z := 0x131f8.
Definition PFUZZ_INIT : Z := 0.             (* [comment removed for export] *)
Definition PGOT_FUZZ_INIT : Z := 0x2a4f0.   (* [comment removed for export] *)
Definition PINIT_FLAG : Z := 0x3b7a0.       (* [comment removed for export] *)
Definition PAEF_ARGC : Z := 0x2b550.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PTARGET_RUN_STACK : Z := 80 + HARNESS_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pat_exit (code : Z) (s : PState) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PEXIT) fc None m (seg_rom usegs)
    /\ stk usegs m lo (bv_unsigned sp)
    /\ rw_cells usegs m 0x3b7d8 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m 0x5bb08 [C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs m 0x2a530 [C8 (Z_to_bv 64 0x2a498); C8 (Z_to_bv 64 0x2a490)]
    /\ rw_cells usegs m 0x2a490 [C8 (Z_to_bv 64 0x12d10)]
    /\ rw_cells usegs m 0x2b798 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m 0x2a4d8 [C8 (Z_to_bv 64 0x21810); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m 0x5bb30 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells usegs m 0x2b540 [C8 (Z_to_bv 64 0x2b540)]                   (* [comment removed for export] *)
    /\ (exists reg : bool, atx_state reg m)                                 (* [comment removed for export] *)
    /\ rw_cells usegs m 0x5bf60 [C8 (Z_to_bv 64 0)] /\ rw_cells usegs m 0x5bf50 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m 0x2b740 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells usegs m 0x2b650 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_file m
    /\ rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 guard]
    /\ mem_inv usegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x5d000 <= lo
    /\ bv_unsigned sp < 2^47.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STG (m : mem) : Prop := exists sj, rw_cells usegs m UREAD_STAGE [CB PSTAGE_LEN sj].

(* [comment removed for export] *)
Definition dvalid_sp (sp0 : word) (argv envp : list (list byte)) : Prop :=
  valid_sp sp0 /\ ATOP = bv_unsigned sp0 - 8388608 /\ entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (ms : machine_state),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    Startup.pat_main sp0 argv envp uid hw draw CAN ms ->
    implM usegs
      (main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
      (ps_init (reservedZ usegs) ATOP)
      (fun code s' ms' => pat_exit code s' ms') ms.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ptarget_alloc_init_spec : forall (bitmap : Z) (s : PState)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  implM usegs (Prog.alloc_init bitmap) s
        (fun _ s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom usegs) /\ s' = s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PTARGET_ALLOC_INIT) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01bh11mh23ms'h31Fh42a0h52a1h62a2h72a3h82a4h92a5h:2a6h;2a7h<6bitmaph=9drhs_dieth>2fch?2gph@2rahA1shB2s'hC2s0hD2s1hE3s10hF3s11hG2s2hH2s3hI2s4hJ2s5hK2s6hL2s7hM2s8hN2s9hO2sphP2t0hQ2t1hR2t2hS2t3hT2t4hU2t5hV2t6hW2tphX1zp;1p;2p;Op;7p;3p;4p;5p;6p;>p;8p10000p4p70R0g000eR1p4p710R2p8P0p1001^p4p710R0p8p1002]p4p70R3P2p8P3P0p8p1003Rp4p70R0p1004Kp4p710p8P0p1004bp4p710p8g005^R0p4p7210g006JR3p4p710p8g006hj1:Tg007Mj1>Tg007kj1CTg008Nj14TP0j2]Tg0093j1BTg009UlOFTg00:Gj1ETg00;=j1UTg00;_j1QTg00<Xj73Tg00=Jj31Tg00=dj2KTg00>?j1?Tg00>]j2;Tg00?Cj1\Tg00@0j20Tg00@Rj46Tg00A?j1WTg00BEj1VTg00CMj2HTg00DIj28Tg00Dcj2@Tg00EVj3ATg00F9j3TTg00Fej5RTg00GNj3PTg00H5j3OTg00I7j2NTg00J2j2MTg00JZj2GTg00KRj2DTg00L7j3=Tg00L\j2LTg00MFj1STP3j6<Tg00NAj1kTg00O?j2jTg00O\j1iTg00P=j3hTg00Phj3gTg00QMj3fTg00RHj2eTg00SJj1bTg00TJj2^Tg00Tjj4_Tg00UJj1`Tg00V;l>[Tg00W3j4JTg00WNj4aTg00XDj6ZTP1j8cTg00Y:j1dTg00Z3j7YTg00Zhj2XTf0R1#:#:p=7f6R3f5R0f4R2f3R4f2R5C6f1R6P1C6p=2P2P41056P1C6p=5P3P0P2P4P5P6P1C6C6p=Ig00\0R7/X1p=9g00]7R8g00]UR9g00^NR:#:R;#:R<#:R=#7R>#:R?#>R@#CRA%4;#>R;/]A%>>R>#CRB%>=#C#B\AP9g00_3R=g00_hRCg00`HfRRDfTREfSRFPDfQRGfPRHfORIfNRJfMRKfLRLfKRMfJRNfIROfHRPfGRQfFRRfERSfDRTfCRUfBRVfARWf@RXf?RYf>RZf=R[f<R\f;R]f:R^f9R_f8R`f7RaP3MOFP0%EEP2%UAREP4%Q=RbF39171fU9196'KX27XB9VCRcPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP3P0P2P4MOFRdP5%7:#4#4#:#7#7#4#4#7#4#7#?,;@ReP6PEP1PbF3RfP=PDPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP3P0P2MOFRgP4%EDRhP5PEP6PbF39171A19FF'KX27RiPfPAPAPAPAPAPA%\ARj10A4Pj10AURUPjF210AMRMPAPjPAP]PjD5R]10AIRIPAPAPj10AYPj10AQPAPjPAPaPjD5F2RaF210AGRQPAPAPAPj10AWPj10AOPAPjPAP_PjD5F2R_10AKRKPAPAPjPAP[PjD5R[10ASRSPAPjPAP0PjD5R0FIROPEPAPAPAPAPjPAPVPjD510ANPAPjPAP^PjD510AJPAPAPj10AZPj10ARPAPjPAP3PjD5F2F2R310AHRHPAPAPAPj10AXPj10APPAPjPAP`PjD5F2R`10ALRLPAPAPjPAP\PjD5R\10ATRTPAPjPAP2PjD5RPC6FIF2P5%EGRGP6PEP1PbF3RX%BARR%Wf;1E%V7RZ1H=f%9XRf3118REPfPZPZ%?<R<,;@g00`hRf%7?R?#?,@;5A;%?:RR1@;R5A;%4:#7#>R:1@:f7AfR;3TRJPgP4PeP5PEDR3P=O=6,NbA1Z16X1ZPA1M:;R^,GDPAPAPAPAPAP0PSPjC6PKP[PQP_F210AFPAPAPAPjPUPjC6PMP]PIPaF2RaPEPAPAPAPAPjPTPjPLP\F2PHP`10ADRIP3F2F2R]P2g00aFRM,D@9=@1P4PEP5PbF3#9=1Z6X0APA1;@RRRP]P21GF^1D@15=@P4PEP5PbF3#9=1Z6X0AP81L@DR^P]P21;@11D@RRR5=@P4PEP5PbF3#9=1Z6XX8PAPDP]P2A=@1RP4PEP5PbF3#9=1Z6X0APAPhP]P2P1P4PEP5PbF3#9=1Z6X0APAPAPAPAPAPPPTPjC6PLP\PHP`F2PIP3PEPAPaPQPOC6F2P4PhP5PEP6PbF3#9,8ZA=@DR%SDE<1;@^%kDE<1j^f%i^E<PMg00akE<Ah:@;9g@DAfD:;E<PgP4PeP5PEP6PbF3,H=P=PgP4PeP5PEP6Pb%4?#4#7#4#4#4#?R?1@>?5A>R>PJP<%BBR?10B>RB'81e=e=1?Bdg00baRBg00cAR?'8%b>=1B?dg00caR?/^8RB#BReP?P8PJP<C_,0BRB'8%`>=1eBdM>[E<b=CJP=PiPXPdP5PGP6PEP1PbF3RG917XA19DD187G189DCJCaEZGcP9P=PC%dFPDPcPdP5g00dM,;@P6PEP1PbF3FYeW1W>W3XVAXUAXTAXSAXFAXEAXNAXMAXLAXKAXJAXIAXHAXGAX;AX:AX9AX8AX7AX6AX5AX4AXDAXCAXRAXQAXPAXWAX?AXOAW@WAW<o"). Qed.

(* [comment removed for export] *)
Lemma ptarget_alloc_count_spec : forall (s : PState)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  implM usegs Prog.alloc_count s
        (fun r s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom usegs) /\ s' = s /\ r = 0)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PTARGET_ALLOC_COUNT) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01bh13ms'h29drhs_dieth31mh41Fh52a0h62a1h72a2h82a3h92a4h:2a5h;2a6h<2a7h=5dietRh>6dietR0h?6dietR1h@6dietR2hA2fchB2gphC1rhD2rahE1shF2s'hG2s0hH2s1hI3s10hJ3s11hK2s2hL2s3hM2s4hN2s5hO2s6hP2s7hQ2s8hR2s9hS2sphT2t0hU2t1hV2t2hW2t3hX2t4hY2t5hZ2t6h[2tph\1zp%0p;1p;2p;Op;7p;3p;4p;5p;6p;>p;8g006hj1:Tg007Mj1DTg007kj1OTg008Nj1@Tg005^j2sTg0093j1KTg00>]j29Tg009UlOCTg00:Gj1JTg00;=j1dTg00;_j1bTg00<Xj72Tg00=Jj31Tg00=dj2ATg00>?j1<Tg00?Cj1mTg00@0j20Tg00@Rj43Tg00A?j1WTg00BEj1eTg00CMj2HTg00DIj27Tg00Dcj2>Tg00EVj3BTg00eXj4cTg00Fej5UTg00GNj3TTg00H5j3STg00I7j2RTg00J2j2aTg00JZj2ITg00Phj3`Tg00O?j2NTg00L\j2^Tg00fDj2vTg006Jj68Tg00gFj2uTg00P=j3tTg00hAj3rTg00hij3qTg00RHj2]Tg00SJj1\Tg00TJj2pTg00Tjj4XTg00UJj1[Tg00V;l>YTg00W3j4MTg00icj1lTg00F9j3kTg00KRj2QTg00L7j3ETg00MFj1iTg00NAj1jTg00O\j1hTg00QMj3nTg00WNj4oTg00XDj6ZTg000ej8gTg00Z3j7fTg00Zhj2PTf0R0#:#:p=6%@0#@p=F%:0#@p=L%@0#:p=Gf7R1f6R2f5R3f4R4f3R5'0f2R6C3f1R7P0C3p==P4P51067P0C3p=4P2P3P4P5P6C3P7P0C3p=5P2P3P4P5P6P7P0C3C3p=?g00\0R8/P0p=V1P87=160p=;P2P3P4P5P6P7P0F2,P8p=_g00]UR9g00^NR:#:R;#:R<#:R=#6R>#:S00#DR?#OR@%@;R;#DRA/s@%D>R>#ORB%D=#O#K\@P9g00_3R=g00]7RCg00`hRDfRREfTRFfSRGPEfQRHfPRIfORJfNRKfMRLfLRM19?DRNfJROfIRPfHRQfGRRfFRSfERTfDRUfCRVfBRWfARXf@RYf?RZf>R[f=R\f<R]f;R^f:R_f9R`f8RaP1P2MOCP3%JFP4%d@RbP5%b=RcF29180fURd9197A1C6D'A'AX18XF9XCCS01PHPIPJPKPLPMfKRePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1P2P3P4P5MOCS02P6%6:#F#6#6#L#G#G#6#<Rf,9?RgP7PbP0PcF2RhP=PEPHPIPJPKPLPMPePOPNPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1P2P3P4MOCP5%JEP6PbP7PcF29180A19GGA1CDDRi'A'AX18PhP@P@P@P@P@P@%m@RjP@P5Pj10@VS03PjG=10@eRkP@PjP@P^PjD4S0410@JRlP@P@PjP@PZPjD4S0510@RS06P@PjP@P1PjD4S07C3S08F510@HRmP@P@P@PjP@PXPjD4S09P@PPP@PjP@P`PjD4S0:D4S0;10@LRnP@P@PjP@P\PjD4S0<10@TS0=P@PjP@P3PjD4RoC3S0>C3PbP@P@P@P@PjP@PWPjD4RpP@POP@PjP@P_PjD4RqD4S0?10@KRrP@P@PjP@P[PjD4S0@10@SS0AP@Pj10@2PjF?RsC3S0B10@IRtP@P@P@PjP@PYPjD4Ru10@NRvP@PjP@PaPjD4RwC310@MS0CP@P@PjP@P]PjD4Rx10@US0DP@PjP@P4PjD4S0EC3F?F5P6%6:#F#6#6#L#G#F#6#<,9?RyP7PbP0PcF2Rz%K@R{%Wh;1b%e8R|1H=h%VzRz3117{bS0FPzP|P|%<<R<,9?Rzg00jPS0G%:;S0H#<R;1>A;5BA1>AD9BAD%@:#6#DR;1>;D7BDRhCcS0IPEPHPIPJPKPLPMPePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1P2P3P4MOCS0JP5PgP6PbDU3T=S=7,RcA1|07X3|S0KP@g00k<R}1a;hR~'IS0LP@P@P@P@P@PoQ0=PjPnQ0<F5PmQ0;10@GS0MP@P@P@PjQ03PjC3S03PkQ04C3S0NPlQ08C3S0OF5RkPbP@P@P@P@PjQ0DPjC3S0PQ0CPxPtP@PuP@PQPwD4S0QF5Rw10@ERuP@P@PpP@P0PqPrPsG=F?S0RP4A`?gzS0SP5PbP6PcF2=;|7X0@P@1Nf<,9?RoP@PkPbP@PwPuP@P@PpP@Q0LPqPrPsG=F?P4P0P5PbP6PcF2=;|7X0@P@PNP@PkPbP@PwPuP@P@PpP@1I0~PqPrPsG=F?P4PoP5PbP6PcF2=;|7X0@P@1ND~,9?Q0RP4PoP5PbP6PcF2=;|7X0@P@P@P@P@P@Q0EQ0DPjC3Q0CPxPtQ0QF5RoPuQ0BPbP@Q0OPmP@P@Q09PvQ0:C3PnQ0>F?F5P5PyP6PbP7PcF_,7|1^?N/N~,9?1vD~E8P}g00kaE8Q0S1uf<E8Q0GAt;?hS0S7r}Aq};hE8Q0JP5PgP6PbP7PcF2,H=P=Q0JP5PgP6PbP7PcQ0H#:#L#6#F#<R}1>>}5B>R}Q0IP<%KBRf10B}Rs'71]=g=1fsdg00baRsg00cARg'7S0H%\}=1sgdg00caRq/pCRp#KRwPqPCQ0IP<CX,0pRk'7%[}=1wkdM>YE8b2CMP@p-1Po%l@RoQ0OPoP@P@P@P@PjQ0=PjC3PnQ0<PmQ0;F5S0;Q0MP@P@Q03PvQ04C3PlQ08F?PoP=fVRoPdPFPGPEPHPIPJPKPNPMPePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaMOCP1%JoRMP2PbP3PcF29180fWRm=19m/Ai'AX18S08P5P5P6P5PdP7PbP0G=RnP2PyP3PbP4PcF2RkPnP2%JdRnP3PbP4PcF2R}%Wk=1{b1H=k%V}R}51|Q0FP}P|P|Q00#6R}#<,>A9BAD%<:R:1>A:5BA;khRAP4P4P5P4PoP6PbP7G=RkP1PyP2PbDU5Tz=S=3,RcQ0KP@1Io~P3P3P4P3PmP5PbP6G=R5Pag00aFRz,Q?9E?0P1PbP2PcF2=;|7X0@P@19?:R:P5Pa1Im~1Q?05E?P1PbP2PcF2=;|7X0@PC1^?oRmP5Pa19?01Q?:R:5E?P1PbP2PcF2=;|7X\CP@PoP5PaAE?0:P1PbP2PcF2=;|7X0@P@PMP5PaP0P1PbP2PcF2=;|7X0@PkP1PMP2PbP3PcF_,7|AE?o:%ioE819?m%joE81NmD%hmE8Pzg00akE8Q0S9`?oAno;hE8PkP1PyP2PbP3PcF2,H=P=PkP1PyP2PbP3Pc%@}#G#L#F#<R}1>>}5B>R>PAP<10B>RB,7f1]=y=1fBdQ0H%\>=1sgdPqPCPAP<CX,0pRp,7w%[>=1wpdM>YE8b2CMP=Q08P@P@P@P@P@Q07Q06PjC3PlQ05Q0MQ0NF5P@PdQ0;PbP@P@P@P@PjQ0APjPrQ0@F5PuQ0?10@FP@P@Q0PPvPxPtQ0QF5F5G=P2PnP3PbP4PcF2RtPdPFPGPEPHPIPJPKPLPNPePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1MOCP2PnP3PbP4PcF2R4918tA19ooRt/Ai1784PtPi179o17CDCMCMCoEZb@b?b>b=EZGgP9P=PCg00lWPEQ01Q02P6g00mQ,9?P7PbP0PcF2FfeW3WAW4XZ@XY@XX@XW@XJ@XI@XR@XQ@XP@XO@XN@XM@XL@XK@X<@X;@X:@X9@X8@X7@X6@X5@XH@XG@XV@XU@XT@X[@XB@XS@WDWEo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition trun_cells0 (m : mem) : Prop :=
  rw_cells usegs m PINIT_FLAG [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m PGOT_FUZZ_INIT [C8 (wz PFUZZ_INIT)]
  /\ rw_cells usegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
  /\ rw_cells usegs m PSTDERR_PTR [C8 (wz RSTDERR)]
  /\ atx_state false m.

(* [comment removed for export] *)
Definition pstdout_ivs : list (Z * Z) :=
  [(0x2b658, 0x2b658 + 232); (0x5bf78, 0x5bf78 + 1024); (PINIT_FLAG, PINIT_FLAG + 1);
   (PAEF_INCB, PAEF_INCB + 1); (0x5b8f0, 0x5b8f4); (0x5b8f8, 0x5b900); (0x5b908, 0x5b910); (0x5ba08, 0x5ba10)].

Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
  match ivs with [] => False | (lo, hi) :: ivs' => (lo <= a < hi) \/ rin_ivs ivs' a end.

(* [comment removed for export] *)
Definition pdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ rin_ivs pstdout_ivs a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma pdrv_pres_refl : forall LB SP m, pdrv_pres LB SP m m.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01Hh12LBh22SPh32_Hh43_H0h53_H1h61ah71mp;1p;2p;3p;4g00n]j1CTg006hj10Tg007Mj13Tg007kj14Tg0093j1BTg00o=j2ATg00>?j16Tg00oYj2<Tg0106j2;Tg00=dj2:Tg010Rj38Tg011Wj29Tg012Wj11Tg0130j17Tg00=Jj32Tg013_j35Tg00;=j1@Tg00DIj2?Tg00W3j4>Tg014\j4=Tg015^#Cg00]7R0g00^N#0R1#0#0R2#0#0#0R3#3#4%32#4R2#BR4[g00`hf0R5'A%61%63'<,;5':f4R3f3R1f1R638g016\f2R7'9#1P3%71R1O1R8=248g00_3R9?531%@2R2524#1R1f5%73559=242#1[1?48P5X01C>W5W4W3X60P7P6P5P5C=eW7W2W1o"). Qed.

Lemma pdrv_pres_trans : forall LB SP m1 m2 m3, pdrv_pres LB SP m1 m2 -> pdrv_pres LB SP m2 m3 -> pdrv_pres LB SP m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h02a0h12E1h22E2h31Hh42H1h52H2h62Hah72Hch82Hxh92LBh:2SPh;2W1h<2W2h=1ah>2m1h?2m2h@2m3p;1p;4p;2p;3p;6g00n]j1DTg006hj13Tg007Mj17Tg007kj16Tg0093j1CTg014\j45Tg00o=j2>Tg00>?j18Tg00oYj2=Tg0106j2<Tg00=dR0j24Tg010Rj3;Tg011Wj2:Tg012Wj19Tg0130j11Tg00=Jj32Tg00;=j1BTg017`j6ATg00W3j4?Tg013_j3@Tf3R1g00_3f2R2f1R33@f0R432#9p=0g015^#Dg00]7R5g00^N#3R6#3#3R7#3#3#3R8#7#6%77#6R7#CR9[R:f4R;P1P2P3C5f5R<P;P2P3C5g00`h/>4%86%88'=,<4'4f8R8f7R6;;3g016\/:2#9P<P1P2P3P4O4P6%11R1O1P8P1O1529P9P8P1%B7R7C0P9P8%1;R1P7C0['4P0P8P1O1f9R=P1O1529P9P=P1P7C0P9P=%1<R1P7C0[P8P1O1f:R>P1O1529P9P>P1P7C0P9P=f6R1#1R?P7C0['4P4P>P?O1f;R@P?O1529P9f<R?%16P7C0P9P?%18RAP7C0RB[P=P8P6P1P<O4P@PAO1P?PAO1529P9P?%1=R=P7C0\B'4P0P?P=O1f=R0P=O1529P9P0P=P7C0P9P0%1>R>P7C0[P0P>O1f?R=P>O1529P9P=P>P7C0P9f>R>%1@R@P7C0['4P4P>P@O1P=P@O1529P9f@R@%1?P7C0P9P@%10R0P7C0[P@P0O1R@fBR?P0O1R=529P9P?P0P7C0R?P9fARB%1>P7C0[P9P@PBP0O1P=P3P1EAP3P1P4O1O1X3?C?W<W2P3P4O2n2001000000120000000b0W;W1P3P4O2n2001000000121000000b0W8W7W6X=5P1P<P;P2C5eW5W4X@:X?:W>W:W9o"). Qed.

Lemma pdrv_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> pdrv_pres LB SP m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01Hh12Hah22Hch32LBh42SPh52_Hh61ah71mh82m'p;1p;4p;2p;3g00n]j1;Tg018>j4:Tg00o=j23Tg006hj10Tg00>?j11Tg00oYj29Tg0106j27Tg00=dj24Tg010Rj35Tg011Wj26Tg012Wj12Tg014\j48Tg015^#;g00]7R0g019AR1f3R2f2R3f1R4f0R5C:g00`h/35g00^N#0R6#1%06#0#0#0#0#1'9,75'4f6f5;54g016\/63#2f4R5P2P3P4O3W5W2W1X60P5P2P3P4C8eW0X81W7W4W3o"). Qed.

Lemma pdrv_pres_agree : forall LB SP m m', pdrv_pres LB SP m m' ->
  magree usegs (fun a => rclient_addr LB SP a /\ ~ rin_ivs pstdout_ivs a) m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01ah11Hh22H0h32Hah42Hch52Hxh62LBh72SPh81mh92m'p;1p;4p;2p;3g00n]j1BTg006hj10Tg007Mj17Tg007kj16Tg0093j1ATg014\j4@Tg00o=j2=Tg00>?j18Tg00oYj2<Tg0106j2;Tg00=dR0j23Tg010Rj34Tg011Wj22Tg012Wj11Tg0130j1:Tg00=Jj35Tg013_j39Tg00;=j1?Tg01:;j4>Tg015^#Bg00]7R1g00^N#0R2#0#0R3#0#0#0R4#7#6%73#6R3#AR5[R6f3R7f2R8f1R9f0R:C@g00`h/=:%82%84'<,;:'3f6R4f5R2;49g016\R;/29#1'3P0f7R0?44812;8#1P2%:7R7O1P4P7O1555g00_3R<?947%?3R3555#1f4R7#:99<4=553#1['3P:f9f8;4712;2#1P0P4P2P9P:O4W5W4P9P:O2n2001000000120000000W2W3X01P<A427:12;:#1'3X01P8P9C>eW1X96W8W7W6o"). Qed.

(* [comment removed for export] *)
Definition ptarget_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (AB lo : Z) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ 0 <= r <= 2
    /\ mem_inv usegs m' /\ frm0 fc' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' AB
    /\ pdrv_pres LB (bv_unsigned sp) m m'
    /\ RHEAP s' LB m'
    /\ stdout_file m' (ps_so s')
    /\ atx_state true m'.

Definition ptarget_run_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z) (errv : word),
  RHEAP s LB m -> In (p, A, cap) LB ->
  bytes_at usegs m A (zbytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  trun_cells0 m -> stderr_file0 m ->
  rauxv_ok m AB -> bv_unsigned sp <= AB -> AB <= 2^47 ->          (* [comment removed for export] *)
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PTARGET_RUN_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m -> frm0 fc ->
  stdout_file m (ps_so s) ->
  tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implM usegs (Prog.run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (ptarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz PTARGET_RUN) fc None m (seg_rom usegs)).
End CANSEC1.
