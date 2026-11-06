(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg F_syscalls StdioFiles Startup F_atexit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Malloc Monad Stdio Driver Adapter Harness Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RDriver_iface () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog:alloc_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c59OSSVerify5KrLib5Plain=RDriver_ifaceBPTARGET_ALLOC_INITC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;alloc_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RDriver_ifaceCPTARGET_ALLOC_COUNTC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5Plain=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RDriver_iface7rin_ivsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc59OSSVerify5KrLib5Plain=RDriver_iface9pdrv_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RDriver_iface;pstdout_ivsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib5Plain=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition PMAIN : Z := 0x12d30.
Definition PSTAGE2_RET : Z := 0x1d368.      (* [comment removed for export] *)
Definition PEXIT : Z := 0x1d8b0.
Definition PTARGET_ALLOC_INIT : Z := 0x12ff4.
Definition PTARGET_ALLOC_COUNT : Z := 0x12ff8.
Definition PTARGET_RUN : Z := 0x13000.
Definition PEMIT_PRINTF : Z := 0x13188.
Definition PFUZZ_INIT : Z := 0.             (* [comment removed for export] *)
Definition PGOT_FUZZ_INIT : Z := 0x26478.   (* [comment removed for export] *)
Definition PINIT_FLAG : Z := 0x37730.       (* [comment removed for export] *)
Definition PAEF_ARGC : Z := 0x274d8.        (* [comment removed for export] *)

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
            F (Z_to_bv 64 PEXIT) fc None m (seg_rom psegs)
    /\ stk psegs m lo (bv_unsigned sp)
    /\ rw_cells psegs m 0x37768 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m 0x57a98 [C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x264b8 [C8 (Z_to_bv 64 0x26420); C8 (Z_to_bv 64 0x26418)]
    /\ rw_cells psegs m 0x26418 [C8 (Z_to_bv 64 0x12ca0)]
    /\ rw_cells psegs m 0x27728 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0x26460 [C8 (Z_to_bv 64 0x1d794); C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x57ac0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells psegs m 0x274c8 [C8 (Z_to_bv 64 0x274c8)]                   (* [comment removed for export] *)
    /\ (exists reg : bool, atx_state reg m)                                 (* [comment removed for export] *)
    /\ rw_cells psegs m 0x57ef0 [C8 (Z_to_bv 64 0)] /\ rw_cells psegs m 0x57ee0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x276c8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells psegs m 0x275d8 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_file m
    /\ rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 guard]
    /\ mem_inv psegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x59000 <= lo
    /\ bv_unsigned sp < 2^47.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STG (m : mem) : Prop := exists sj, rw_cells psegs m PREAD_STAGE [CB PSTAGE_LEN sj].

(* [comment removed for export] *)
Definition dvalid_sp (sp0 : word) (argv envp : list (list byte)) : Prop :=
  valid_sp sp0 /\ ATOP = bv_unsigned sp0 - 8388608 /\ entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (ms : machine_state),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    Startup.pat_main sp0 argv envp uid hw draw CAN ms ->
    implM psegs
      (main_model Prog.io raw_malloc raw_free PREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
      (ps_init (reservedZ psegs) ATOP)
      (fun code s' ms' => pat_exit code s' ms') ms.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ptarget_alloc_init_spec : forall (bitmap : Z) (s : PState)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  implM psegs (Prog.alloc_init bitmap) s
        (fun _ s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom psegs) /\ s' = s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PTARGET_ALLOC_INIT) fc None m (seg_rom psegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01bh11mh23ms'h31Fh42a0h52a1h62a2h72a3h82a4h92a5h:2a6h;2a7h<6bitmaph=9drhs_dieth>2fch?2gph@2rahA1shB2s'hC2s0hD2s1hE3s10hF3s11hG2s2hH2s3hI2s4hJ2s5hK2s6hL2s7hM2s8hN2s9hO2sphP2t0hQ2t1hR2t2hS2t3hT2t4hU2t5hV2t6hW2tphX1zp;1p;2p;Op;7p;3p;4p;5p;6p;>p;8p10000p4p70R0g000eR1p4p710R2p8P0p1001^p4p710R0p8p1002]p4p70R3P2p8P3P0p8p1003Rp4p70R0p1004Kp4p710p8P0p1004bp4p710p8g005^R0p4p7210g006JR3p4p710p8g006hj11Tg007Mj1?Tg007kj1DTg008Nj17TP0j2kTg0093j1BTg009UlOFTg00:Gj1ETg00;=j1UTg00;_j1STg00<Xj74Tg00=Jj32Tg00=dj2HTg00>?j1>Tg00>]j2:Tg00?Cj1]Tg00@0j20Tg00@Rj46Tg00A?j1WTg00BEj1VTg00CMj2ITg00DIj28Tg00Dcj2ATg00EVj3@Tg00F9j3RTg00Fej5QTg00GNj3PTg00H5j3OTg00I7j2NTg00J2j2MTg00JZj2GTg00KRj2CTg00L7j3=Tg00L\j2LTg00MFj1TTP3j6;Tg00NAj1jTg00O?j2iTg00O\j1hTg00P=j3gTg00Phj3fTg00QMj3cTg00RHj2bTg00SJj1`Tg00TJj2\Tg00Tjj4^Tg00UJj1_Tg00V;l>[Tg00W3j4KTg00WNj4aTg00XDj6ZTP1j8dTg00Y:j1eTg00Z3j7YTg00Zhj2XTf0R1#7#7p=<f6R3f5R0f4R2f3R4f2R5C6f1R6P1C6p=3P2P41056P1C6p=5P3P0P2P4P5P6P1C6C6p=Jg00\0R7/X1p=9g00]7R8g00]UR9g00^NR:#1R;#1R<#1R=#1#1R>#1R?#?R@#DRA%7;#?R;/kA%?>R>#DRB%?=#D#B\AP9g00_3R=g00_hRCg00`HfRRDfTREfSRFPDfQRGfPRHfORIfNRJfMRKfLRLfKRMfJRNfIROfHRPfGRQfFRRfERSfDRTfCRUfBRVfARWf@RXf?RYf>RZf=R[f<R\f;R]f:R^f9R_f8R`f7RaP3MOFP0%EEP2%UAREP4%S=RbF49271fU9296'HX27XB9VCRcPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP3P0P2P4MOFRdP5%1:#1#7#1#<#<#<#<#1#7#1#1#>,:@ReP6PEP1PbF4RfP=PDPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP3P0P2MOFRgP4%EDRhP5PEP6PbF49271A29FF'HX27RiPfPAPAPAPAPAPA%]ARj10A4Pj10AURUPjF310AMRMPAPjPAP]PjD5R]10AIRIPAPAPj10AYPj10AQPAPjPAPaPjD5F3RaF310AGRQPAPAPAPj10AWPj10AOPAPjPAP_PjD5F3R_10AKRKPAPAPjPAP[PjD5R[10ASRSPAPjPAP0PjD5R0FJROPEPAPAPAPAPjPAPVPjD510ANPAPjPAP^PjD510AJPAPAPj10AZPj10ARPAPjPAP3PjD5F3F3R310AHRHPAPAPAPj10AXPj10APPAPjPAP`PjD5F3R`10ALRLPAPAPjPAP\PjD5R\10ATRTPAPjPAP2PjD5RPC6FJF3P5%EGRGP6PEP1PbF4RX%BARR%Wf;2E%V7RZ1I=f%9XRf3218REPfPZPZ%><R<,:@g00`hRf%1?#1R?#>,A;5@;%>:RR1A;R5@;%7:#1#1#?R:1A:f7@fR;3RRJPgP4PeP5PEDQ3P=O=6,NbA2Z16X1ZPA1M:;R^,GDPAPAPAPAPAP0PSPjC6PKP[PQP_F310AFPAPAPAPjPUPjC6PMP]PIPaF3RaPEPAPAPAPAPjPTPjPLP\F3PHP`10ADRIP3F3F3R]P2g00aFRM,C@9=@1P4PEP5PbF4#9=2Z6X0APA1:@RRRP]P21GF^1C@15=@P4PEP5PbF4#9=2Z6X0AP81L@DR^P]P21:@11C@RRR5=@P4PEP5PbF4#9=2Z6XX8PAPDP]P2A=@1RP4PEP5PbF4#9=2Z6X0APAPhP]P2P1P4PEP5PbF4#9=2Z6X0APAPAPAPAPAPPPTPjC6PLP\PHP`F3PIP3PEPAPaPQPOC6F3P4PhP5PEP6PbF4#9,8ZA=@DR%TDE;1:@^%jDE;1i^f%h^E;PMg00akE;Ag:@;9f@DAcD:;E;PgP4PeP5PEP6PbF4,I=P=PgP4PeP5PEP6Pb%<?#1#1#7#<#>R?1A>?5@>R>PJP<%BBR?10B>RB'81b=e=2?Bdg00baRBg00cAR?'8%`>=2B?dg00caR?/\8RB#BReP?P8PJP<C^,0BRB'8%_>=2eBdM>[E;b=CKP=PiPXPdP5PGP6PEP1PbF4RG927XA29DD187G189DCKCaEZGdP9P=PC%eFPDPcPdP5g00dM,:@P6PEP1PbF4FYeW1W>W3XVAXUAXTAXSAXFAXEAXNAXMAXLAXKAXJAXIAXHAXGAX;AX:AX9AX8AX7AX6AX5AX4AXDAXCAXRAXQAXPAXWAX?AXOAW@WAW<o"). Qed.

(* [comment removed for export] *)
Lemma ptarget_alloc_count_spec : forall (s : PState)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  implM psegs Prog.alloc_count s
        (fun r s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom psegs) /\ s' = s /\ r = 0)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PTARGET_ALLOC_COUNT) fc None m (seg_rom psegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01bh13ms'h29drhs_dieth31mh41Fh52a0h62a1h72a2h82a3h92a4h:2a5h;2a6h<2a7h=5dietRh>6dietR0h?6dietR1h@6dietR2hA2fchB2gphC1rhD2rahE1shF2s'hG2s0hH2s1hI3s10hJ3s11hK2s2hL2s3hM2s4hN2s5hO2s6hP2s7hQ2s8hR2s9hS2sphT2t0hU2t1hV2t2hW2t3hX2t4hY2t5hZ2t6h[2tph\1zp%0p;1p;2p;Op;7p;3p;4p;5p;6p;>p;8g006hj1;Tg007Mj1ETg007kj1MTg008Nj1=Tg005^j2nTg0093j1GTg00>]j27Tg009UlODTg00:Gj1ITg00;=j1bTg00;_j1`Tg00<Xj72Tg00=Jj33Tg00=dj2CTg00>?j1?Tg00?Cj1lTg00@0j20Tg00@Rj41Tg00A?j1WTg00BEj1cTg00CMj2JTg00DIj28Tg00Dcj2BTg00EVj3@Tg00eXj4aTg00Fej5TTg00GNj3STg00H5j3RTg00I7j2QTg00J2j2_Tg00JZj2HTg00Phj3PTg00O?j2LTg00L\j2]Tg00fDj2tTg006Jj69Tg00gFj2sTg00P=j3rTg00hAj3qTg00hij3pTg00RHj2ZTg00SJj1YTg00TJj2mTg00Tjj4XTg00UJj1UTg00V;l>[Tg00W3j4KTg00icj1iTg00F9j3hTg00KRj2OTg00L7j3FTg00MFj1gTg00NAj1fTg00O\j1jTg00QMj3kTg00WNj4eTg00XDj6\Tg000ej8oTg00Z3j7dTg00Zhj2NTf0R0#;#;p=:%=0#=p=5f7R1f6R2f5R3f4R4f3R5'0f2R6C1f1R7P0C1p=>P4P51067P0C1p=4P2P3P4P5P6C1P7P0C1p=6P2P3P4P5P6P7P0C1C1p=Ag00\0R8/N0p=V1N87=360p=<P2P3P4P5P6P7P0F2,N8p=^g00]UR9g00^NR:#;R;#;R<#;R=#:R>#;S00#ER?#MR@%=;R;#ERA/n@%E>R>#MRB%E=#M#G\@P9g00_3R=g00]7RCg00`hRDfRREfTRFfSRGPEfQRHfPRIfORJfNRKfMRLfLRM17?DRNfJROfIRPfHRQfGRRfFRSfERTfDRUfCRVfBRWfARXf@RYf?RZf>R[f=R\f<R]f;R^f:R_f9R`f8RaP1P2MODP3%IFP4%b@RbP5%`=RcF29380fURd9397A3C6D'C'CX18XF9XCCS01PHPIPJPKPLPMfKRePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1P2P3P4P5MODS02P6%::#=#;#=#5#5#5#5#;#:#?Rf,7?RgP7PbP0PcF2RhP=PEPHPIPJPKPLPMPePOPNPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1P2P3P4MODP5%IEP6PbP7PcF29380A39GGA3CDDRi'C'CX18PhP@P@P@P@P@P@%l@RjP@P5Pj10@VS03PjG>10@eRkP@PjP@P^PjD4S0410@JRlP@P@PjP@PZPjD4S0510@RS06P@PjP@P1PjD4S07C1S08F610@HRmP@P@P@PjP@PXPjD4S09P@PPP@PjP@P`PjD4S0:D4S0;10@LRnP@P@PjP@P\PjD4S0<10@TS0=P@PjP@P3PjD4RoC1S0>C1PbP@P@P@P@PjP@PWPjD4RpP@POP@PjP@P_PjD4RqD4S0?10@KRrP@P@PjP@P[PjD4S0@10@SS0AP@Pj10@2PjFARsC1S0B10@IRtP@P@P@PjP@PYPjD4Ru10@NRvP@PjP@PaPjD4RwC110@MS0CP@P@PjP@P]PjD4Rx10@US0DP@PjP@P4PjD4S0EC1FAF6P6%::#=#;#5#5#5#5#5#:#?,7?RyP7PbP0PcF2Rz%G@R{%Wh;3b%c8R|1J=h%VzRz3318{bS0FPzP|P|%?<R<,7?Rzg00jPS0G%;;S0H#?R;1BA;5@A1BAD9@AD%=:#:#ER;1B;D7@DRhCaS0IPEPHPIPJPKPLPMPePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1P2P3P4MODS0JP5PgP6PbDT3S=R=7,QcA3|07X3|S0KP@g00k<R}1_;hR~'HS0LP@P@P@P@P@PoQ0=PjPnQ0<F6PmQ0;10@GS0MP@P@P@PjQ03PjC1S03PkQ04C1S0NPlQ08C1S0OF6RkPbP@P@P@P@PjQ0DPjC1S0PQ0CPxPtP@PuP@PQPwD4S0QF6Rw10@ERuP@P@PpP@P0PqPrPsG>FAS0RP4AP?gzS0SP5PbP6PcF2=<|7X0@P@1Lf<,7?RoP@PkPbP@PwPuP@P@PpP@Q0LPqPrPsG>FAP4P0P5PbP6PcF2=<|7X0@P@PNP@PkPbP@PwPuP@P@PpP@1H0~PqPrPsG>FAP4PoP5PbP6PcF2=<|7X0@P@1LD~,7?Q0RP4PoP5PbP6PcF2=<|7X0@P@P@P@P@P@Q0EQ0DPjC1Q0CPxPtQ0QF6RoPuQ0BPbP@Q0OPmP@P@Q09PvQ0:C1PnQ0>FAF6P5PyP6PbP7PcF^,8|1]?N/L~,7?1tD~E9P}g00kaE9Q0S1sf<E9Q0GAr;?hS0S7q}Ap};hE9Q0JP5PgP6PbP7PcF2,J=P=Q0JP5PgP6PbP7PcQ0H#:#=#:#5#?R}1B>}5@>R}Q0IP<%GBRf10B}Rs'81Z=g=3fsdg00baRsg00cARg'8S0H%Y}=3sgdg00caRq/mCRp#GRwPqPCQ0IP<CX,0pRk'8%U}=3wkdM>[E9b2CKP@p-1Po%i@RoQ0OPoP@P@P@P@PjQ0=PjC1PnQ0<PmQ0;F6S0;Q0MP@P@Q03PvQ04C1PlQ08FAPoP=fVRoPdPFPGPEPHPIPJPKPNPMPePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaMODP1%IoRMP2PbP3PcF29380fWRm=39m/Ci'CX18S08P5P5P6P5PdP7PbP0G>RnP2PyP3PbP4PcF2RkPnP2%IdRnP3PbP4PcF2R}%Wk=3{b1J=k%V}R}53|Q0FP}P|P|Q00#:R}#?,BA9@AD%?:R:1BA:5@A;hhRAP4P4P5P4PoP6PbP7G>RkP1PyP2PbDT5Sz=R=3,QcQ0KP@1Ho~P3P3P4P3PmP5PbP6G>R5Pag00aFRz,O?9F?0P1PbP2PcF2=<|7X0@P@17?:R:P5Pa1Hm~1O?05F?P1PbP2PcF2=<|7X0@PC1]?oRmP5Pa17?01O?:R:5F?P1PbP2PcF2=<|7X\CP@PoP5PaAF?0:P1PbP2PcF2=<|7X0@P@PMP5PaP0P1PbP2PcF2=<|7X0@PkP1PMP2PbP3PcF^,8|AF?o:%goE917?m%foE91LmD%jmE9Pzg00akE9Q0S9P?oAko;hE9PkP1PyP2PbP3PcF2,J=P=PkP1PyP2PbP3Pc%5}#:#=#5#?R}1B>}5@>R>PAP<10B>RB,8f1Z=y=3fBdQ0H%Y>=3sgdPqPCPAP<CX,0pRp,8w%U>=3wpdM>[E9b2CKP=Q08P@P@P@P@P@Q07Q06PjC1PlQ05Q0MQ0NF6P@PdQ0;PbP@P@P@P@PjQ0APjPrQ0@F6PuQ0?10@FP@P@Q0PPvPxPtQ0QF6F6G>P2PnP3PbP4PcF2RtPdPFPGPEPHPIPJPKPLPNPePOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaP1MODP2PnP3PbP4PcF2R4938tA39ooRt/Ci1884PtPi189o18CDCKCKCeE\b@b?b>b=E\GoP9P=PCg00lWPEQ01Q02P6g00mQ,7?P7PbP0PcF2FdeW3WAW4XZ@XY@XX@XW@XJ@XI@XR@XQ@XP@XO@XN@XM@XL@XK@X<@X;@X:@X9@X8@X7@X6@X5@XH@XG@XV@XU@XT@X[@XB@XS@WDWEo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition trun_cells0 (m : mem) : Prop :=
  rw_cells psegs m PINIT_FLAG [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m PGOT_FUZZ_INIT [C8 (wz PFUZZ_INIT)]
  /\ rw_cells psegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
  /\ rw_cells psegs m PSTDERR_PTR [C8 (wz RSTDERR)]
  /\ atx_state false m.

(* [comment removed for export] *)
Definition pstdout_ivs : list (Z * Z) :=
  [(0x275e0, 0x275e0 + 232); (0x57f08, 0x57f08 + 1024); (PINIT_FLAG, PINIT_FLAG + 1);
   (PAEF_INCB, PAEF_INCB + 1); (0x57880, 0x57884); (0x57888, 0x57890); (0x57898, 0x578a0); (0x57998, 0x579a0)].

Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
  match ivs with [] => False | (lo, hi) :: ivs' => (lo <= a < hi) \/ rin_ivs ivs' a end.

(* [comment removed for export] *)
Definition pdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ rin_ivs pstdout_ivs a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

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
  magree psegs (fun a => rclient_addr LB SP a /\ ~ rin_ivs pstdout_ivs a) m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_iface ()) ["CANSEC1"] "h01ah11Hh22H0h32Hah42Hch52Hxh62LBh72SPh81mh92m'p;1p;4p;2p;3g00n]j1BTg006hj10Tg007Mj17Tg007kj16Tg0093j1ATg014\j4@Tg00o=j2=Tg00>?j18Tg00oYj2<Tg0106j2;Tg00=dR0j23Tg010Rj34Tg011Wj22Tg012Wj11Tg0130j1:Tg00=Jj35Tg013_j39Tg00;=j1?Tg01:;j4>Tg015^#Bg00]7R1g00^N#0R2#0#0R3#0#0#0R4#7#6%73#6R3#AR5[R6f3R7f2R8f1R9f0R:C@g00`h/=:%82%84'<,;:'3f6R4f5R2;49g016\R;/29#1'3P0f7R0?44812;8#1P2%:7R7O1P4P7O1555g00_3R<?947%?3R3555#1f4R7#:99<4=553#1['3P:f9f8;4712;2#1P0P4P2P9P:O4W5W4P9P:O2n2001000000120000000W2W3X01P<A427:12;:#1'3X01P8P9C>eW1X96W8W7W6o"). Qed.

(* [comment removed for export] *)
Definition ptarget_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (AB lo : Z) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ 0 <= r <= 2
    /\ mem_inv psegs m' /\ frm0 fc' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
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
  bytes_at psegs m A (zbytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  trun_cells0 m -> stderr_file0 m ->
  rauxv_ok m AB -> bv_unsigned sp <= AB -> AB <= 2^47 ->          (* [comment removed for export] *)
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PTARGET_RUN_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m -> frm0 fc ->
  stdout_file m (ps_so s) ->
  tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implM psegs (Prog.run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (ptarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz PTARGET_RUN) fc None m (seg_rom psegs)).
End CANSEC1.
