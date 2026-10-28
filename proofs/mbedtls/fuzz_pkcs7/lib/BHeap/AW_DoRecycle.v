(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_CbRecycle AW_LCDealloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001503edf0b5b4d1 0 2 0 1 30 1P0042b4dd5a5994c9 0 2 0 1 29 1P025be275480441a9 0 2 0 1 29 1P02bf69f41f60585e 0 2 0 1 29 1P0375ffc62999a6c3 0 2 0 1 29 1P045b1c4f1374bfc0 0 2 0 1 33 1P053ba8c6cb4300b6 0 2 0 1 29 1P05cb5cb4c849b1e4 0 2 0 1 29 1P07564635f1b3381c 0 2 0 1 30 1P07b85a74a6b5f718 0 2 0 1 29 1P084bf89cf352b8ae 0 2 0 1 29 1P0b32c2eb6d082436 0 2 0 1 29 1P0b3740b4cce862c7 0 2 0 1 30 1P0bc68c23fc3490b2 0 2 0 1 29 1P0beff881274da586 0 2 0 1 29 1P0c6e45f1a0d3d386 0 2 0 1 33 1P0d4389aab3e45ae8 0 2 0 1 17 1P0dbc03f06bc31354 0 2 0 1 29 1P108ec9277621e0a0 0 2 0 1 30 1P10c7aa49cbd584e3 0 2 0 1 29 1P13c956e81871d17a 0 2 0 1 33 1P14f365738119693d 0 2 0 1 29 1P151ef8a12ca965a3 0 2 0 1 33 1P16479751d810413f 0 2 0 1 29 1P16f2a56e1e06eecb 0 2 0 1 29 1P1853429dcaa08dc6 0 2 0 1 33 1P18fd1efc7ca4a153 0 2 0 1 33 1P19cd01b2c444baf8 0 2 0 1 30 1P1a6e11d7c10ef3bb 0 2 0 1 29 1P1ae3be2661291aed 0 2 0 1 33 1P1bced992da4582bf 0 2 0 1 33 1P1cd3c2daf3b81a42 0 2 0 1 33 1P1e546abd5921a5f6 0 2 0 1 29 1P1e7acd38aa10e24c 0 2 0 1 33 1P1ed2320f25632607 0 2 0 1 33 1P1fa013f3977cafbf 0 2 0 1 17 1P2062dbad34ae1dbb 0 2 0 1 16 1P213c1137ea382d5a 0 2 0 1 29 1P21556498b04fbf45 0 2 0 1 29 1P224bc7e39feca74f 0 2 0 1 30 1P228350ff3ccda304 0 2 0 1 29 1P25558881a1c4c560 0 2 0 1 30 1P2630c8ac48619b9e 0 2 0 1 29 1P28a71f7d46c0f2fc 0 2 0 1 33 1P28b3ab616d1de002 0 2 0 1 29 1P28ed25e98d3a80ea 0 2 0 1 29 1P29110a4d7cf280a8 0 2 0 1 29 1P2b3dadf2949433e3 0 2 0 1 29 1P2c3fa2a1fe51fe01 0 2 0 1 30 1P2d99cacee705d896 0 2 0 1 30 1P2dc35b9f8ee9e8c9 0 2 0 1 29 1P3058ae9782156a02 0 2 0 1 29 1P314f347e1d7f37cd 0 2 0 1 29 1P31aac5032b7959aa 0 2 0 1 30 1P32939f1165f56569 0 2 0 1 17 1P32c611b1d96bfca7 0 2 0 1 29 1P338607edcec603e5 0 2 0 1 16 1P33c162dd1886b992 0 2 0 1 29 1P34398f73657d9e3b 0 2 0 1 29 1P3509e3920c665657 0 2 0 1 29 1P3557095e799c8306 0 2 0 1 29 1P35795a40d9ffe3ad 0 2 0 1 29 1P361d7c64c2ea7ba9 0 2 0 1 29 1P3695dd4f2304452e 0 2 0 1 29 1P36c6217522be8259 0 2 0 1 33 1P37642dec20380f28 0 2 0 1 30 1P39617d40df5291cc 0 2 0 1 30 1P3b599843ca5c2874 0 2 0 1 29 1P3c9cfe34c8c58d68 0 2 0 1 29 1P3e6fc02e507e8504 0 2 0 1 29 1N0154d85a670f30fdN05b34d16013f2be5N093b17479bb0ec1cN1c9bbdbd615942b9N2a90d40ea92fac7dN3614481e9b48e905N3cd4d344405cd6d3"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DoRecycle () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.qc_cells"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.DoRecycle.dr_regs"; "ARUN_1.A_DR_HEAD"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.DoRecycle.dr_frame"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_DORECYCLE"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "ARUN_1.A_DR_INNER"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_CB_RECYCLE"; "ARUN_1.A_DR_TAIL"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SPACEBEG_CELL"; "ARUN_1.A_DR_BACK"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_LC_DEALLOC"].

Section ARUN_1. Context {hAR : arun}.
Definition A_DORECYCLE : Z := 0x49a88.       (* [comment removed for export] *)
Definition A_DR_HEAD : Z := 0x49b00.         (* [comment removed for export] *)
Definition A_DR_INNER : Z := 0x49b4c.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DR_TAIL : Z := 0x49b58.         (* [comment removed for export] *)
Definition A_DR_BACK : Z := 0x49b84.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LARGE_DEALLOC : Z := 0x4a18c.   (* [comment removed for export] *)

Section DoRecycle.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition dr_frame (m : mem) (SP T STK : Z) (j0 : list byte) (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DoRecycle ()) "(0.$1.O10.(2.O?.-70.)(3.$4.(5.#8.O<.)(3.$4.(6.(7.&40.(2.O>.+=0.)))(3.$4.(6.(7.&40.O=.))(3.$4.(6.O;.)(3.$4.(6.O:.)(3.$4.(6.O9.)(3.$4.(6.O8.)(3.$4.(6.O7.)(3.$4.(6.O6.)(3.$4.(6.O5.)(3.$4.(6.O4.)(3.$4.(6.O3.)(3.$4.(6.O2.)(3.$4.(6.O1.)(8.$4.))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition dr_regs (SP : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (C : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_DoRecycle ()) "(9.O1:.(7.&40.(2.O1;.-70.))O19.O18.O17.O16.O15.(7.&40.O1.)(7.&40.$:.)O14.O13.O12.O11.O10.O?.O>.O=.(7.&40.(2.$:.+40.))(7.&40.(2.$:.+2;0.))O<.(7.&40.+2000000000.)O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L2017701605.61 L24905121097.75L30126384741.60L48751849838.1 L51666185338.2 L62775105363.6000000<00D00S00W00X00gS3hAR3len2H3S3hAR2SPS3hAR3len2LB2H2S2SPFS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  Lemma dr_entry : ltac2:(CDefT.buildp (gd_tbl_AW_DoRecycle ()) "Pra,(;.&40.)Pgp,(;.&40.)Ptp,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Ps0,(;.&40.)Ps1,(;.&40.)Pa0,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Ps2,(;.&40.)Ps3,(;.&40.)Ps4,(;.&40.)Ps5,(;.&40.)Ps6,(;.&40.)Ps7,(;.&40.)Ps8,(;.&40.)Ps9,(;.&40.)Ps10,(;.&40.)Ps11,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)PSP,$<.PC,$<.PT,$<.PSTK,$<.Plen,$<.Pfirst,$<.Plast,$<.Pbytes,$<.Plo,$<.PF,(=.&5.(;.&40.))Pfc,(;.&20.)Pm,P,(;.&40.)(>.(;.&8.))P,(?.(10.=R8.)(11.R8.(12.+2.+3?.)))P,(?.(10.+1000.R;.)(13.(10.(2.R;.+1000.)+10000.)(10.+65?000.R;.)))P,(10.(2.R<.+1000.)(12.+2.+2?.))P,(?.(10.=R<.)(11.R<.(12.+2.+40.)))P,(10.R10.R?.)P,(10.(2.R10.+20.)(12.+2.+3>.))P,(0.$1.R7.R11.(14.R>.R=.R<.R;.))P,(15.VCS,R12.+20.)P,(16.$1.R9.R<.R14.)P,(10.(17.VhAR,)R=.)P,(10.R>.(18.R16.+70.))P,(10.R17.(12.+2.+3>.))P,(15.VCS,R10.(18.R18.R10.))P,(19.$1.R>.)(1:.$1.VAL,VCS,Lms',$1;.(1<.P,(;.&40.)(>.(;.&8.))Lm',P,(;.&40.)(>.(;.&8.))(1<.(1=.(;.&8.))Lj0,(1=.(;.&8.))(?.(1>.(3.(1?.$<.$<.)(20.$<.$<.R15.R1=.)(8.(1?.$<.$<.)))R12.R2.)(?.(21.$1.R12.R2.)(?.(19.$1.R2.)(?.(0.$1.R2.R1<.(14.R19.R18.R17.R16.))(13.(?.(22.(23.$<.R19.=))(1<.(;.&40.)La1',(;.&40.)(?.(23.$1;.R4.(24.(25.R1>.R39.R38.R37.R36.R35.R34.(7.&40.R1:.)R1.(7.&40.(2.R1<.+=0.))(7.&40.R1;.)R30.R2?.R2>.R2=.R2:.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1=.)R15.(7.&40.$26.)R14.(27.(;.&40.))R3.(28.$1.)))(?.(29.R3.R1>.R1<.R1;.R2.R25.R26.R27.R28.R29.R2:.R2;.R2<.R32.R33.R39.)(16.$1.R3.R16.(2.R1>.-70.))))))(?.(23.$<.R19.=)(1<.(;.&40.)La1',(;.&40.)(1<.(;.&40.)La2',(;.&40.)(1<.(;.&40.)La3',(;.&40.)(?.(23.$1;.R6.(24.(9.R3;.(7.&40.R20.)R3:.R39.R38.R37.R36.R35.R34.(7.&40.R1<.)R3.R2.R1.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R17.(2:.R3;.)R16.(27.(;.&40.))R5.(28.$1.)))(16.$1.R5.R18.R20.)))))))))))))(24.(9.R35.(7.&40.R1:.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(7.&40.R19.)(7.&40.(2.R18.+=0.))(7.&40.R17.)R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R11.(7.&40.$2;.)R10.(27.(;.&40.))R?.(28.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP C T STK len first last bytes lo F fc m
      LB TB1 TB2 STKB C0 C1 QC CCS ST LOIMG SPL SPH SCS MI.
    facts. unfold qc_cells in *. unfold A_DORECYCLE, A_DR_HEAD, A_INSTANCE in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lx_aceil.
    lx_run (PLAN [0x49b00] [] 40%N); try clear LXlen;
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx, QCl : rw_cells _ ?mx C _ |- _ =>
        apply evtA_done; exists mx;
        first [ (* [comment removed for export] *)
                lazymatch goal with STl : stk _ mx lo (SP + -104) |- _ =>
                  lx_carve STl 8%nat ST2 FRj j0; replace (SP + -104 - Z.of_nat 8) with (SP + -112) in ST2, FRj by (clear; lia);
                  lazymatch goal with FRl : rw_cells _ mx (SP + -104) _ |- _ => chunk_join FRj FRl FRf end;
                  exists j0; split; [exact MUl|]; split; [exact WMl|]; split; [assumption|]; split; [exact QCl|];
                  left; split; [lx_arith|]; eexists; split; [unfold dr_regs, A_INSTANCE; lx_mseq|]; split; [unfold dr_frame; exact FRf| exact ST2] end
              | (* [comment removed for export] *)
                exists (@nil byte); split; [exact MUl|]; split; [exact WMl|]; split; [assumption|]; split; [exact QCl|];
                right; split; [lx_arith|]; do 3 eexists; split; [lx_mseq| lx_stk_grow lo; assumption] ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dr_head_post (SP : Z) (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)
      (C b len next last bytes bsize count e0 lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (m' : mem),
      munch [(lo, SP); (C, C + 32)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' C (qc_cells (len - 1) next (if next =? 0 then 0 else last) (bytes - bsize))
      /\ ( (count <> 0
            /\ ms' = MS (dr_regs SP (Z_to_bv 64 A_DR_INNER) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -104)) (Z_to_bv 64 e0) a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 b) (Z_to_bv 64 count) (Z_to_bv 64 (b + 152)) (Z_to_bv 64 (count + 16)) (Z_to_bv 64 16) s10 s11 t3 t4 t5 t6 C)
                        F (Z_to_bv 64 A_CB_RECYCLE) fc None m' (seg_rom asegs))
        \/ (count = 0
            /\ exists a0' a1' s7 s8 s9, ms' = MS (dr_regs SP ra gp tp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 b) (Z_to_bv 64 count) s7 s8 s9 s10 s11 t3 t4 t5 t6 C)
                        F (Z_to_bv 64 A_DR_TAIL) fc None m' (seg_rom asegs)) ).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L12413256317.72L13052765101.75L13606932915.72L14946898661.74L14946898661.75L15413451043.72L15936025863.72L20367057978.72L20367421905.72L20765172779.71L21779031470.72L246676609.73  L25093930540.72L26040600684.72L27807105733.72L3315943292.75 L34383400032.71L39280637297.0 L40138315632.76L40138315632.77L40380900403.71L44421369622.1 L45306793715.72L52723105533.72L52749732781.1 L52767233997.78L53399287543.76L53399287543.77L54496718319.73L59308634630.4 L60234967559.73L64193412887.74L64193412887.75L6443700185.72 L6443866674.72 L6963410614.75 L7044018604.72 L9738815618.71 00000F00\01D01f02H03003F03\04204H04^05405J05`06606L06b06c07c09:09P09U09k0:A0:D0:Z0;I0<C0<Y0<j0=B0=[0>40>J0>`0?90?O0?eS3hAR1b5count5elems2ELS3hAR1b5count2e02er2ELS3hAR5bytes5bsize5count5elems3BSB3BYB2ELS3hAR1C5count5elems2EL2C12HB5Ha_stS3hAR1C5count5elems2EL2C12HB5Ha_stS3hAR5bytes5bsize5count5elems3BSB3BYB2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1b5count5elems2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1b5count2e02er2ELS3hAR1b5count5elems2ELSS3hAR2SP1C1b4next5count2lo5elems3CNT2EL2C02CB3SPL2HB5Ha_st5Hl_stS3hAR2SP1C1b3len4next5count2lo5elems3NXB3CNT2EL2C02CB3SPL2Kn2HB5Ha_st5Hl_st5bytes5bsizeS3hAR1b5count5elems2ELS3lenS3hAR1b5count5elems2ELS3hAR1b5count5elems2ELS1bS3hAR1b5count2e02er2ELS3hAR1C1b4next5count5elems2EL2CB2HB5Ha_st5Hl_stS3hAR1C1b3len5count5elems2EL2CB2HB5Ha_st5Hl_st5bytes5bsizeS3hAR1C5count5elems2ELS5count3CNT2EL2KcS3hAR5count5elems3CNT2ELS3hAR1C5count5elems2EL2HBS3hAR1C5count5elems2EL2HBS3hAR1C5count5elems2ELS3hAR1C5count5elems2ELS3hAR1C5count5elems2EL2HBS3hAR1b5count5elems2ELS3hAR1C5count5elems2EL". (* [comment removed for export] *)
  Lemma dr_head : forall
      (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP C b len next last bytes bsize count lo : Z) (elems : list word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem),
      1 <= len < 2^63 -> 0 <= next < 2^64 -> 0 <= last < 2^64 -> 0 <= bsize <= bytes -> bytes < 2^63 ->
      0x65f000 <= b -> b + 8192 <= 2^47 -> 0 <= count <= 1021 -> length elems = Z.to_nat count ->
      SP <= C -> C + 32 <= 2^62 -> (C + 32 <= b \/ b + 8192 <= C) ->
      rw_cells asegs m C (qc_cells len b last bytes) -> crange CS C 32 ->
      rw_cells asegs m b (batch_hdr next bsize count) -> u64arr asegs m (b + 24) elems -> crange CS b 8192 ->
      ACEIL <= lo -> lo <= SP - 112 -> SP <= 2^62 -> (SP <= b \/ b + 8192 <= lo) ->
      munch [(lo, SP); (C, C + 32)] m0 m -> wmono asegs m0 m -> mem_inv asegs m -> crange CS lo (SP - lo) ->
      evtA asegs AL CS (dr_head_post SP ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 C b len next last bytes bsize count
                          (match elems with [] => 0 | e :: _ => bv_unsigned e end) lo F fc m0)
        (MS (dr_regs SP ra gp tp t0 t1 t2 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 C)
            F (Z_to_bv 64 A_DR_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP C b len next last bytes bsize count lo elems F fc m0 m
      LB NXB LAB BSB BYB B0 B1 CNT EL C0 C1 CB QC CCS BH BE BCS LOIMG SPL SPH SEP MU WM MI SCS.
    facts. unfold qc_cells, batch_hdr, dr_regs in *. unfold A_DR_HEAD, A_DR_INNER, A_DR_TAIL, A_CB_RECYCLE, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases Kn; zify_cond Kn.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases Kc; zify_cond Kc.
      + (* [comment removed for export] *)
        apply evtA_done; unfold dr_head_post; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [replace (next =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kn); replace (len - 1) with (len + -1) by (clear; lia); assumption|right; split; [exact Kc| do 5 eexists; unfold dr_regs, A_INSTANCE; reflexivity]].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        destruct elems as [|e0 er]; [exfalso; cbn in EL; clear -EL Kc CNT; lia|].
        pose proof (u64arr_read asegs _ (b + 24) (e0 :: er) 0 e0 _ BE eq_refl ltac:(clear; lia) eq_refl) as RD.
        replace (b + 24 + 8 * 0) with (b + 152 + -128) in RD by (clear; lia).
        zstep. clear RD. zstep. zstep.
        apply evtA_done; unfold dr_head_post; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [replace (next =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kn); replace (len - 1) with (len + -1) by (clear; lia); assumption|left; split; [exact Kc| unfold dr_regs, A_INSTANCE; rewrite Z_to_bv_bv_unsigned; reflexivity]].
    - (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases Kc; zify_cond Kc.
      + (* [comment removed for export] *)
        apply evtA_done; unfold dr_head_post; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [subst next; cbn [Z.eqb]; replace (len - 1) with (len + -1) by (clear; lia); assumption|right; split; [exact Kc| do 5 eexists; unfold dr_regs, A_INSTANCE; reflexivity]].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        destruct elems as [|e0 er]; [exfalso; cbn in EL; clear -EL Kc CNT; lia|].
        pose proof (u64arr_read asegs _ (b + 24) (e0 :: er) 0 e0 _ BE eq_refl ltac:(clear; lia) eq_refl) as RD.
        replace (b + 24 + 8 * 0) with (b + 152 + -128) in RD by (clear; lia).
        zstep. clear RD. zstep. zstep.
        apply evtA_done; unfold dr_head_post; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [subst next; cbn [Z.eqb]; replace (len - 1) with (len + -1) by (clear; lia); assumption|left; split; [exact Kc| unfold dr_regs, A_INSTANCE; rewrite Z_to_bv_bv_unsigned; reflexivity]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L16784074066.50L17641792336.2 L19622189599.47L20650380073.5 L31686075875.47L37111212091.1 L41249998872.3 L45518918144.50L47804990688.51L48579347943.5 L55696874086.2 L59310648043.7 00000M00R00k01901R01U01a02802L02Z02_03:S1b5count1i5elems2IB3CNT2EL1KS1b1iS5count1i5elems2IB3CNT2ELS5count1i2IB1KS5count1i5elems2IB3CNT2ELS1iS5count1i2IBS1b5count1i5elems2IB2ELS1b5count1i5elems2ELS5count1i2IB1KS1b1iS5count1i5elems2IB2EL1K3NTH". (* [comment removed for export] *)
  Lemma dr_inner_next : ltac2:(CDefT.buildp (gd_tbl_AW_DoRecycle ()) "Pra,(;.&40.)Pgp,(;.&40.)Ptp,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Ps10,(;.&40.)Ps11,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)PSP,$<.PC,$<.Pb,$<.Pcount,$<.Pi,$<.Pelems,(1=.(;.&40.))PF,(=.&5.(;.&40.))Pfc,(;.&20.)Pm,P,(;.&40.)(>.(;.&8.))P,(10.+65?000.R7.)P,(10.(2.R8.+2000.)(12.+2.+2?.))P,(?.(10.=R7.)(11.R7.R8.))P,(10.R9.+3?=.)P,(23.$2<.(2=.(;.&40.)R8.)(2>.R:.))P,(2?.$1.R6.(2.R<.+18.)R9.)P,(15.VCS,R=.+2000.)P,(19.$1.R8.)(1:.$1.VAL,VCS,Lms',$1;.(13.(?.(11.(2.R>.+1.)R?.)(1<.(;.&40.)Le,(;.&40.)(?.(23.(>.(;.&40.))(30.(;.&40.)R>.(2>.(2.R?.+1.)))(31.(;.&40.)R1.))(23.$1;.R2.(24.(25.R13.(7.&40.$32.)R26.R25.R24.R23.R22.(7.&40.(2.R13.-68.))R1.R1?.R1>.R1=.R1<.R1;.R1:.(7.&40.R11.)(7.&40.R10.)(7.&40.(2.(2.R11.+98.)(33.+8.(2.R?.+1.))))(7.&40.(2.R10.+10.))(7.&40.(2.+10.(2.R?.+1.)))R19.R18.R17.R16.R15.R14.R12.)R=.(7.&40.$34.)R<.(27.(;.&40.))R;.(28.$1.))))))(?.(23.$<.(2.R>.+1.)R?.)(23.$1;.R1.(24.(25.R12.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(7.&40.R10.)(7.&40.R?.)(7.&40.(2.(2.R10.+98.)(33.+8.(2.R>.+1.))))(7.&40.(2.R?.+10.))(7.&40.(2.+10.(2.R>.+1.)))R18.R17.R16.R15.R14.R13.R11.)R<.(7.&40.$35.)R;.(27.(;.&40.))R:.(28.$1.)))))(24.(25.R11.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(7.&40.R?.)(7.&40.R>.)(7.&40.(2.(2.R?.+98.)(33.+8.R=.)))(7.&40.(2.R>.+10.))(7.&40.(2.+10.R=.))R17.R16.R15.R14.R13.R12.R10.)R;.(7.&40.$32.)R:.(27.(;.&40.))R9.(28.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 SP C b count i elems F fc m
      B0 B1 IB CNT EL BE BCS MI.
    facts. unfold dr_regs in *. unfold A_DR_INNER, A_DR_TAIL, A_CB_RECYCLE, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct (nth_error elems (Z.to_nat (i + 1))) as [e|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear -NTH EL IB K; lia].
      pose proof (u64arr_read asegs _ (b + 24) elems (i + 1) e _ BE NTH ltac:(clear -IB; lia) eq_refl) as RD.
      replace (b + 24 + 8 * (i + 1)) with (b + 152 + 8 * i + 8 + -128) in RD by (clear; lia).
      zstep. clear RD. zstep. zstep.
      apply evtA_done. left. split; [clear -K IB CNT; lia|]. exists e. split; [first [exact NTH | reflexivity]|].
      replace (b + 152 + 8 * i + 8) with (b + 152 + 8 * (i + 1)) by (clear; lia). replace (16 + i + 1) with (16 + (i + 1)) by (clear; lia).
      reflexivity.
    - apply evtA_done. right. split; [clear -K IB CNT; lia|].
      replace (b + 152 + 8 * i + 8) with (b + 152 + 8 * (i + 1)) by (clear; lia). replace (16 + i + 1) with (16 + (i + 1)) by (clear; lia).
      reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L15615277569.72L15615277696.73L19820535456.71L22414783254.73L33392944668.73L33697876151.71L36717278177.2 L38797662903.71L43119416129.73L45332959566.74L48193359348.73L53534663706.71L58128026272.73L58931694336.73L58931694465.72L59308628304.7 L59308628433.7 L60599954521.2 L60748045565.71L754545169.2   00000@00P00Q00`01001501<01I01T01\01l02:02;02Z03603I03\03]03j042S3hAR2SB3SB03SB1S3hAR2SB3SB03SB1FS3hAR2SP2lo3SPLS3hAR2SB1b2K12K2S3hARS2SB2ckS3hAR2AL4IMG'S3hAR2SP2loS3hAR2SPS3hAR2SB3SB03SB1S3hAR2AL5ALWF'FS3hAR2SB1b2ck3SB03SB12HB3CKB2K1S3hAR2SB1b2ck3SB03SB12HB3CKBS2SB1b2ck2HB3CKB2K1S2SB1b2ck2HB3CKB2K2SS3hAR2AL4IMG'S2ck3CKB". (* [comment removed for export] *)
  Lemma dr_tail : ltac2:(CDefT.buildp (gd_tbl_AW_DoRecycle ()) "Pra,(;.&40.)Pgp,(;.&40.)Ptp,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Ps6,(;.&40.)Ps7,(;.&40.)Ps8,(;.&40.)Ps9,(;.&40.)Ps10,(;.&40.)Ps11,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Pq9,(;.&40.)Pq8,(;.&40.)Pq7,(;.&40.)Pq6,(;.&40.)Pq5,(;.&40.)Pq4,(;.&40.)Pq3,(;.&40.)Pq2,(;.&40.)Pq1,(;.&40.)Pq0,(;.&40.)Pqra,(;.&40.)PSP,$<.PC,$<.PT,$<.PSTK,$<.PSB,$<.Pb,$<.Pck,$<.Plo,$<.Pj0,(1=.(;.&8.))PF,(=.&5.(;.&40.))Pfc,(;.&20.)Pm,P,(;.&40.)(>.(;.&8.))P,(10.+10007???9000.R8.)P,(10.(2.R9.+2000001000.)(12.+2.+2?.))P,(23.$<.R9.(2.(2.R:.+1800000000.)(33.+10.R8.)))P,(?.(10.=R9.)(11.R9.+10000000.))P,(?.(10.+1000.R>.)(13.(10.(2.R>.+1000.)+10000.)(10.+65?000.R>.)))P,(10.(2.R?.+1000.)(12.+2.+2?.))P,(?.(10.=R?.)(11.R?.(12.+2.+40.)))P,(36.$1.R8.$37.(3.$4.(6.(7.&40.R?.))(8.$4.)))P,(29.R9.R14.R12.R11.R<.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,(16.$1.R:.R>.(2.R15.-70.))P,(10.(17.VhAR,)R?.)P,(10.R10.(18.R17.+70.))P,(10.R18.(12.+2.+3>.))P,(15.VCS,R12.(18.R19.R12.))P,(19.$1.R?.)(1:.$1.VAL,VCS,Lms',$1;.(1<.(;.&40.)La0',(;.&40.)(1<.(;.&40.)La1',(;.&40.)(?.(23.$1;.R3.(24.(25.R1>.(7.&40.$38.)R40.R3?.R3>.R3=.R3<.(7.&40.(2.R1<.+=0.))(7.&40.$:.)(7.&40.+18.)(7.&40.R19.)R37.R36.R35.R34.(7.&40.R19.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R1=.)R15.(7.&40.$39.)R14.(27.(;.&40.))R13.(28.$1.)))(?.(23.(;.&40.)R2.R3;.)(23.(;.&40.)R1.R3:.)))))(24.(25.R1;.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.(7.&40.R16.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R1:.)R12.(7.&40.$35.)R11.(27.(;.&40.))R10.(28.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra SP C T STK SB b ck lo j0 F fc m
      SB0 SB1 HB CKB TB1 TB2 STKB SBC FR ST LOIMG SPL SPH SCS MI.
    facts. unfold dr_regs, dr_frame in *. unfold A_DR_TAIL, A_DR_BACK, A_LC_DEALLOC, A_SPACEBEG_CELL, A_INSTANCE in *.
    change (1074072 + 32) with 1074104 in SBC.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 HB SB0 CKB. lia. }
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 HB SB0 CKB. lia. }
    zstep. zstep. zstep. zstep.
    replace (b - SB) with (24 * 4294967296 + 16 * ck) by (rewrite HB; clear; lia).
    rewrite (shl27_shr59 24 (16 * ck)) by (clear -CKB; lia).
    zstep. zstep. zstep.
    apply evtA_done. do 2 eexists. split; [reflexivity| split; reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00X0?L11537341518.75L13006078974.74L13894031273.74L14363224526.75L1683193161.73 L16894925182.74L1857745065.74 L19514985214.74L20354867734.73L2241202446.1  L246676609.74  L25239275390.74L25930443433.74L26101742542.75L28440133161.74L30043635022.75L31368485710.75L31949773865.74L33020233214.74L35434159870.74L37968691625.74L39993858558.74L40476415273.74L46495729321.74L47442874190.75L48242093646.75L49692409214.74L52513089577.74L55923285198.75L57248070350.75L58532158889.74L61015804158.74L64557895465.74L6456412661.73 L65127317551.74L6567309950.74 L67182558334.74L67431634894.75L67955980878.75L7876665897.74 00000800C00R00Z00b00m01<01G01N01R01Y01d02302;02J02R02Z02i03403?03N03Y03h04704?04G04R04a04i05105@05K05Z05a05m06806C06K06S06bS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR1CS2SPS3hAR1CS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR1CS3hAR3len2LBS3hAR2SP2loS3hAR2SP2loS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  Lemma dr_back : ltac2:(CDefT.buildp (gd_tbl_AW_DoRecycle ()) "Pgp,(;.&40.)Ptp,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Ps4,(;.&40.)Ps6,(;.&40.)Ps7,(;.&40.)Ps8,(;.&40.)Ps9,(;.&40.)Ps10,(;.&40.)Ps11,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Pq9,(;.&40.)Pq8,(;.&40.)Pq7,(;.&40.)Pq6,(;.&40.)Pq5,(;.&40.)Pq4,(;.&40.)Pq3,(;.&40.)Pq2,(;.&40.)Pq1,(;.&40.)Pq0,(;.&40.)Pqra,(;.&40.)PSP,$<.PC,$<.PT,$<.PSTK,$<.Plen,$<.Pfirst,$<.Plast,$<.Pbytes,$<.Plo,$<.Pj0,(1=.(;.&8.))PF,(=.&5.(;.&40.))Pfc,(;.&20.)Pm0,P,(;.&40.)(>.(;.&8.))Pm,P,(;.&40.)(>.(;.&8.))PW,(1=.(1?.$<.$<.))P,(?.(10.=R;.)(11.R;.(12.+2.+3?.)))P,(10.R10.R?.)P,(10.(2.R10.+20.)(12.+2.+3>.))P,(0.$1.R5.R11.(14.R>.R=.R<.R;.))P,(15.VCS,R12.+20.)P,(29.R7.R14.R12.R11.R;.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,(16.$1.R8.R=.(2.R15.-70.))P,(10.(17.VhAR,)R>.)P,(10.R?.(18.R17.+70.))P,(10.R18.(12.+2.+3>.))P,(1>.(3.(1?.$<.$<.)(20.$<.$<.R11.R19.)R;.)R=.R<.)P,(21.$1.R>.R=.)P,(19.$1.R>.)P,(15.VCS,R14.(18.R1<.R14.))(1:.$1.VAL,VCS,Lms',$1;.(13.(?.(22.(23.$<.R1:.=))(23.$1;.R1.(24.(25.R1>.(7.&40.$38.)R41.R40.R3?.R3>.R3=.(7.&40.R1:.)R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R1=.)R14.(7.&40.$26.)R13.(27.(;.&40.))R11.(28.$1.))))(?.(23.$<.R1:.=)(1<.P,(;.&40.)(>.(;.&8.))Lm',P,(;.&40.)(>.(;.&8.))(?.(23.$1;.R2.(24.(9.R20.(7.&40.R1?.)R42.R41.R40.R3?.R3>.R21.R22.(7.&40.R1;.)R3<.R3;.R3:.R39.R38.R37.R36.R23.R24.R25.R26.R27.R28.R29.R2:.R30.R2?.R2>.R2=.R2<.R2;.)R15.(2:.R20.)R14.(27.(;.&40.))R1.(28.$1.)))(?.(1>.(3.(1?.$<.$<.)(20.$<.$<.R17.R1?.)R11.)R13.R1.)(?.(21.$1.R13.R1.)(?.(19.$1.R1.)(?.(0.$1.R1.R1>.(14.R1;.R1:.R19.R18.))(16.$1.R1.R17.R1?.)))))))))(24.(25.R1=.(7.&40.$38.)R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R1<.)R13.(7.&40.$38.)R12.(27.(;.&40.))R10.(28.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra SP C T STK len first last bytes lo j0 F fc m0 m W
      LB C0 C1 QC CCS FR ST LOIMG SPL SPH MU WM MI SCS.
    facts. unfold dr_regs, dr_frame, qc_cells in *. unfold A_DR_BACK, A_DR_HEAD, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    - apply evtA_done. left. split; [exact K| reflexivity].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. replace (SP + -112 + 112) with SP by (clear; lia). zstep.
      release_frame FR ST SP.
      apply evtA_done. right. split; [exact K|]. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DoRecycle.

End ARUN_1.
