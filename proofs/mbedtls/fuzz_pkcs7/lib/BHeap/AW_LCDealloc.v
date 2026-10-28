(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_CbRecycle.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_LCDealloc () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "ARUN_1.LCDealloc.pcl_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SPACEBEG_CELL"; "ARUN_1.LCDealloc.lcd_frame"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.LCDealloc.lcd_push_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.A_LCD_PUSH"; "ARUN_1.LCDealloc.lcd_at_push"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_LC_DEALLOC"; "ARUN_1.A_LCD_BACK"; "ARUN_1.A_LC_DRAIN"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "ARUN_1.A_LCDR_BACK"; "ARUN_1.A_RTA"; "ARUN_1.LCDealloc.lcdr_frame"].

Section ARUN_1. Context {hAR : arun}.
Definition A_LCD_PUSH : Z := 0x4a008.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LC_DRAIN : Z := 0x4a358.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LCD_BACK : Z := 0x4a174.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_RTA : Z := 0x4a4fc.             (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LCDR_BACK : Z := 0x4a3bc.       (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UNMAP_OR_DIE : Z := 0x7caa8.    (* [comment removed for export] *)

Section LCDealloc.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition pcl_cells (count max : Z) (csz : Z) : list cell := [C4 (Z_to_bv 64 count); C4 (Z_to_bv 64 max); C8 (Z_to_bv 64 csz)].
  Definition lcd_frame (m : mem) (SP : Z) (s4 s3 s2 s1 s0 ra : word) : Prop :=
    rw_cells asegs m (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition lcd_push_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T PC SB c count max csz AB lo : Z) (cks : list word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Lms',$0.(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lstj,(2.&40.)(4.(5.$0.R;.(6.(7.O23.(8.&40.O24.)O22.O21.O20.O1?.O1>.O1=.O1<.R:.R9.R8.R7.R6.R5.R4.R3.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.)O3.(9.O23.)O2.(:.(2.&40.))R2.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.O5.O24.)(>.(?.$10.$10.)(11.$10.$10.O<.(12.O<.+4.))(>.(?.$10.$10.)(11.$10.$10.(12.O<.+10.)(12.O<.+50.))(>.(?.$10.$10.)(11.$10.$10.(12.O=.+:>0.)(12.O=.+:>8.))(13.(?.$10.$10.))))))O1.R2.)(4.(14.$<.O1.R2.)(4.(15.$<.R2.)(4.(16.$<.R2.O<.(17.(12.O9.+1.)O8.O7.))(4.(18.$<.R2.(12.O<.+10.)(19.(2.&40.)O4.(1:.O9.)(8.&40.(1;.(1<.O6.(12.O;.(1=.O:.+100000000.)))+10.))))(4.(16.$<.R2.(12.O=.+:>0.)(>.$1>.(1?.R1.)(13.$1>.)))(20.$<.R2.O5.O24.))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01B0?L11334691781.84L12318818630.85L12344381586.88L13377304829.84L15577069396.84L15608741202.4 L15614986785.84L1631053703.86 L16591383828.88L16898987495.84L17110585503.84L1734022996.84 L17529991960.86L17899956979.84L1862073392.84 L18939318893.84L19098184541.84L19518785127.84L19732357805.2 L19824513946.84L23342160651.84L25235475431.84L25521497955.84L25934767664.84L26438528495.85L27335347790.85L2777086687.88 L28774119925.84L29149214414.85L29888672018.86L29888672018.87L30333359328.84L30506863137.84L31411303618.88L31945707696.84L32175915186.84L3276969806.85 L33024821607.84L33693599117.84L36909564707.85L37141453475.85L37972757808.84L38692635477.0 L38793254797.84L39268637205.0 L39333131958.86L39340114894.85L41368220192.88L42303277385.84L45039154511.89L46338021298.88L47337043407.87L47717380897.84L49117839730.88L49698585326.87L49743871925.89L53522295072.84L53633640586.88L5507620028.88 L55345507429.84L561051718.87  L565325339.85  L5802316517.86 L58142605646.85L59049596677.84L60235411825.84L60735279559.84L61011739751.84L62537825409.85L63439991861.87L63463343073.84L63787280654.1 L63894104180.3 L64553829296.84L65144493349.85L65669398844.84L67178229991.84L67650878948.4 L68092512244.84L7872343728.84 L7872343728.85 L8162533873.84 00000E00n01l01m01n02B02Z03N04:04M04c05205D05_06606E06F06Y06c06d06e07807W07n08>08N09U0:20:B0;O0<\0<k0=S0>=0>T0>c0?30?F0?S0@A0@B0@Y0@Z0@o0A00AC0AS0BX0Bh0C`0DR0EH0Ec0FU0G10H>0HT0ID0IE0IW0JO0KG0K`0L00LU0M50MJ0M]0Mm0NR0Nd0Nh0O10OH0OX0P30PF0PZ0Q50QL0Qc0R2S3hAR1T3cks3CKL2Tq2TQS3hAR1T2PC1c5count3max3cks2CB3HPC3CNT3CKLS3hAR1T2PC2SB1c5count3max2AB3cks2CB3HPC3CNT4MX163CKL3AB02Tq2TQFFS5count3max3CNT4MX16S3hAR2SB3cks3CKL3SB03SB1S3hAR2SP1T2PC1c5count3max2lo3cks2CB3HPC3CNT4MX163CKLS3hAR3stj1T3csz3cks3CKL2Tq2TQ2HB5Ha_st5Hl_stS3hAR2SP2lo3cks3CKLS3hAR3csz3cks4CSZB3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKL2HBS3hAR1T2PC1c3cks2CB3HPC3CKLS3hAR2SP2lo3cks3CKL3SPLS3hAR1T3cks3CKLFS3hAR2SP2lo3cks3CKLS2PC5countFFS3hAR2SP2lo3cks3CKLS3hAR1T2SB1c2AB3cks3TB13TB23CKLS3hAR2SP2lo3cks3CKL3SPLS3hAR2PC3cks3CKLS3hAR2SP3cks3CKLS3hAR3stj2SP1T2SB1c3csz2AB2lo3cks3CKL3AB05LOIMG3SPL4SEP12HB5Ha_st5Hl_stS3hAR2SB1c2AB3cks3CKL3AB03AB1S3hAR2SP3cks3CKLS3hAR2SP1T2PC2SB1c5count3max2AB2lo3cks3TB12CB3HPC3CNT3CKL3AB05LOIMG3SPL2Tq2TQS3hAR2SP1T2PC2SB1c5count3max2AB2lo3cks3TB12CB3HPC3CNT3CKL3AB05LOIMG3SPL2Tq2TQS3hAR1T3cks3CKLS3hAR2SB1c2AB3cks2CB3CKL3SB03SB13AB03AB1S3hAR2PC2SB1c5count3max2AB3cks3CNT3CKL3AB0S3hAR2SP2lo3cks3CKL3SPLS3hAR1T3cks3CKLS3hAR2SP3cks3CKLS3hAR2SP2lo3cks3CKLS3hAR3cks3CKLS3hAR1T2PC1c5count3max3cks2CB3HPC3CNT4MX163CKLFS3hAR2SP2lo3cks3CKL3SPLSS3hAR2AL3cks3CKL4IMG'SS3hAR2PC3cks3CKL2HBS3hAR2SP3cks3CKLS3hAR2SP1T2PC1c5count2lo3cks2CB3HPC3CKL5LOIMG3SPL4SEP12HB5Ha_st5Hl_stS3hAR2SP3cks3CKLS3hAR1T2PC2SB1c5count3max2AB3cks2CB3HPC3CNT4MX163CKL3AB0S3hAR3stj1T2PC1c3csz3cks2CB3HPC3CKL2HB5Ha_st5Hl_stS3hAR1T2PC1c5count3cks2CB3HPC3CKL2Tq2TQ2HB5Ha_st5Hl_stS3hAR1T2PC1c3cks2CB3HPC3CKLS3hAR3stj1T2PC1c3csz3cks2CB3HPC3CKL2HB5Ha_st5Hl_stS3hAR1T3cks3TB23CKL2HB5Ha_stS3hAR2SP1T2PC2SB1c5count3max2AB2lo3cks2CB3HPC3CNT4MX163CKL3AB05LOIMG3SPL4SEP1S3hAR2AL3cks3CKL5ALWF'S3hAR1T2PC1c5count3cks2CB3HPC3CKL2HB5Ha_st5Hl_stFS3hAR1c3cks2CB3CKLS3hAR1T2PC1c5count3max3cks3TB22CB3HPC3CNT4MX163CKL2Tq2TQS3hAR1T2PC1c5count3max3cks3TB22CB3HPC3CNT4MX163CKL2Tq2TQS3hAR2PC3cks3CKL2HB5Ha_stS3hAR2SP3cks3CKLS3hAR2SB1c2AB3cks3CKL3SB03SB13AB03AB1S3hAR5count3max3cks3CNT4MX163CKLS3hAR2AL3cks3CKL4IMG'S3hAR2SP2lo3cks3CKLS3hAR2PC3cks3CKLS3hAR2PC5count3cks3CKL2HB5Ha_st5Hl_stS3hAR1c3cks2CB3CKLS2SPS2SB1c2ABS3hAR2SP2lo3cks3CKL3SPLS3hAR2SP3cks3CKLS3hAR1T2PC1c3cks2CB3HPC3CKLS3hAR2SP2lo3cks3CKLS5count3max3CNT4MX16S3hAR1T2PC1c3cks2CB3HPC3CKLS3hAR2SP2lo3cks3CKL3SPLS3hAR2SP2lo3cks3CKL3SPLS3hAR1T3cks3CKL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma lcd_push : ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prax,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Pstj,(2.&40.)PSP,$10.PT,$10.PPC,$10.PSB,$10.Pc,$10.Pcount,$10.Pmax,$10.Pcsz,$10.PAB,$10.Plo,$10.Pcks,(21.(2.&40.))PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))P,(4.(23.+1000.R>.)(24.(23.(12.R>.+1000.)+10000.)(23.+65?000.R>.)))P,(23.(12.R?.+1000.)(25.+2.+2?.))P,(5.$10.(26.R10.+1000.)=)P,(4.(23.+1.R>.)(23.R>.+1>.))P,(5.$10.R11.(12.(12.R12.+=0.)(1=.+50.R?.)))P,(4.(23.=R?.)(27.R?.R>.))P,(23.R?.+10.)P,(4.(23.=R?.)(27.R?.(25.+2.+20.)))P,(5.$28.(29.(2.&40.)R=.)#10.)P,(23.+10007???9000.R15.)P,(23.(12.R16.+2000001000.)(25.+2.+2?.))P,(23.(12.R17.(1=.R16.+100000000.))R12.)P,(27.R13.(12.(12.R18.(1=.R17.+100000000.))+100000000.))P,(16.$<.R>.R1:.(17.R17.R16.R15.))P,(18.$<.R?.(12.R1;.+10.)R13.)P,(16.$<.R10.(12.R1=.+:>0.)(>.$1>.(1?.R1?.)(13.$1>.)))P,(2:.VCS,R1>.+1000.)P,(2;.$<.R12.$2<.(>.$1>.(1?.(8.&40.R1=.))(13.$1>.)))P,(2=.R13.R21.R34.R35.R36.R3:.R3;.R41.)P,(20.$<.R14.R19.(12.R22.-30.))P,(23.(2>.VhAR,)R1:.)P,(23.R1;.(1<.R24.+30.))P,(23.R25.(25.+2.+3>.))P,(24.(23.R26.R25.)(23.(12.R25.+1000.)R1=.))P,(=.(>.(?.$10.$10.)(11.$10.$10.R1>.R27.)(>.(?.$10.$10.)(11.$10.$10.R25.(12.R25.+4.))(>.(?.$10.$10.)(11.$10.$10.(12.R25.+10.)(12.R25.+50.))(>.(?.$10.$10.)(11.$10.$10.(12.R26.+:>0.)(12.R26.+:>8.))(13.(?.$10.$10.))))))R1:.R19.)P,(14.$<.R1;.R1:.)P,(15.$<.R1;.)P,(2:.VCS,R21.(1<.R2:.R21.))(2?.$<.VAL,VCS,(30.R2;.R4;.R4:.R49.R48.R47.R46.R45.R44.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)(6.(7.R32.(8.&40.(12.R2;.-30.))R4:.R49.R48.R47.R46.(8.&40.R29.)R30.(8.&40.(12.R2:.+=0.))(8.&40.$31.)(8.&40.R27.)(8.&40.R23.)(8.&40.R26.)R43.R42.R41.R2?.R2>.R2=.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R20.(8.&40.$32.)R1?.(:.(2.&40.))R1=.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax x8 x9 x18 x19 x20 stj
      SP T PC SB c count max csz AB lo cks F fc m0 m
      TB1 TB2 TAL CB HPC CNT MX16 CSZB CKL SB0 SB1 AB0 AB1 PCC CK STT TCS SBC FR ST LOIMG SPL SPH SEP1 MU WM MI SCS.
    facts. unfold pcl_cells, lcd_frame in *. unfold A_LCD_PUSH, A_SPACEBEG_CELL, A_INSTANCE in *.
    change (1074072 + 32) with 1074104 in SBC.
    pose proof (Z.div_mod T 4096 ltac:(lia)) as TQ. rewrite TAL, Z.add_0_r in TQ. set (Tq := T / 4096) in TQ. clearbody Tq. clear TAL.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 c 32) by (clear; lia). change (2^32) with 4294967296.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. rewrite (shl32_shr30 count) by (clear -CNT MX16; lia).
    zstep. zstep. zstep.
    replace (Z.shiftr (AB - c * 4294967296 - SB) 4) with ((AB - (SB + c * 4294967296)) / 16) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^4) with 16; clear; f_equal; lia).
    (* [comment removed for export] *)
    zstep.
    pose proof (u32arr_store_ok asegs _ (PC + 16) cks count _ CK ltac:(rewrite CKL; clear -CNT MX16; lia) eq_refl) as SOK.
    replace (PC + 16 + 4 * count) with (PC + count * 4 + 16) in SOK by (clear; lia).
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le4 ?v)) _) =>
      pose proof (u32arr_write asegs mx (PC + 16) cks count v CK ltac:(rewrite CKL; clear -CNT MX16; lia)) as CK';
      replace (PC + 16 + 4 * count) with (PC + count * 4 + 16) in CK' by (clear; lia)
    end.
    store_done. try clear CK. rename CK' into CK.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. replace (SP + -48 + 48) with SP by (clear; lia). zstep.
    release_frame FR ST SP.
    apply evtA_done. unfold lcd_push_post, pcl_cells. deexists 10.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [assumption|]. split; [exact CK|]. split; [eassumption| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition lcd_at_push (SP : Z) (rax gp tp t0 t1 t2 x9 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T PC c AB count : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Lms',$0.(5.$0.R1.(6.(7.O20.(8.&40.(12.O21.-30.))O1?.O1>.O1=.O1<.O1;.(8.&40.O7.)O1:.(8.&40.(12.O8.+=0.))(8.&40.$31.)(8.&40.O6.)(8.&40.O5.)(8.&40.O4.)O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.)O3.(8.&40.$32.)O2.(:.(2.&40.))O1.(;.$<.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00f0?L15129414474.68L16901428961.67L1859764022.67 L19516900705.66L21142837706.68L23342007671.70L24525580653.70L24525581796.71L25233164513.67L25936553270.66L26905125859.68L26905125859.69L27170469450.68L27335347790.68L2901267287.2  L29149214414.68L31947592630.67L3276969806.67 L33022511713.67L33180861642.68L37448855216.4 L37975166518.67L39302203090.65L39340114894.68L40202209158.67L45217263562.67L46338021298.70L46338021298.71L46911995317.69L47717199197.70L49698585326.69L49698585326.70L55275905170.69L55333265220.69L55347951430.68L58142605646.68L59308635013.4 L59308635916.4 L59310731859.3 L59321211473.3 L60234967940.71L60388966608.68L60388966608.69L6040143663.68 L61013493601.67L61346586394.69L61615578845.69L62537825409.71L64551387318.67L65144493349.68L67176444897.67L67657156688.4 L68092860808.70L7870557622.67 00000800C00R00]00e00f01=01T01_01n02902D02L02T02Y02a03003803C03K03^03m04<04D04L04T05N06T06U06h07=07R07e07o08908A08S08e08o09:09Q09c0:50:=0:H0:S0:f0:n0;=0;E0;P0;c0<60<ES3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SPFS3hAR5count3max3CNT3MXBS3hAR5count3max3CNT3MXBS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2HBS3hAR2SP2HBS3hAR2SPS3hAR2SPS1T1cS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS5count3max3CNT3MXBS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2ra2SP1T2PC1c2lo2CB3HPC5LOIMG3SPL4SEP12HB5Ha_st5Hl_stS3hAR2s02SP1T2PC1c2lo2CB3HPC5LOIMG3SPL4SEP12HB5Ha_st5Hl_st2s12s22s32s4FS3hAR1T2PC1c2CB3HPCS3hAR2SP3SPH2HB5Ha_stS3hAR2SP3SPH2HB5Ha_stS3hAR1T2PC1c2CB3HPCS3hAR1c2CBS3hAR1c2CBS3hAR2SPS5count3max3CNT2KfS5count3max3CNT2KmS1c2CB3Kc0S1c2CB4Kc32S3hAR5count3max3CNT3MXBS3hAR2SP2lo3SPL2HBS3hAR2SP2lo3SPL2HBS3hAR2SPS3hAR2SP2loS3hAR2SP2HBS3hAR1T2PC1c2CB3HPCS3hAR2PCS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS5count3max3CNT3MXBS3hAR1T2PC1c2CB3HPCS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma lcd_fast : ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$10.PT,$10.PPC,$10.Pc,$10.Pcount,$10.Pmax,$10.Pcsz,$10.PAB,$10.Plo,$10.PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(4.(23.+1000.R;.)(24.(23.(12.R;.+1000.)+10000.)(23.+65?000.R;.)))P,(23.(12.R<.+1000.)(25.+2.+2?.))P,(4.(23.+1.R;.)(23.R;.+1>.))P,(5.$10.R=.(12.(12.R>.+=0.)(1=.+50.R<.)))P,(4.(23.=R<.)(27.R<.R;.))P,(27.R<.(25.+2.+1?.))P,(4.(23.=R;.)(27.R;.(25.+2.+40.)))P,(16.$<.R8.R11.(17.R?.R>.R=.))P,(2:.VCS,R13.+1000.)P,(20.$<.R:.R=.R15.)P,(23.(2>.VhAR,)R>.)P,(23.R?.(1<.R17.+30.))P,(23.R18.(25.+2.+3>.))P,(24.(23.R19.R18.)(23.(12.R18.+1000.)R11.))P,(2:.VCS,R12.(1<.R1:.R12.))P,(15.$<.R10.)(2?.$<.VAL,VCS,Lms',$0.(1.(2.&40.)Lx9,(2.&40.)(1.(2.&40.)La5',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(33.R20.R3:.R39.R38.R37.R36.R35.R3.R2.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1?.R1>.R1=.R19.R1<.R17.R16.R1.R4.)(4.(=.(>.(?.$10.$10.)(11.$10.$10.R18.R20.)(13.(?.$10.$10.)))R15.R1.)(4.(14.$<.R15.R1.)(4.(15.$<.R1.)(4.(16.$<.R1.R1>.(17.R1<.R1;.R1:.))(4.(2=.R1.R20.R2<.R2=.R2>.R33.R34.R3:.)(20.$<.R1.R18.(12.R20.-30.)))))))))))(6.(7.R36.(8.&40.R1<.)R35.R34.R33.R32.R31.R30.R2?.(8.&40.(12.R1;.+=0.))(8.&40.$31.)(8.&40.R19.)(8.&40.R15.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R13.(8.&40.$34.)R12.(:.(2.&40.))R11.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP T PC c count max csz AB lo F fc m
      TB1 TB2 CB HPC CNT MXB ABB PCC TCS ST LOIMG SPL SPH SEP1 SCS MI.
    facts. unfold pcl_cells in *. unfold A_LC_DEALLOC, A_INSTANCE in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases Kc0; zify_cond Kc0. { exfalso. clear -Kc0 CB. lia. }
    zstep. zstep. if_cases Kc32; zify_cond Kc32. { exfalso. clear -Kc32 CB. lia. }
    zstep. zstep. zstep.
    replace (T + 208 + c * 80) with PC by (rewrite HPC; clear; lia).
    zstep. rewrite (sx32_small max) by (clear -CNT MXB; lia).
    zstep. if_cases Km; zify_cond Km. { exfalso. clear -Km CNT. lia. }
    zstep. rewrite (sx32_small count) by (clear -CNT MXB; lia).
    zstep. if_cases Kf; zify_cond Kf. { exfalso. clear -Kf CNT. lia. }
    apply evtA_done. deexists 3. split. { unfold lcd_at_push, A_INSTANCE, A_LCD_PUSH. reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact FR| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00d0?L15129414474.66L16901428961.65L1859764022.65 L19516900705.64L21142837706.66L23342007671.68L24525580653.68L24525581542.69L25233164513.65L25936553270.64L26905125859.66L26905125859.67L27170469450.66L27335347790.66L2901267287.2  L29149214414.66L31947592630.65L3276969806.65 L33022511713.65L33180861642.66L37448855216.2 L37975166518.65L39302203090.63L39340114894.66L40202209158.65L45217263562.65L46338021298.68L46338021298.69L46911995317.67L47717199197.68L49698585326.67L49698585326.68L55275905170.67L55333265220.67L55347951430.66L58142605646.66L59308634759.2 L59308635916.3 L59310731859.3 L59321211473.3 L60388966608.66L60388966608.67L6040143663.66 L61013493601.65L61346586394.67L61615578845.67L62537825409.69L64551387318.65L65144493349.66L67176444897.65L68092860808.68L7870557622.65 00000800C00R00]00e00f01301C01N01]01h02302;02C02H02P02_02g03203:03C03R03a03i04104905306906:06M06b07707J07T07^07f07n08:08D08O08a09309;09F09Q09d09l0:;0:C0:N0:a0;0S3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SPFS3hAR3max3MXBS3hAR3max3MXB2KdS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2HBS3hAR2SP2HBS3hAR2SPS3hAR2SPS1T1cS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3max3MXBS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2ra2SP1T2PC1c2lo2CB3HPC5LOIMG3SPL4SEP12HB5Ha_st5Hl_stS3hAR2s02SP1T2PC1c2lo2CB3HPC5LOIMG3SPL4SEP12HB5Ha_st5Hl_st2s12s22s32s4FS3hAR1T2PC1c2CB3HPCS3hAR2SP3SPH2HB5Ha_stS3hAR2SP3SPH2HB5Ha_stS3hAR1T2PC1c2CB3HPCS3hAR1c2CBS3hAR1c2CBS3hAR2SPS3max2KdS3max3MXB2KmS1c2CB3Kc0S1c2CB4Kc32S3hAR2SP2lo3SPL2HBS3hAR2SP2lo3SPL2HBS3hAR2SPS3hAR2SP2loS3hAR2SP2HBS3hAR1T2PC1c2CB3HPCS3hAR2PCS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR1T2PC1c2CB3HPCS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma lcd_drain : ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$10.PT,$10.PPC,$10.Pc,$10.Pmax,$10.Pcsz,$10.PAB,$10.Plo,$10.PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(4.(23.+1000.R:.)(24.(23.(12.R:.+1000.)+10000.)(23.+65?000.R:.)))P,(23.(12.R;.+1000.)(25.+2.+2?.))P,(4.(23.+1.R:.)(23.R:.+1>.))P,(5.$10.R<.(12.(12.R=.+=0.)(1=.+50.R;.)))P,(4.(23.+1.R;.)(27.R;.(25.+2.+1?.)))P,(4.(23.=R:.)(27.R:.(25.+2.+40.)))P,(16.$<.R7.R?.(17.R=.R=.R<.))P,(2:.VCS,R11.+1000.)P,(20.$<.R9.R<.R13.)P,(23.(2>.VhAR,)R=.)P,(23.R>.(1<.R15.+30.))P,(23.R16.(25.+2.+3>.))P,(24.(23.R17.R16.)(23.(12.R16.+1000.)R10.))P,(2:.VCS,R11.(1<.R18.R11.))P,(15.$<.R?.)(2?.$<.VAL,VCS,Lms',$0.(1.(2.&40.)Lx14,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R3.(6.(7.(8.&40.$35.)(8.&40.(12.R1=.-30.))R36.R35.R34.R33.R32.(8.&40.R1;.)(8.&40.(12.R1<.+=0.))(8.&40.(12.R1<.+=0.))(8.&40.R1;.)(8.&40.$31.)(8.&40.R1:.)R2.(8.&40.R19.)R2=.R2<.(8.&40.$31.)(8.&40.R1:.)(8.&40.R17.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R15.(8.&40.$36.)R14.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.R16.R1=.)(13.(?.$10.$10.)))R13.R1.)(4.(14.$<.R13.R1.)(4.(15.$<.R1.)(4.(16.$<.R1.R1;.(17.R19.R19.R18.))(4.(2=.R1.R1=.R29.R2:.R2;.R30.R31.R37.)(20.$<.R1.R16.(12.R1=.-30.))))))))))(6.(7.R34.(8.&40.R1:.)R33.R32.R31.R30.R2?.R2>.R2=.(8.&40.(12.R19.+=0.))(8.&40.$31.)(8.&40.R17.)(8.&40.R14.)R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R12.(8.&40.$34.)R11.(:.(2.&40.))R10.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP T PC c max csz AB lo F fc m
      TB1 TB2 CB HPC MXB ABB PCC TCS ST LOIMG SPL SPH SEP1 SCS MI.
    facts. unfold pcl_cells in *. unfold A_LC_DEALLOC, A_INSTANCE, A_LCD_BACK, A_LC_DRAIN in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases Kc0; zify_cond Kc0. { exfalso. clear -Kc0 CB. lia. }
    zstep. zstep. if_cases Kc32; zify_cond Kc32. { exfalso. clear -Kc32 CB. lia. }
    zstep. zstep. zstep.
    replace (T + 208 + c * 80) with PC by (rewrite HPC; clear; lia).
    zstep. rewrite (sx32_small max) by (clear -MXB; lia).
    zstep. if_cases Km; zify_cond Km. { exfalso. clear -Km MXB. lia. }
    zstep. rewrite (sx32_small max) by (clear -MXB; lia).
    zstep. if_cases Kd; zify_cond Kd. 2:{ exfalso; clear -Kd; lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. deexists 2. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact FR| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L47729753627.52L62537825409.53L67657122630.2 L68088629966.5200000?00C00N00]S1T2PC1c2CB3HPCS2PCS5count3CNTS1T2PC1c2CB3HPC". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma lcd_back : ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$10.PT,$10.PPC,$10.Pc,$10.Pcount,$10.Pmax,$10.Pcsz,$10.PAB,$10.PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(4.(23.+1000.R:.)(24.(23.(12.R:.+1000.)+10000.)(23.+65?000.R:.)))P,(23.(12.R;.+1000.)(25.+2.+2?.))P,(4.(23.+1.R:.)(23.R:.+1>.))P,(5.$10.R<.(12.(12.R=.+=0.)(1=.+50.R;.)))P,(4.(23.=R;.)(27.R;.(25.+2.+1?.)))P,(16.$<.R6.R>.(17.R<.R;.R:.))P,(2:.VCS,R10.+1000.)P,(15.$<.R8.)(2?.$<.VAL,VCS,(33.R13.(8.&40.$35.)R2;.R2:.R29.R28.R27.(8.&40.(12.R12.+=0.))R21.R20.R1?.(8.&40.$31.)(8.&40.R10.)(8.&40.R<.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R12.R11.R10.R<.R?.R;.R:.R9.)(6.(7.(8.&40.$35.)(8.&40.(12.R13.-30.))R2;.R2:.R29.R28.R27.(8.&40.R11.)(8.&40.(12.R12.+=0.))R26.R25.R24.R23.R22.R21.R20.R1?.(8.&40.$31.)(8.&40.R10.)(8.&40.R<.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R;.(8.&40.$35.)R:.(:.(2.&40.))R9.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP T PC c count max csz AB F fc m
      TB1 TB2 CB HPC CNT PCC TCS MI.
    facts. unfold pcl_cells in *. unfold A_LCD_BACK, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. rewrite (sx32_small count) by (clear -CNT; lia). zstep.
    apply evtA_done. unfold lcd_at_push, A_INSTANCE, A_LCD_PUSH. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition lcdr_frame (m : mem) (SP : Z) (j0 : list byte) (ra : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "(16.$<.O4.(12.O3.-40.)(>.$1>.(37.#8.O2.)(>.$1>.(1?.(8.&40.$31.))(>.$1>.(1?.(8.&40.=))(>.$1>.(1?.(8.&40.=))(>.$1>.(1?.(8.&40.=))(>.$1>.(1?.(8.&40.=))(>.$1>.(1?.(8.&40.=))(>.$1>.(1?.O1.)(13.$1>.))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0180?L13008260193.64L13326966474.64L13896079414.64L16901428961.64L17412854912.2 L1859764022.64 L18699521429.1 L19335785290.65L19516900705.63L20977510940.64L23341931402.64L23342006397.65L24525535120.64L24525581415.65L25030990809.2 L25233164513.64L25244530876.65L25363888586.65L2589632713.65 L25936553270.63L26438528495.66L26758072608.69L29176651982.65L31376905802.65L31947592630.64L33022511713.64L37404009674.65L37448855216.2 L37975166518.64L38758388235.65L39220637093.0 L39302709343.62L39333131958.67L41415936155.65L41415990140.2 L41418004092.2 L41531883086.64L42001773902.65L4216608462.65 L43414810954.65L46338021298.67L46338021298.68L46924779029.64L47717151648.64L47717197911.65L47852169094.64L49004614727.2 L49440411594.65L49698585326.66L49698585326.67L55271494450.64L55273555981.2 L57370105059.65L57370105059.66L57792571214.65L5802316517.67 L58459420406.65L58459420406.66L59308634630.3 L61013493601.64L61611208061.64L62537825409.65L62537825409.66L62929648619.2 L64551387318.64L67176444897.64L67394690510.65L68092807029.64L68092861570.65L68306003022.65L7870557622.64 L9891990907.1  00000?00K00^00m01601I01M01Y01h01i01j01k02802E02N02]02j03603?03R03^04^04j05605I05X05d05m06@06P06Q06d07407=07B07C07O07[07g0830960:60:70:R0:m0;90;B0;N0;h0<B0<]0<f0=60=F0=R0=h0>B0>\0>g0?60?Q0?]0?i0@10@D0@S0@_0A:0AU0Aa0B40B7S3hAR2SP3max2loS3hAR2SP3maxS3hAR2SP3max2lo3SPLS3hAR2SP3max2loS3max3MXBS3hAR2SP3max2lo3SPLS2SPS3hAR2SP3maxS3hAR2SP3max2loFFFS3hAR3max3MXBS3hAR3max3MXBS3max3MXBS3hAR2SP3max2loS3hAR3max3MXBS3hAR2SP3maxS3hAR3maxS3hAR2SP3max2lo3SPLS3hAR2PC3maxS3hAR2SP1T2PC1c3max2lo2CB3HPC3MXB5LOIMG3SPL4SEP13HB05Ha_st5Hl_stS3hAR2SP3maxS3hAR2SP3maxS3hAR2SP3max2lo3SPLS3hAR2SP3max2loS3hAR2SP3maxS3max3MXBS3hAR2SP3max2lo3SPLS3hAR3max3MXB2HBSS3hAR2SP3max2lo3SPLS3hAR2PC3max3HB0S3hAR3maxS3maxSS3hAR2SP3maxS3hAR2SP3maxS3hAR2SP3maxS3hAR2SP3maxS3hAR2ra2SP1T2PC1c3max2lo2CB3HPC3MXB5LOIMG3SPL4SEP13HB05Ha_st5Hl_stS3hAR2SP1T2PC1c3max2lo2CB3HPC3MXB5LOIMG3SPL4SEP13HB05Ha_st5Hl_stFS3hAR1T2PC1c3max2CB3HPC3MXBS3hAR1T2PC1c3max2CB3HPC3MXBS3hAR2SP3maxS3max3MXBS3hAR2SP3maxS3hAR2SP3max3SPH3HB05Ha_stS3hAR2SP3max3SPH3HB05Ha_stS3hAR1T2PC1c3max2CB3HPC3MXBS3max3MXBS3hAR2SP3max3HB0S3hAR2SP3max3HB0S3hAR2SP3maxS3hAR2PC3max3HB05Ha_stS3hAR2SP2PC3max2lo3SPL3HB0S3hAR2SP2PC3max2lo3SPL3HB0S3max2HB2KcS3hAR2SP3max2loS3hAR1T2PC1c3max2CB3HPC3MXBS3hAR2PC3maxS3hAR2PC3maxS2PC3maxS3hAR2SP3max2lo3SPLS3hAR2SP3max2loS3hAR2SP3maxS3hAR1T2PC1c3max2CB3HPC3MXBS3hAR1T2PC1c3max2CB3HPC3MXBS3hAR2SP3maxS3hAR2SP3max2lo3SPLS1T". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma lcdr_A : ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$10.PT,$10.PPC,$10.Pc,$10.Pmax,$10.Pcsz,$10.Plo,$10.PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(4.(23.+1000.R9.)(24.(23.(12.R9.+1000.)+10000.)(23.+65?000.R9.)))P,(23.(12.R:.+1000.)(25.+2.+2?.))P,(4.(23.+1.R9.)(23.R9.+1>.))P,(5.$10.R;.(12.(12.R<.+=0.)(1=.+50.R:.)))P,(4.(23.+2.R:.)(23.R:.+10.))P,(16.$<.R6.R=.(17.R;.R;.R:.))P,(2:.VCS,R?.+1000.)P,(20.$<.R8.R;.R11.)P,(23.(2>.VhAR,)R<.)P,(23.R=.(1<.R13.+40.))P,(23.R14.(25.+2.+3>.))P,(24.(23.R15.R14.)(23.(12.R14.+1000.)R?.))P,(2:.VCS,R10.(1<.R16.R10.))P,(15.$<.R>.)(2?.$<.VAL,VCS,Lms',$0.(1.(2.&40.)La6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(21.(2.&8.))Lj0,(21.(2.&8.))(4.(5.$0.R4.(6.(7.(8.&40.$38.)(8.&40.(12.R1<.-40.))R35.R34.R33.R32.R31.R30.R2?.(8.&40.$31.)(8.&40.(12.R1<.-38.))(8.&40.(12.R1;.+:=0.))(8.&40.R19.)(8.&40.(12.(12.R1:.+10.)(1=.+4.(1<.R18.(1;.R18.+2.)))))(8.&40.(1;.R18.+2.))R3.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R15.(8.&40.$39.)R14.(:.(2.&40.))R2.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.R16.R1<.)(>.(?.$10.$10.)(11.$10.$10.R1:.(12.R1:.+4.))(13.(?.$10.$10.))))R13.R2.)(4.(14.$<.R13.R2.)(4.(15.$<.R2.)(4.(16.$<.R2.R1:.(17.(1<.R18.(1;.R18.+2.))R18.R17.))(4.(3:.R2.R1<.R1.R36.)(20.$<.R2.R16.(12.R1<.-40.)))))))))))(6.(7.R32.(8.&40.R18.)R31.R30.R2?.R2>.R2=.R2<.R2;.(8.&40.(12.R17.+=0.))(8.&40.R16.)(8.&40.$31.)(8.&40.R15.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R11.(8.&40.$36.)R10.(:.(2.&40.))R?.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP T PC c max csz lo F fc m
      TB1 TB2 CB HPC MXB PCC TCS ST LOIMG SPL SPH SEP1 SCS MI.
    facts. unfold pcl_cells in *. unfold A_LC_DRAIN, A_INSTANCE, A_LCDR_BACK, A_RTA in *.
    pose proof (munch_refl [(lo, SP); (PC, PC + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (HB : 1 <= max / 2 <= max) by (clear -MXB; split; [apply Z.div_le_lower_bound| apply Z.div_le_upper_bound]; lia).
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    zstep. zstep. zstep. zstep.
    zstep. rewrite (sx32_small max) by (clear -MXB; lia). zstep. rewrite (zx32_lit max) by (clear -MXB; lia).
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. rewrite (Z.shiftr_div_pow2 max 1) by (clear; lia). change (2^1) with 2.
    zstep. zstep. rewrite (Z.mod_small max 4294967296) by (clear -MXB; lia).
    zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc HB. lia. }
    zstep. zstep. zstep. zstep.
    zstep. rewrite (Z.shiftl_mul_pow2 (max - max / 2) 2) by (clear -HB; lia). change (2^2) with 4.
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. deexists 3.
    replace (T + 208 + 2047 + 513) with (T + 2768) by (clear; lia). replace (PC + (max - max / 2) * 4 + 16) with (PC + 16 + 4 * (max - max / 2)) by (clear; lia).
    replace (SP + -64 + 8) with (SP + -56) by (clear; lia).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [assumption|]. split; [| exact ST]. unfold lcdr_frame, A_INSTANCE. exact FR.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L16408089748.58L17300487886.59L1745796682.59 L19516687975.57L19813496778.59L24483416543.61L25936864816.57L26101742542.59L2841479090.59 L28444373396.58L3023655625.56 L33026492378.56L35438268739.58L3700428279.59 L37979210637.56L39937688649.56L39989712451.58L40482576816.57L41531883086.58L43121706933.58L46491748628.58L47442874190.59L48242093646.59L4922019779.58 L49688261315.58L49698585326.60L52517234580.58L55923306218.57L57792571214.57L58428347210.59L58528010772.58L62426986254.1 L64547441933.56L67188883034.56L67394690510.57L67533486051.59L7775456458.59 00000?00G00O00Z00b01B01Q01Y01^01m02<02G02R02f03503=03H03W03_03g04604>04F04Q04\05105@05H05P05X05g05k06:06E06M06X06`S3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2HB5Ha_st5Hl_st2s02s12s2S3hAR2SP2lo3SPLS3hAR2SPS3hARS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo1W3SPL2HBS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2loS3hAR2SP2loS3hAR2SP3SPH2HB5Ha_stS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS2SPS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SPS3hAR2SP2HBS3hAR2SP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma lcdr_B : ltac2:(CDefT.buildp (gd_tbl_AW_LCDealloc ()) "Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pra,(2.&40.)PSP,$10.Plo,$10.Pj0,(21.(2.&8.))PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))PW,(21.(?.$10.$10.))P,(3:.R2.R8.R6.R9.)P,(20.$<.R3.R8.(12.R9.-40.))P,(23.(2>.VhAR,)R9.)P,(23.R:.(1<.R;.+70.))P,(23.R<.(25.+2.+3>.))P,(=.(>.(?.$10.$10.)(11.$10.$10.R<.R=.)R6.)R8.R7.)P,(14.$<.R9.R8.)P,(15.$<.R9.)P,(2:.VCS,R?.(1<.R10.R?.))(2?.$<.VAL,VCS,Lms',$0.(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R5.(6.(7.R17.(8.&40.R16.)R34.R33.R32.R31.R30.R2?.R2>.R4.R3.R2.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R13.(9.R17.)R12.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.R15.R16.)R?.)R11.R1.)(4.(14.$<.R11.R1.)(4.(15.$<.R1.)(20.$<.R1.R15.R16.)))))))))(6.(7.(8.&40.$38.)(8.&40.(12.R11.-40.))R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R>.(8.&40.$38.)R=.(:.(2.&40.))R;.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra SP lo j0 F fc m0 m W
      FR ST LOIMG SPL SPH MU WM MI SCS.
    facts. unfold lcdr_frame in FR. unfold A_LCDR_BACK, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR0 ST (SP + -64).
    (* [comment removed for export] *)
    zstep. zstep. replace (SP + -64 + 64) with SP by (clear; lia). zstep.
    release_frame FR ST SP.
    apply evtA_done. deexists 4.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End LCDealloc.

End ARUN_1.
