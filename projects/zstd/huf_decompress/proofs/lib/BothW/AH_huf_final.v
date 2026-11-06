(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ABase AMalloc_iface AFake_iface ADriver_iface AInstanceF AFreeAll AHarness_iface
     AH_huf_iface AH_huf_rdt2 AHarness_bm AH_huf_split AH_huf_asm1 AH_huf_asm2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_final () := "I59OSSVerify5KrLib5BothW=AMalloc_iface<AMallocIface00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothW=AMalloc_iface3aciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AH_huf_rdt2>huf_rdt_stmtA2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface=huf_dec_stmtAC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5BothW>AHarness_iface;payload_atAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5BothW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm7hinv_bmC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW5ABase6al_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface2HUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit6aps_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA9fuzz_oneAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface>fuzz_oneA_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit6implMAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_split9hMA_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AH_huf_asm2:fz_secondAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AH_huf_asm19fz_firstAC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib5BothW;AHarness_bm?fuzz_oneA_stmtBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5BothW;AHarness_bm7AHBM_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm7AHBM_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface;AHUF_RDT_X1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface;AHUF_RDT_X2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface;AHUF_DEC_1XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AH_huf_iface;AHUF_DEC_4XC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5BothW>AHarness_iface>AHARNESS_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface;ATRUN_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface9ATRUN_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps:AAllocAsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface;AFUZZ_ENTRYC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib5BothW<AH_huf_final=huf_lib_stmtAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5BothW8AFreeAll8AHI_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AInstanceF5AI_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5BothW:AInstanceF<AI_of_DRV_CIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib5BothW<AH_huf_final@fuzz_oneA_of_libC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib5BothW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5BothW=ADriver_iface>drv_img_rangesC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW;AFake_iface>afake_rng_monoC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem fuzz_oneA_of_lib : forall {rc : runConstT} (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop)
    (dt_ok : amem -> Z -> Z -> Prop),
  (forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
  (forall a, AHBM_LO <= a < AHBM_HI -> in_ranges (aci AI) a) ->        (* [comment removed for export] *)
  huf_rdt_stmtA2 AI rng_fs dt_ok AHUF_RDT_X1 -> huf_rdt_stmtA2 AI rng_fs dt_ok AHUF_RDT_X2 ->
  huf_dec_stmtA AI rng_fs dt_ok AHUF_DEC_1X -> huf_dec_stmtA AI rng_fs dt_ok AHUF_DEC_4X ->
  fuzz_oneA_stmtB AI rng_fs.
Proof.
intros rc AI rng_fs dt_ok MONO CIBM RDT1 RDT2 DEC1 DEC4.
unfold fuzz_oneA_stmtB.
intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
  s LB D payload lo rstk AH HLB PAY PAYB PLB D16 SZ HINV HBM ST BOT LOS SPG SP16 RC RLO RHI RRLO S0E MI FRM TP A0E A1E RAE
  HUL RSTK RI RISH RFS RR AOK.
subst a0 a1.
eapply fz_firstA; try eassumption.
intros producer dt wksp dBuf s' RNG1 ms HS.
eapply fz_secondA; eassumption.
Qed.

(* [comment removed for export] *)
Definition huf_lib_stmtA (rc : runConstT) : Prop :=
  exists dt_ok : amem -> Z -> Z -> Prop,
       huf_rdt_stmtA2 (AI_of (@AHI_free rc)) afake_rng dt_ok AHUF_RDT_X1
    /\ huf_rdt_stmtA2 (AI_of (@AHI_free rc)) afake_rng dt_ok AHUF_RDT_X2
    /\ huf_dec_stmtA (AI_of (@AHI_free rc)) afake_rng dt_ok AHUF_DEC_1X
    /\ huf_dec_stmtA (AI_of (@AHI_free rc)) afake_rng dt_ok AHUF_DEC_4X.

(* [comment removed for export] *)
Theorem fuzz_client_of_lib : (forall rc : runConstT, huf_lib_stmtA rc) ->
  forall rc : runConstT, fuzz_oneA_stmtB (AI_of (@AHI_free rc)) afake_rng.
Proof.
intros HL rc. destruct (HL rc) as (dt_ok & R1 & R2 & D1 & D4).
assert (CIBM : forall a, AHBM_LO <= a < AHBM_HI -> in_ranges (aci (AI_of (@AHI_free rc))) a).
{ intros a Ha.
  assert (HIN : In (nth 21 drv_img_ranges (0, 0)) drv_img_ranges) by (apply nth_In, Nat.ltb_lt; vm_compute; reflexivity).
  assert (HC : (Z.leb (fst (nth 21 drv_img_ranges (0, 0))) AHBM_LO && Z.leb AHBM_HI (snd (nth 21 drv_img_ranges (0, 0))))%bool = true)
    by (vm_compute; reflexivity).
  apply andb_true_iff in HC. destruct HC as [HC1 HC2]. apply Z.leb_le in HC1, HC2.
  exists (nth 21 drv_img_ranges (0, 0)). split; [apply AI_of_DRV_CI; exact HIN| lia]. }
exact (fuzz_oneA_of_lib (AI_of (@AHI_free rc)) afake_rng dt_ok afake_rng_mono CIBM R1 R2 D1 D4).
Qed.
