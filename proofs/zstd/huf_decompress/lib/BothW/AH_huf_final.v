(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import ABase AMalloc_iface AFake_iface ADriver_iface AInstanceF AFreeAll AHarness_iface
     AH_huf_iface AH_huf_rdt2 AHarness_bm AH_huf_split AH_huf_asm1 AH_huf_asm2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_final () := "I5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<AMallocIface00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_rdt2>huf_rdt_stmtA2C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_stmtAK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC46Stdlib5Lists4List2InK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;payload_atAC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK47Corelib7Numbers7BinNums1Z02I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7hinv_bmC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_sp0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface2HUC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6aps_okC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA9fuzz_oneAC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface>fuzz_oneA_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_split9hMA_stateC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm2:fz_secondAC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_asm19fz_firstAC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm?fuzz_oneA_stmtBI5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_LOC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_HIC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;AHUF_RDT_X1C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;AHUF_RDT_X2C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;AHUF_DEC_1XC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;AHUF_DEC_4XI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface>AHARNESS_STACKC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;ATRUN_DEPTHC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface9ATRUN_RETC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;AFUZZ_ENTRYI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_final=huf_lib_stmtAI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW8AFreeAll8AHI_freeC5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF5AI_ofI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF<AI_of_DRV_CIK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_final@fuzz_oneA_of_libK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface9afake_rngC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_rangesI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface>afake_rng_mono".
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
