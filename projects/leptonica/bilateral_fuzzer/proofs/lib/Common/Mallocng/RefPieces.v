(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RefPieces () := "C69OSSVerify5KrLib6Common8Mallocng:MallocTree4mretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5mbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree6mcrashC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree1MC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib6Common8PropExec6v_andiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps3is0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Common8PropExec7v_slliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7v_srliwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces6halveFC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib6Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces7shrinkFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_sbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces3zlFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C69OSSVerify5KrLib6Common8Mallocng9MallocOps2w0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib6Common8Mallocng9RefPieces4mletC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng:MallocTree5itree00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng:MallocTree6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib6Common8Mallocng9MallocOps=m_canary_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces6as_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps>m_canary_checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;A_INIT_DONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_lwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces7am_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LIBCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_ldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps4wlitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4c_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree7massertC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces6am_resC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng9RefPieces8aslot_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common8Mallocng;MallocShape6magreeC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib6Common8Mallocng8RefStmts<alloc_slot_DC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib6Common8Mallocng7RefStep4wtopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout4A_TPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib6Common8Mallocng9MallocOps<m_alloc_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5tsafeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng8RefStmts?alloc_slot_stmtC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init5Logic8eq_ind_rI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition halveF (usage : word) : nat -> word -> word :=
  fix halve (k : nat) (a3 : word) : word :=
    match k with O => a3 | S k' =>
      if negb (is0 (v_andi a3 1)) then a3
      else if negb (c_ltu usage (v_slliw a3 2)) then a3
      else halve k' (v_srliw a3 1)
    end.

(* [comment removed for export] *)
Definition shrinkF (size : word) : nat -> word -> word :=
  fix shrink (k : nat) (a2 : word) : word :=
    match k with O => a2 | S k' =>
      if is0 (v_srli (v_mul size a2) 20) then a2
      else shrink k' (v_srliw a2 1)
    end.

(* [comment removed for export] *)
Definition zlF (size : word) : nat -> word -> M unit :=
  fix zl (k : nat) (a2 : word) : M unit :=
    match k with O => mret tt | S k' => m_sb a2 w0 ;; zl k' (v_add a2 size) end.

Lemma halveF_S : forall usage k a3,
  halveF usage (S k) a3 =
  (if negb (is0 (v_andi a3 1)) then a3
   else if negb (c_ltu usage (v_slliw a3 2)) then a3
   else halveF usage k (v_srliw a3 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h02a3h11kh25usagep;1p;2p;3p-1R0p10000p4p710p8P0p10014R1p4p7210R2p8P0p10029p4p710p8P1p4p710p1003?p4p710R1p8P2P1p8g004@j10Tg004ej1;Tg005Cj14Tg005fj12Tg006Dj2:Tg007?j19Tg008Aj11Tg008_j25Tg009[j26Tg00:Uj27Tg00;Qj33Tg00<Vj28Tg00=0R1#0R2#0#0#0#0#0#;#4R0g00=Ug00>4R3P0f0R4%21R1':#9#1P4P3P0f2R3%22,54'6#1P4f11741533n0100000020000n0100000020000,80X00W1W2o"). Qed.
Lemma halveF_O : forall usage a3, halveF usage O a3 = a3.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h02a3h15usagep;1p;2g004@j10Tg004ej13Tg005Cj12Tg00<Vj21Tg00=0#0#0#0#0#0#0#3#2R0f0,10X00W1o"). Qed.
Lemma shrinkF_S : forall size k a2,
  shrinkF size (S k) a2 = (if is0 (v_srli (v_mul size a2) 20) then a2 else shrinkF size k (v_srliw a2 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h02a2h11kh24sizep;1p;2p;3g004@j10Tg004ej1:Tg005Cj13Tg00>Tj22Tg00?Nj19Tg005fj11Tg00@3j28Tg007?j14Tg00:Uj25Tg00@nj36Tg00<Vj27Tg00=0R0#0R1#0#0#0#0#0#:#3R2g00=Ug00>4P2f2R3f0R4'2%91#0#0#1'8#4P4f1%10,54563n0100000020000,72X02W1W2o"). Qed.
Lemma shrinkF_O : forall size a2, shrinkF size O a2 = a2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h02a2h14sizep;1p;2g004@j10Tg004ej13Tg005Cj12Tg00<Vj21Tg00=0#0#0#0#0#0#0#3#2R0f0,10X00W1o"). Qed.
Lemma zlF_S : forall size k a2, zlF size (S k) a2 = (m_sb a2 w0 ;; zlF size k (v_add a2 size)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h02a2h11kh24sizep;1p;3p;2p;4g004@j10Tg004ej18Tg005Cj12Tg003?j11Tg00B4j37Tg00C8j26Tg00D2j33Tg0014j44Tg00<Vj25Tg00=0#0#0#0#0#0#0#8#2R0g00=Ug00E4R1#1P1P1p,2MLf0g00ET37f3R2f2f1/6233V1C4'5X00W1W2o"). Qed.
Lemma zlF_O : forall size a2, zlF size O a2 = mret tt.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h02a2h14sizep;1p;2g004@j10Tg004ej15Tg005Cj12Tg003?j11Tg0000j24Tg00<Vj23Tg00=0#0#0#0#0#0#0#5#2R0g00E4R1#1g00FU,41'3X00W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mlet {A B : Type} (x : A) (f : A -> M B) : M B := f x.

Lemma mlet_eq {A B} : forall (x : A) (f : A -> M B), mlet x f = f x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h01Ah11Bh21fh31xp;1p;2p100G5R0p60621000R1g003?R2p4p710R3p8p200R4P0p6061001p8p201R0P3p8P0P1p8P2j11Tg00<Vj20Tf1R2f2R1%11R1[f0P2O1,01W2W3X10X04o"). Qed.

Lemma mbind_mlet {A B C} : forall (x : A) (f : A -> M B) (k : B -> M C) s,
  MallocTree.mbind (mlet x f) k s = mlet x (fun y => MallocTree.mbind (f y) k) s.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h01Ah11Bh21Ch31fh41kh51sh61xh71yp;1p;4p;5p;2p200R0g00G5R1p6061001p8p201R2g003?R3p4p710R4p8P2g0014R5p4p710p8P2P1p60621000R6p8p202R7P4p8P7P5p4p7210p8P7P6p8P3j14Tg00H8j13TP5j40TP1j51Tg00<Vj22Tf2R1f3R5%45[R3g00I?f4R6#3f6R4P6P5P4f5P5f0R5O1P1C0X74P5D1'2W5X43W3W6X27X12X00o"). Qed.

(* [comment removed for export] *)
Definition as_actg (m3 : word) : M (option (word * word)) :=
  mp3 <- m_ld (at_ m3 16) ;;
  ab <- m_lbu (at_ mp3 8) ;;
  let act2 := v_sllw (wlit 2) ab in
  massert (is0 (v_andi (at_ m3 28) 3)) ;;
  fr4 <- m_lw (at_ m3 28) ;;
  m_sw (at_ m3 28) (v_and fr4 (v_subw w0 act2)) ;;
  let mask := v_and fr4 (v_addiw act2 (-1)) in
  m_sw (at_ m3 24) mask ;;
  massert (negb (is0 mask)) ;;
  w32 <- m_lw (at_ m3 32) ;;
  let d := v_addi (v_srli (v_slli w32 52) 58) (-7) in
  (if c_ltu (wlit 31) d then mret tt
   else b <- m_lbu (at_ (v_add A_LOCK d) 888) ;;
        if is0 b then mret tt
        else m_sb (at_ (v_add A_LOCK d) 888) (v_addi b (-1))) ;;
  mret (Some (m3, mask)).

(* [comment removed for export] *)
Definition as_tav (pm m0 : word) : M (option (word * word)) :=
  if is0 m0 then mret None
  else
    am <- m_lw (at_ m0 24) ;;
    if negb (is0 am) then mret (Some (m0, am))
    else
      fr <- m_lw (at_ m0 28) ;;
      nx <- m_ld (at_ m0 8) ;;
      mo <- (if negb (is0 fr)
             then m_sd pm nx ;; mret (Some nx)
             else
               (if c_eq nx m0 then m_sd pm w0
                else pv <- m_ld m0 ;;
                     m_sd (at_ pv 8) nx ;;
                     pv2 <- m_ld m0 ;;
                     nx2 <- m_ld (at_ m0 8) ;;
                     m_sd nx2 pv2 ;;
                     h <- m_ld pm ;;
                     if c_eq h m0 then n3 <- m_ld (at_ m0 8) ;; m_sd pm n3
                     else mret tt) ;;
               m_sd m0 w0 ;; m_sd (at_ m0 8) w0 ;;
               m1 <- m_ld pm ;;
               if is0 m1 then mret None else mret (Some m1)) ;;
      match mo with
      | None => mret None
      | Some m =>
        fr1 <- m_lw (at_ m 28) ;;
        w <- m_ld (at_ m 32) ;;
        mf <- (if negb (is0 (v_andi w 32))
                  && c_eq fr1 (v_addiw (v_sllw (wlit 2) w) (-1))
               then m' <- m_ld (at_ m 8) ;;
                    m_sd pm m' ;;
                    fr' <- m_lw (at_ m' 28) ;;
                    mret (m', fr')
               else mret (m, fr1)) ;;
        let '(m2, fr2) := mf in
        mp <- m_ld (at_ m2 16) ;;
        ai <- m_lbu (at_ mp 8) ;;
        let act := v_addiw (v_sllw (wlit 2) ai) (-1) in
        m3o <- (if negb (is0 (v_and act fr2)) then mret (Some m2)
                else nx3 <- m_ld (at_ m2 8) ;;
                     if negb (c_eq nx3 m2)
                     then m_sd pm nx3 ;; mret (Some nx3)
                     else
                       let a5 := v_andi ai 31 in
                       w5 <- m_ld (at_ m2 32) ;;
                       szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w5 5) 126)) ;;
                       let a6 := v_addi a5 2 in
                       let a4 := v_addi a5 1 in
                       let t0 := v_addi (v_slli a5 4) 48 in
                       let size := v_slli szc 4 in
                       let a7 := v_mul t0 szc in
                       let t0' := v_mul size a6 in
                       let a6' := v_addiw a7 15 in
                       let t0'' := v_addiw t0' 16 in
                       match m_span_loop 40 a6' t0'' a4 size with
                       | None => mcrash
                       | Some cnt =>
                         let lim := v_addi (v_andi w5 31) 1 in
                         let cnt' := if c_ltu cnt lim then cnt else lim in
                         m_sb (at_ mp 8) (v_or (v_andi (v_addi cnt' (-1)) 31) (v_andi ai 224)) ;;
                         mret (Some m2)
                       end) ;;
        match m3o with
        | None => mret None
        | Some m3 =>
          am3 <- m_lw (at_ m3 24) ;; massert (is0 am3) ;;
          as_actg m3
        end
      end.

(* [comment removed for export] *)
Definition as_take (m mask : word) : M word :=
  let first := v_and mask (v_subw w0 mask) in
  m_sw (at_ m 24) (v_subw mask first) ;;
  if is0 first then mcrash
  else m_ctz32 mask.

(* [comment removed for export] *)
Definition as_cnt (sc usage size : word) : M word :=
  if negb (c_lts (wlit 8) sc)
  then let tb := v_add A_SMALL_CNT_TAB (v_add (v_slli sc 1) sc) in
       t0 <- m_lbu tb ;;
       if negb (c_ltu usage (v_slli t0 2)) then mret t0
       else t1 <- m_lbu (at_ tb 1) ;;
            if negb (c_ltu usage (v_slli t1 2)) then mret t1
            else m_lbu (at_ tb 2)
  else t <- m_lbu (v_add A_MED_CNT_TAB (v_andi sc 3)) ;;
       mret (shrinkF size 40 (halveF usage 8 t)).

(* [comment removed for export] *)
Definition as_fail (m : word) : M word :=
  m_free_meta_ag (at_ A_LOCK 24) m ;;
  mret wm1.

(* [comment removed for export] *)
Definition as_tail (s7 pm sc m p cnt aidx c1 : word) : M word :=
  us2 <- m_ld (at_ s7 472) ;;
  m_sd (at_ s7 472) (v_add us2 cnt) ;;
  m_sw (at_ m 24) (v_addi (v_sllw (wlit 2) aidx) (-1)) ;;
  am <- m_lw (at_ m 24) ;;
  m_sw (at_ m 28) (v_add (v_sllw (wlit 2) c1) (v_xori am (-1))) ;;
  m_sd (at_ m 16) p ;;
  m_sd p m ;;
  mp <- m_ld (at_ m 16) ;;
  ab <- m_lbu (at_ mp 8) ;;
  m_sb (at_ mp 8) (v_or (v_andi ab 224) (v_andi aidx 31)) ;;
  wm2 <- m_ld (at_ m 32) ;;
  m_sd (at_ m 32) (v_addi (v_or (v_or (v_srli (v_slli sc 58) 52) (v_andi c1 31))
                                (v_and wm2 PAGEMASK)) 32) ;;
  am2 <- m_lw (at_ m 24) ;;
  m_sw (at_ m 24) (v_addi am2 (-1)) ;;
  nx <- m_ld (at_ m 8) ;; massert (is0 nx) ;;
  pv <- m_ld m ;; massert (is0 pv) ;;
  hd <- m_ld pm ;;
  (if is0 hd then m_sd m m ;; m_sd (at_ m 8) m ;; m_sd pm m
   else m_sd (at_ m 8) hd ;; hp <- m_ld hd ;; m_sd m hp ;;
        m_sd (at_ hp 8) m ;; n2 <- m_ld (at_ m 8) ;; m_sd n2 m) ;;
  mret w0.

(* [comment removed for export] *)
Definition as_nested (fuel' : nat) (sp s7 pm sc m size cnt1 a4 : word) : M word :=
  let a1 := v_addi a4 12 in
  let n16 := v_srli a4 4 in
  j <- (if c_ltu a1 (wlit 157) then mret n16
        else m_size_to_class_big A_SIZE_CLASSES n16) ;;
  let j' := v_addiw j 0 in
  idx <- m_alloc_slot fuel' (at_ sp (-144)) j' a1 ;;
  if c_lts idx w0 then as_fail m
  else
    szj <- m_lhu (v_add A_SIZE_CLASSES (v_slli j' 1)) ;;
    gj <- m_ld (at_ (v_add A_LOCK (v_slli j' 3)) 88) ;;
    ctr <- m_lw (at_ A_LOCK 20) ;;
    p <- m_enframe gj idx (v_addi (v_slli szj 4) (-4)) ctr ;;
    wm <- m_ld (at_ m 32) ;;
    m_sd (at_ m 32) (v_srli (v_slli wm 52) 52) ;;
    c3 <- m_lbu (at_ p (-3)) ;;
    m_sb (at_ p (-3)) (v_addi (v_andi c3 31) 192) ;;
    zlF size (S (Z.to_nat (bv_unsigned cnt1))) (at_ p 12) ;;
    as_tail s7 pm sc m p cnt1 (v_addi cnt1 (-1)) (v_addi cnt1 (-1)).

(* [comment removed for export] *)
Definition as_bn (sc : word) : M (bool * option word) :=
  let d := v_addiw sc (-7) in
  if c_ltu (wlit 31) d then mret (false, None)
  else let a5 := v_add A_LOCK d in
       b <- m_lbu (at_ a5 888) ;;
       us <- m_lbu (at_ a5 856) ;;
       let nosmall := negb (c_ltu b (wlit 100)) in
       (if is0 us then mret tt
        else sq <- m_lbu (at_ A_LOCK 920) ;;
             if c_lts (wlit 9) (v_sub sq us) then mret tt
             else if c_ltu b (wlit 99) then m_sb (at_ a5 888) (v_addi b 1)
             else m_sb (at_ a5 888) (wlit 150)) ;;
       mret (nosmall, Some a5).

(* [comment removed for export] *)
Definition as_mm2 (s7 pm sc req m size usage pg cnt1 a4 : word) (nosmall : bool) (sq : word) : M word :=
    sq' <- (if c_eq sq (wlit 255)
            then m_sd (at_ A_LOCK 856) w0 ;; m_sd (at_ A_LOCK 864) w0 ;;
                 m_sd (at_ A_LOCK 872) w0 ;; m_sd (at_ A_LOCK 880) w0 ;; mret (wlit 1)
            else mret (v_addi sq 1)) ;;
    m_sb (at_ A_LOCK 920) sq' ;;
    usage2 <- (if c_lts (wlit 31) sc then mret usage
               else if negb (is0 (v_andi sc 1)) then mret usage
               else u1 <- m_ld (at_ s7 480) ;; mret (v_add u1 usage)) ;;
    mlet (
      if negb (c_ltu usage2 (v_slliw cnt1 2)) then cnt1
      else if nosmall then cnt1
      else let a5 := v_andi sc 3 in
           let a6 := v_slli pg 3 in
           if c_eq a5 (wlit 1) && c_ltu a6 a4 then wlit 2
           else if c_eq a5 (wlit 2) && c_ltu (v_slli pg 2) a4 then wlit 3
           else if is0 a5 && c_ltu a6 a4 then wlit 3
           else if is0 a5 && c_ltu (v_slli pg 1) a4 then wlit 5
           else cnt1) (fun cnt2 =>
    let needed0 := v_mul size cnt2 in
    mlet (v_addi (v_add needed0 (v_and (v_sub (wlit (2^64 - 16)) needed0) (v_addi pg (-1)))) 16) (fun needed =>
    mlet (
      if nosmall then (cnt2, needed)
      else if c_ltu (wlit 7) cnt2 then (cnt2, needed)
      else let r := v_addi (v_add req (v_and (v_addi pg (-1)) (v_sub (wlit (2^64 - 20)) req))) 20 in
           if c_ltu r (v_addi size 16) then (wlit 1, r)
           else if c_ltu r (v_slli pg 2) then (cnt2, needed)
           else if c_ltu usage2 (v_slliw cnt2 1) then (wlit 1, r)
           else (cnt2, needed)) (fun cn =>
    let '(cnt3, needed3) := cn in
    p <- sys_mmap MMrw needed3 ;;
    if c_eq p wm1 then as_fail m
    else
      wm <- m_ld (at_ m 32) ;;
      let aimax := v_divu (wlit 4080) size in
      ctr <- m_lw (at_ A_LOCK 20) ;;
      m_sd (at_ m 32) (v_or (v_srli (v_slli wm 52) 52) (v_and needed3 PAGEMASK)) ;;
      m_sw (at_ A_LOCK 20) (v_addi ctr 1) ;;
      mlet (if c_ltu cnt3 aimax then cnt3 else aimax) (fun a2 =>
      let aidx := v_and (v_addi (v_sltu a2 (v_addi a2 (-1))) (-1)) (v_addi a2 (-1)) in
      as_tail s7 pm sc m p cnt3 aidx (v_addi cnt3 (-1)))))).

(* [comment removed for export] *)
Definition as_mmapg (s7 pm sc req m size usage pg cnt1 a4 : word) : M word :=
  bn <- as_bn sc ;;
  let '(nosmall, _) := bn in
  sq <- m_lbu (at_ A_LOCK 920) ;;
  as_mm2 s7 pm sc req m size usage pg cnt1 a4 nosmall sq.

(* [comment removed for export] *)
Definition as_group (fuel' : nat) (sp s7 pm sc req : word) : M word :=
  szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;
  m <- m_alloc_meta (at_ sp (-64)) ;;
  if is0 m then mret wm1
  else
  usage <- m_ld (at_ s7 472) ;;
  pg <- m_ld A_PAGE_SIZE ;;
  let size := v_slli szc 4 in
  cnt <- as_cnt sc usage size ;;
  let half := v_srli pg 1 in
  mlet (if c_eq cnt (wlit 1)
        then v_subw (wlit 2) (v_sltu half (v_addi size 16))
        else cnt) (fun cnt1 =>
  let a4 := v_mul size cnt1 in
  if negb (c_ltu half (v_addi a4 16))
  then as_nested fuel' sp s7 pm sc m size cnt1 a4
  else as_mmapg s7 pm sc req m size usage pg cnt1 a4).

(* [comment removed for export] *)
Definition as_res (fuel' : nat) (sp s7 pm sc req : word) : M word :=
  m0 <- m_ld pm ;;
  ta <- as_tav pm m0 ;;
  match ta with
  | Some (m, mask) => as_take m mask
  | None => as_group fuel' sp s7 pm sc req
  end.

Lemma m_alloc_slot_pieces : forall fuel' sp sc req,
  m_alloc_slot (S fuel') sp sc req =
  (cc <- m_canary_load ;;
   let '(gp, cg) := cc in
   let s7 := v_add A_LOCK (v_slli sc 3) in
   let pm := at_ s7 88 in
   res <- as_res fuel' sp s7 pm sc req ;;
   m_canary_check gp cg ;;
   mret res).
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "p'0h02cci002cch15fuel'h22pmh33reqh43resh52s7h62sch72spi012cgi022gpp;1p;2p;6p;3p;4g004@j10Tg004ej1@Tg005Cj15Tg003?j14Tg00JGR0j2?Tg00Jgj1;Tg00L3j1:Tg00?Nj11Tg005fj13Tg00M;j26Tg00C8j27Tg00N6j28Tg00Nkj69Tg00P0j3>Tg0000j2=Tg0014j42Tg00<Vj2<Tg00=Ug00=0R1#0R2#0#0#0#0#0#@#5R3%43R41?33R5P3p,2MLR6#;P0P3P3P4f0R4%:6f4R0%11#3'6'7P3%12#1#0#0#0#3,84P3P3P3f8f7f1R2P4f6f5E9g00E4R4P3f39>601=32V4C2X43C2b2b5n2001100000120102101X05C2'<X33X63W7W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_newarea (pagesize : word) : M (option (word * bool)) :=
  sh <- m_ld A_META_SHIFT ;;
  let n := v_sll (wlit 2) sh in
  p <- sys_mmap MMnone (v_mul n pagesize) ;;
  if c_eq p wm1 then MallocTree.mret None
  else sh2 <- m_ld A_META_SHIFT ;;
       m_sd A_AVAIL_AREA_CNT (v_mul (v_addi n (-1)) (v_srli pagesize 12)) ;;
       m_sd A_META_SHIFT (v_addi sh2 1) ;;
       m_sd A_AVAIL_AREAS (v_add p pagesize) ;;
       MallocTree.mret (Some (v_add p pagesize, true)).

(* [comment removed for export] *)
Definition am_brk (pagesize cb : word) : M (option (word * bool)) :=
  if c_eq cb wm1 then MallocTree.mret None
  else if negb (is0 cb)
  then let new := v_add cb pagesize in
       r <- sys_brk_grow new ;;
       MallocTree.mret (Some (new, c_eq r new))
  else r0 <- sys_brk_query ;;
       let al := v_add (v_and (v_addi pagesize (-1)) (v_sub MallocOps.w0 r0)) r0 in
       m_sd A_BRK al ;;
       let new := v_add al (v_slli pagesize 1) in
       r <- sys_brk_grow new ;;
       (if c_eq r new
        then b <- m_ld A_BRK ;;
             g <- sys_mmap_fixed_none b pagesize ;;
             MallocTree.mret (Some (new, true))
        else MallocTree.mret (Some (new, false))).

(* [comment removed for export] *)
Definition am_areas (pagesize aac2 : word) : M (option (word * bool)) :=
  if negb (is0 aac2) then p <- m_ld A_AVAIL_AREAS ;; MallocTree.mret (Some (p, true))
  else am_newarea pagesize.

(* [comment removed for export] *)
Definition am_prov (pagesize aac : word) : M (option (word * bool)) :=
  if negb (is0 aac)
  then p <- m_ld A_AVAIL_AREAS ;; MallocTree.mret (Some (p, true))
  else
    cb <- m_ld A_BRK ;;
    br <- am_brk pagesize cb ;;
    match br with
    | Some (new, true) =>
        m_sd A_BRK new ;;
        m_sd A_AVAIL_AREA_CNT (v_srli pagesize 12) ;;
        MallocTree.mret (Some (v_sub new pagesize, false))
    | _ =>
        aac2 <- (match br with
                 | Some _ => a <- m_ld A_AVAIL_AREA_CNT ;; m_sd A_BRK wm1 ;; MallocTree.mret a
                 | None => MallocTree.mret aac end) ;;
        am_areas pagesize aac2
    end.

(* [comment removed for export] *)
Definition am_tail (p : word) : M word :=
    aac3 <- m_ld A_AVAIL_AREA_CNT ;;
    tl <- m_ld A_AREA_TAIL ;;
    m_sd A_AVAIL_AREA_CNT (v_addi aac3 (-1)) ;;
    m_sd A_AVAIL_AREAS (v_add p (wlit 4096)) ;;
    (if is0 tl then m_sd A_AREA_HEAD p
     else m_sd (at_ tl 8) p) ;;
    sec <- m_ld A_CTX ;;
    m_sd A_AREA_TAIL p ;;
    m_sd p sec ;;
    t1 <- m_ld A_AREA_TAIL ;;
    m_sw (at_ t1 16) (wlit 101) ;;
    t2 <- m_ld A_AREA_TAIL ;;
    let m := at_ t2 24 in
    m_sd A_AVAIL_META (at_ m 40) ;;
    m_sd A_AVAIL_META_CNT (wlit 100) ;;
    m_sd (at_ m 8) MallocOps.w0 ;; m_sd m MallocOps.w0 ;;
    MallocTree.mret m.

(* [comment removed for export] *)
Definition am_okc (pagesize p : word) (test : bool) : M bool :=
  if test && is0 (v_and (v_addi pagesize (-1)) p)
  then pg2 <- m_ld A_PAGE_SIZE ;;
       massert (c_eq pg2 (wlit 4096)) ;;
       r <- sys_mprotect_rw p pagesize ;;
       if is0 r then MallocTree.mret true
       else e <- m_lw A_ERRNO ;; MallocTree.mret (c_eq e (wlit 38))
  else MallocTree.mret true.

Definition am_some (pagesize p : word) (test : bool) : M word :=
  ok <- am_okc pagesize p test ;;
  if negb ok then MallocTree.mret MallocOps.w0
  else am_tail p.

(* [comment removed for export] *)
Definition am_res (pagesize : word) : M word :=
  fmh <- m_ld A_FREE_META_HEAD ;;
  if negb (is0 fmh) then
    let m := fmh in
    nx <- m_ld (at_ m 8) ;;
    (if c_eq nx m then m_sd A_FREE_META_HEAD MallocOps.w0
     else pv <- m_ld m ;;
          m_sd (at_ pv 8) nx ;;
          pv2 <- m_ld m ;;
          nx2 <- m_ld (at_ m 8) ;;
          m_sd nx2 pv2 ;;
          h <- m_ld A_FREE_META_HEAD ;;
          if c_eq h m then n3 <- m_ld (at_ m 8) ;; m_sd A_FREE_META_HEAD n3
          else MallocTree.mret tt) ;;
    m_sd (at_ m 8) MallocOps.w0 ;; m_sd m MallocOps.w0 ;;
    MallocTree.mret m
  else
  amc <- m_ld A_AVAIL_META_CNT ;;
  if negb (is0 amc) then
    m <- m_ld A_AVAIL_META ;;
    m_sd A_AVAIL_META (at_ m 40) ;;
    m_sd A_AVAIL_META_CNT (v_addi amc (-1)) ;;
    m_sd (at_ m 8) MallocOps.w0 ;; m_sd m MallocOps.w0 ;;
    MallocTree.mret m
  else
  aac <- m_ld A_AVAIL_AREA_CNT ;;
  r <- am_prov pagesize aac ;;
  match r with
  | None => MallocTree.mret MallocOps.w0
  | Some (p, test) => am_some pagesize p test
  end.

(* [comment removed for export] *)
Definition am_init (sp : word) : M unit :=
  auxv <- m_ld (at_ A_LIBC 8) ;;
  let s0 := v_mul sp (wlit 0x41c64e6d) in
  sec <- m_scan_auxv AUXV_FUEL auxv MallocOps.w0 s0 ;;
  m_sd A_CTX sec ;;
  m_sw A_INIT_DONE (wlit 1).

Lemma m_alloc_meta_pieces : forall sp,
  m_alloc_meta sp =
  (cc <- m_canary_load ;;
   let '(gp, cg) := cc in
   ini <- m_lw A_INIT_DONE ;;
   (if negb (is0 ini) then MallocTree.mret tt else am_init sp) ;;
   pg <- m_ld (at_ A_LIBC 48) ;;
   massert (c_eq pg (wlit 4096)) ;;
   let pagesize := if c_ltu (wlit 4096) pg then pg else wlit 4096 in
   res <- am_res pagesize ;;
   m_canary_check gp cg ;;
   MallocTree.mret res).
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "p'0h02cci002cch13inih28pagesizeh32pgh43resh52spi012cgi022gpp;1p;2p;3p;4g004ej1ITg005Cj1;Tg003?j13Tg00JGR0j2HTg00Jgj1DTg00Q=j1<Tg00RJj2:Tg007?j18Tg008Aj17Tg0000j22Tg00SNj16Tg00TTj19Tg00?Nj1GTg005fj15Tg00N6j2FTg00U\j2CTg00V`j1=Tg00Wcj2>Tg00X\j1?Tg009[j2@Tg00Ycj1ATg00P0j3BTg0014j41Tg00<Vj2ETg004@j14Tf0R1#4#4p=0g00=0R2#0#0#0R3#I#;R4%34R51H44R6P4p,2MLR7#DP0P4P4P5P1P4P4%<7,:7g00E4R5P4g00>4R0%35%81#7g00FU,25f4#6n0100000020000P4P4%97%G2#0#0#5'F,C7P5P4%03#0#0#5#=R3,>1#?P0P4f1R0,@3P0P3n0100000020000P4P4P4%A1P5P4f7f65B71240V5C1X44C1b2V5C1X34C1V5C1X14C1n2001100000121102101X06C1'EW5o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aslot_at {fx : FPState} (fuel : nat) : Prop :=
  forall md regs mm rom (s : mstate) (sc req sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - alloc_slot_D fuel -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = sc -> getr regs 11 = req ->
  tsafe (m_alloc_slot fuel (at_ sp (-144)) sc req s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ALLOC_SLOT mm rom) md)
           (tshape (m_alloc_slot fuel (at_ sp (-144)) sc req s) L).

Lemma alloc_slot_stmt_of_at {fx : FPState} : (forall fuel, aslot_at fuel) -> alloc_slot_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h01ah14fuelh21Hh31Lh41Ph52fxh62mdh72mmh83mm'h91rh:4regsh;5regs'h<3reqh=3reth>3romh?1sh@2s'hA2schB2sphC1xp;2p;1p;3p;6p;5g00Zhj2ZTg004@j10Tg00?Nj1>Tg004ej1<Tg005Cj1ATg00[oj2VTg00\[j1RTg00]=j1QTg00^<j19Tg00_Aj1LTg00`8j31Tg00`Rj2CTg005fj14Tg00aYj38Tg00b<j25Tg00bfj2UTg00cFj17Tg00dKj22Tg00dgj1?Tg00f1j2@Tg00fNj16Tg00gSj2PTg00h0j1OTg00i1j2:Tg00iMj2;Tg00ihj1MTg00jJj1=Tg00jcj1KTg00k[j1ITg00laj1JTg00N6j2HTg00m?j6GTg00nJj3NTg00oOj1BTg010Gj1FTg011Jj2DTg012Cj1ETg013Lj5STg014Ej2TTg015?j2YTg0164j3XTg0173j2WTf3R0f2R1f1R2'Df0R331p=3g018@g00=UR41Z23]1g019>g00=0R5#0R6#>R7#<R8%06R9#0R:#0R;#0#0R<#<R=#AR>'VR?%<:#AR:#RR@\>RAg00I?RBp-0\B\>g01:4\B\>f;RC#Qg01:mf8RD#9f<RE#L31f9RF/CCP>f=RG%46R6g01;dRH588RIf6RJC3g01<@RKf7RL,5=%4;'Ug01<^R;31%7E,2;%7G15=F%?E'@'2f:R;,5=f>RM#6'2f?RN#6%4<,P6'2f@R6#O15=MR<fARO#?'@15=3RP'21:P<';fER<P2O1%M:R:51@#=[^0>P>P<%45=88HPGC3%KMP>fGR5%49=88Hp,2MLRQ#IC3P>fHRR%07#4=88HRSfCRTC3P>fIRU%>7#4=88HPTC3PQfFRH%>9#0#0#0#0#J,HTP<fDR9P5EG=N>OPHP0P1O21C01f4R7#7fNRV#751Kf5RW#6fORX#651K%9J#BfP#9#B51KP>PWPSPDC3P>PJPIPVC3%A8%F3P>PFP2fX/D2C3[]CfUR8#7/2P%68,:P';fR,5=RI%?8'@R815=2R='21:=I';#=PEP1O1fYP1O151@[[^0>128P1:PI';PEP2O1=1@:#=[^0>%EQf\P;fQPCfWDS%9EfZ'T'YPXPGPEO23X[[[[[[[[[[^;?^8A^@B^9>PVPRfMfLfKfJPUP5PHP<P9PTfBPOP6PNPMPGPEPCP;PFPDPLPJPWP7P0P1P2P3ONUUUUUUUUUUUUUUUUUUW3W4X=>XB>X<>XA>X14W?X>AW7W:W61W2QeW2W5o"). Qed.

Lemma alloc_slot_D_S : forall f, alloc_slot_D (S f) = alloc_slot_D f + 144.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h04__x1h17__arithh24__ffh38__varmaph45__with54cstrh61fh71zp;1p;2p;3p;4p;7p;6g01=<j12Tg01=\j1MTg004@j11Tg00?Nj1=Tg005fj19Tg01>:j25Tg01>Wj20Tg00`8j33Tg01?4j1?Tg00dKj2>Tg01?Yj1<Tg01@9j1;Tg01@Yj2:Tg01A7j1LTg01AUj1KTg01B@j26Tg01Bcj2JTg01CFj34Tg01Cij37Tg01DLj4DTg01E7j7CTg01E[j2BTg00<Vj2ATg01F=j2@Tg01Fij3ETg01GHj4FTg01H:j1GTg01HYj1HTg01I=j6ITg00dgj18Tg00=Ug01<@R0f0R1#2R2#Mg00=0R3#1#1#=#1#1#1#1#9R4/51/04R5f1R6#2,54/04/04530X70%?1g01<^R7/>2g01I[R2#<%;21:06%L0%K0R2g01JGg00E4R8P8g01JfR8P01604R91J03R:%93R3,60540570=409g01KFA709:=409=409CDg00FUFC1B28P1f2R8g00>4R2g01KmR9'A1@18=329dAE076CFb2b3b4X001013,54/041054530^00P1%28O1b1b5%G1R8#2%H1EI%88%81/04530eW6o"). Qed.
Lemma alloc_slot_D_ge : forall f, 144 <= alloc_slot_D f.
Proof.
ltac2:(KReplay.run1 (kr_t_RefPieces ()) ["WithLayout"] "h04__x1h17__arithh24__ffh38__varmaph45__with54cstrh61fp;1p;2p;3p;4p;8p;7g01?4j1RTg01=<j13Tg00dKj21Tg01LMj26Tg01H:j17Tg01M6j3LTg01M_j2@Tg01NKj2?Tg01?Yj1=Tg01O7j3<Tg01@9j1;Tg01@Yj28Tg01A7j19Tg01AUj1QTg01B@j22Tg01Bcj2PTg01DLj44Tg00ihj1KTg004@j10Tg00?Nj1ATg005fj1BTg01Cij3>Tg01CFj3CTg01OWj8DTg01E[j2ETg00<Vj2FTg01F=j2GTg00`8j3HTg01Fij3ITg01GHj4JTg01>:j2:Tg01>Wj2MTg00dgj1NTg01E7j7OTf1R0g01JGR1g00E4R2P2g01JfR3f0R4g00FUFOp=5g00=U%R4g01<^R5%34'1g01<@R6g01I[R7g01P;R8,66R9%78#7,669L69g01PZ'@'?%=73<%;71860%96%Q6R7P1P2P2P3P61265g01QFR1g00=0R9,P6R8C4,57%K2P6%09#0#A#0#0#0#0#BR9,26R2P1A>628=C62C4,57GD1E73P4f2R7g00>4R3g01KmR2'F1G47=H32dAI650CJb2b3b4W011541:90/M9,19[^06P4%37P0O2b1b5%N4,19eW6o"). Qed.

End WithLayout.
