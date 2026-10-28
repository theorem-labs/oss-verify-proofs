(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_z4kx.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4kx2 () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx8z4kx_ctxC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic3and00C46Stdlib5Lists4List:Forall_appC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5mulop01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03I46Stdlib5Lists4List6Exists00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop07I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4kx2:z4_R5_casec5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4kx2:z4_R2_caseC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4kx2:z4_E1_caseK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4kx2:z4_E2_caseC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;tab_img_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXTac=ztab_fact_imgI47Corelib4Init5Logic2or00c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4kx2;z4_ctz_tab2K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6all_roC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7all_romC5ARocqVerifyHarness?AgentSubmission6Common4KXGo9zr_ok_imgK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01C56Stdlib6ZArith6BinInt1Z3oppC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9kx_mul_m1K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4kx29z4_S_case".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Definition z4_R5_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH P : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    SS <= P -> P + 8 <= SS + n ->
    (forall (ra s0 s1 a3 t1 t5 : word),
       evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 t1 x7 s0 s1 (Z_to_bv 64 P) x11 x12 a3 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 x27 x28 x29 t5 x31)
                            F (Z_to_bv 64 0x86d3c) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17
                             x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x86ccc) fc None mm (seg_rom bsegs)).

Theorem z4_R5 : z4_R5_case.
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH P C P1 P2 K.
  z4kx_intro C.
  kx_runFm [0x86d3c] 60%nat
    [KZRange P 4096 (2^47); KZRange SS 4096 (2^47); KZRange n 8 (2^47); KZRange (SS + n - P) 8 (2^47); KZRange (P - SS) 0 (2^47)]
    [(P, 8)] [] [(P, 8)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; apply (proj2 (proj2 WS)); lia end)).
  kx_post_regs_keep.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR ?ra _ _ _ _ ?t1 _ ?s0 ?s1 _ _ _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?t5 _) _ _ _ _ _ _) =>
      eapply evtF_eq; [| apply (K ra s0 s1 a3 t1 t5)]
  end.
  all: try (lazymatch goal with |- @eq machine_state _ _ =>
    (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
Time Qed.

Definition z4_R2_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH P : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    SS <= P -> P + 8 <= SS + n ->
    (forall (ra s0 s1 s8 a3 t1 t5 : word),
       evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 t1 x7 s0 s1 (Z_to_bv 64 P) x11 x12 a3 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) s8 x25 x26 x27 x28 x29 t5 x31)
                            F (Z_to_bv 64 0x87430) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17
                             x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x873c0) fc None mm (seg_rom bsegs)).

Theorem z4_R2 : z4_R2_case.
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH P C P1 P2 K.
  z4kx_intro C.
  kx_runFm [0x87430] 60%nat
    [KZRange P 4096 (2^47); KZRange SS 4096 (2^47); KZRange n 8 (2^47); KZRange (SS + n - P) 8 (2^47); KZRange (P - SS) 0 (2^47)]
    [(P, 8)] [] [(P, 8)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; apply (proj2 (proj2 WS)); lia end)).
  kx_post_regs_keep.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR ?ra _ _ _ _ ?t1 _ ?s0 ?s1 _ _ _ ?a3 _ _ _ _ _ _ _ _ _ _ ?s8 _ _ _ _ _ ?t5 _) _ _ _ _ _ _) =>
      eapply evtF_eq; [| apply (K ra s0 s1 s8 a3 t1 t5)]
  end.
  all: try (lazymatch goal with |- @eq machine_state _ _ =>
    (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
Time Qed.

Definition z4_E1_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH P : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    SS <= P -> P + 8 <= SS + n ->
    (forall (ra s1 a3 t1 t5 s11 : word),
       bv_unsigned s11 <= 7 ->
       evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 (Z_to_bv 64 P) x11 x19 a3 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 s11 x28 x29 t5 x31)
                            F (Z_to_bv 64 0x8733c) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17
                             x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x872b4) fc None mm (seg_rom bsegs)).

Theorem z4_E1 : z4_E1_case.
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH P C P1 P2 K.
  z4kx_intro C.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x8733c] 60%nat
    [KZRange P 4096 (2^47); KZRange SS 4096 (2^47); KZRange n 8 (2^47); KZRange (SS + n - P) 8 (2^47); KZRange (P - SS) 0 (2^47);
     KZRange DT4 4096 (2^47); KZRange SP 4096 (2^47); KZWord (SP + 128) 8 DT4]
    [(P, 8); (SP + 128, 8)] [] [(P, 8)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA;
          first [apply (proj2 (proj2 WS)); lia | apply (proj2 (proj2 WF)); lia] end)).
  kx_post_regs_keep.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR ?ra _ _ _ _ ?t1 _ _ ?s1 _ _ _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ ?s11 _ _ ?t5 _) _ _ _ _ _ _) =>
      eapply evtF_eq; [| apply (K ra s1 a3 t1 t5 s11)]
  end.
  all: try (lazymatch goal with |- @eq machine_state _ _ =>
    (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
  all: (lazymatch goal with |- bv_unsigned _ <= 7 =>
    cbn [edenot]; rewrite u_and64, Z_to_bv_unsigned; unfold bv_wrap; change (7 mod bv_modulus 64) with 7;
    apply land_le_r; [apply bv_unsigned_in_range | lia] end).
Time Qed.

Definition z4_E2_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH P NB B : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    SS <= P -> P + 8 <= SS + n -> 0 <= NB -> 8 * NB <= B <= 64 ->
    (forall (ra s1 a3 t1 t5 : word),
       evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 (Z_to_bv 64 P) x11 x19 a3 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 (Z_to_bv 64 (B - 8 * NB)) x28 x29 t5 x31)
                            F (Z_to_bv 64 0x87290) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 (Z_to_bv 64 NB) x14 x15 x16 x17
                             x18 x19 x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 x26 (Z_to_bv 64 B) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x87204) fc None mm (seg_rom bsegs)).

Theorem z4_E2 : z4_E2_case.
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH P NB B C P1 P2 P3 P4 K.
  z4kx_intro C.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x87290] 60%nat
    [KZRange P 4096 (2^47); KZRange SS 4096 (2^47); KZRange n 8 (2^47); KZRange (SS + n - P) 8 (2^47); KZRange (P - SS) 0 (2^47);
     KZRange DT4 4096 (2^47); KZRange SP 4096 (2^47); KZRange NB 0 8; KZRange B 0 64; KZRange (B - 8 * NB) 0 64;
     KZWord (SP + 128) 8 DT4]
    [(P, 8); (SP + 128, 8)] [] [(P, 8)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA;
          first [apply (proj2 (proj2 WS)); lia | apply (proj2 (proj2 WF)); lia] end)).
  kx_post_regs_keep.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR ?ra _ _ _ _ ?t1 _ _ ?s1 _ _ _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?t5 _) _ _ _ _ _ _) =>
      eapply evtF_eq; [| apply (K ra s1 a3 t1 t5)]
  end.
  all: try (lazymatch goal with |- @eq machine_state _ _ =>
    (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
Time Qed.

(* [comment removed for export] *)
Lemma z4_ctz_tab2 : forall mm, mem_inv bsegs mm -> ztab_fact bsegs mm 0x20d53 64 1 [(0, 0, 63)].
Proof.
  intros mm MI. apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity].
Qed.

Lemma z4_srl58_bound : forall w : word, 0 <= bv_unsigned (alu64 ALU_SRL w (Z_to_bv 64 58)) < 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R.
  rewrite <- (Z_to_bv_bv_unsigned w), srl_lit_ez, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616 in *.
  change (58 mod 64) with 58. try change (2^58) with 288230376151711744. try change (2^64) with 18446744073709551616.
  set (u := bv_unsigned w) in *. clearbody u. Z.div_mod_to_equations. lia.
Qed.

Ltac z4_acc_ctz WI :=
  lazymatch goal with |- accP _ _ _ =>
    unfold accP, adenot; cbn [a_base a_off edenot fst snd];
    lazymatch goal with |- context [alu64 ALU_SRL ?w (Z_to_bv 64 58)] =>
      let SB := fresh "SB" in pose proof (z4_srl58_bound w) as SB;
      let Y := fresh "Y" in set (Y := alu64 ALU_SRL w (Z_to_bv 64 58)) in *; clearbody Y end;
    rewrite ?alu_add; unfold v_add, PropExec.v_addi; rewrite ?Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 64) with 18446744073709551616; change (bv_modulus 12) with 4096;
    rewrite ?(Z.mod_small _ 18446744073709551616) by lia; rewrite ?(Z.mod_small _ 4096) by lia;
    apply (proj2 (proj2 WI)); lia
  end.

Definition z4_S_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (x1 gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH IP K8 OP SE BW : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    SS <= IP -> IP + 8 <= SS + n -> K8 = 0 \/ K8 = 8 \/ K8 = 16 \/ K8 = 24 ->
    rw_cells bsegs mm (SP + 208 + K8) [C8 (Z_to_bv 64 BW)] -> 1 <= BW < 2^64 ->
    rw_cells bsegs mm (SP + 248) [C8 (Z_to_bv 64 SS)] ->
    DST <= OP -> OP <= SE -> SE <= DST + dcap ->
    (forall (ra s1 a3 t5 s11 : word),
       bv_unsigned s11 <= 63 -> 8 <= SE - OP ->
       evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 s1 (Z_to_bv 64 IP) (Z_to_bv 64 (SE - OP)) (Z_to_bv 64 OP) a3
                                 x14 x15 x16 (Z_to_bv 64 9) x18 (Z_to_bv 64 OP) (Z_to_bv 64 SE) (Z_to_bv 64 SS)
                                 (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SE - 9)) (Z_to_bv 64 SE)
                                 (Z_to_bv 64 0x20d53) s11 x28 x29 t5 x31)
                            F (Z_to_bv 64 0x86c7c) fc None mm (seg_rom bsegs))) ->
    (forall (ra s1 a3 s8 t5 s11 : word),
       bv_unsigned s11 <= 63 -> SE - OP < 8 ->
       evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 s1 (Z_to_bv 64 IP) (Z_to_bv 64 (SE - OP)) (Z_to_bv 64 8) a3
                                 x14 x15 x16 (Z_to_bv 64 9) x18 (Z_to_bv 64 OP) (Z_to_bv 64 SE) (Z_to_bv 64 SS)
                                 (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 0x7fff8000) s8 (Z_to_bv 64 SE)
                                 (Z_to_bv 64 0x20d53) s11 x28 x29 t5 x31)
                            F (Z_to_bv 64 0x871d8) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 IP) (Z_to_bv 64 K8) x12 x13
                             x14 x15 x16 (Z_to_bv 64 9) x18 (Z_to_bv 64 OP) x20 x21 x22 (Z_to_bv 64 0x7fff8000) x24
                             (Z_to_bv 64 SE) (Z_to_bv 64 0x20d53) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x86bac) fc None mm (seg_rom bsegs)).

Theorem z4_S : z4_S_case.
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH IP K8 OP SE BW C P1 P2 P3 HB HBW HL P4 P5 P6 K1 K2.
  z4kx_intro C.
  pose proof (z4_ctz_tab2 mm MI) as CT.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 208 + K8) _ HB) as HBB.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 248) _ HL) as HLB.
  assert (HBL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 BW)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  assert (HLL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 SS)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  assert (K8R : 0 <= K8 <= 24) by lia.
  destruct (Z_lt_ge_dec (SE - OP) 8) as [LT|GE].
  - kx_runFm [0x86c7c; 0x871d8] 80%nat
      [KZRange IP 4096 (2^47); KZRange SS 4096 (2^47); KZRange n 8 (2^47); KZRange (SS + n - IP) 8 (2^47); KZRange (IP - SS) 0 (2^47);
       KZRange SP 4096 (2^47); KZRange K8 0 24; KZRange BW 1 (2^64 - 1); KZRange OP 4096 (2^47); KZRange SE 4096 (2^47);
       KZRange (SE - OP) 0 7; KZTab 0x20d53 64 1 [(0, 0, 63)];
       KZWord (SP + 208 + K8) 8 BW; KZWord (SP + 248) 8 SS]
      [(IP, 8); (SP + 208 + K8, 8); (SP + 248, 8); (0x20d53, 64)] [] [(IP, 8)].
    all: try (z4br).
    all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
    all: try ((lazymatch goal with |- accP _ _ _ =>
            unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA;
            first [apply (proj2 (proj2 WS)); lia | apply (proj2 (proj2 WF)); lia] end)).
    all: try ((z4_acc_ctz WI)).
    kx_post_regs_keep.
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR ?ra _ _ _ _ _ _ _ ?s1 _ _ _ ?a3 _ _ _ _ _ _ _ _ _ _ ?s8 _ _ ?s11 _ _ ?t5 _) _ _ _ _ _ _) =>
        eapply evtF_eq; [| apply (K2 ra s1 a3 s8 t5 s11)]
    end.
    all: try (lazymatch goal with |- @eq machine_state _ _ =>
      (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
    all: try (lia).
    all: try ((lazymatch goal with |- bv_unsigned _ <= _ =>
      match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end)).
  - kx_runFm [0x86c7c; 0x871d8] 80%nat
      [KZRange IP 4096 (2^47); KZRange SS 4096 (2^47); KZRange n 8 (2^47); KZRange (SS + n - IP) 8 (2^47); KZRange (IP - SS) 0 (2^47);
       KZRange SP 4096 (2^47); KZRange K8 0 24; KZRange BW 1 (2^64 - 1); KZRange OP 4096 (2^47); KZRange SE 4096 (2^47);
       KZRange (SE - OP) 8 (2^47); KZTab 0x20d53 64 1 [(0, 0, 63)];
       KZWord (SP + 208 + K8) 8 BW; KZWord (SP + 248) 8 SS]
      [(IP, 8); (SP + 208 + K8, 8); (SP + 248, 8); (0x20d53, 64)] [] [(IP, 8)].
    all: try (z4br).
    all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
    all: try ((lazymatch goal with |- accP _ _ _ =>
            unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA;
            first [apply (proj2 (proj2 WS)); lia | apply (proj2 (proj2 WF)); lia] end)).
    all: try ((z4_acc_ctz WI)).
    kx_post_regs_keep.
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR ?ra _ _ _ _ _ _ _ ?s1 _ _ _ ?a3 _ _ _ _ _ _ _ _ _ _ ?s8 _ _ ?s11 _ _ ?t5 _) _ _ _ _ _ _) =>
        eapply evtF_eq; [| apply (K1 ra s1 a3 t5 s11)]
    end.
    all: try (lazymatch goal with |- @eq machine_state _ _ =>
      (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
    all: try (lia).
    all: try ((lazymatch goal with |- bv_unsigned _ <= _ =>
      match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end)).
Time Qed.
