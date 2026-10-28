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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4kx () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx8z4kx_ctxC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invI47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic3and00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaI47Corelib4Init5Logic2eq00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okK46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem6replayC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_u8arr_replayC5ARocqVerifyHarness?AgentSubmission6Common5KXMem=replay_lengthK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop02I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03I46Stdlib5Lists4List6Exists00K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx9z4_T_casec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx9z4_L_casec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx:z4_D2_casec5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx=z4_sum5_boundc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_z4kx:z4_D5_case".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Notation amem := (word -> option byte).

(* [comment removed for export] *)
Definition z4kx_ctx (RNG : footprint) (mm : amem) (SP DT4 DBL DBH DST dcap SS n SBL SBH : Z) : Prop :=
  mem_inv bsegs mm
  /\ (exists tbl, bytes_at bsegs mm DT4 tbl /\ Z.of_nat (length tbl) = 8192)
  /\ ztab_fact bsegs mm DT4 8192 4 [(2, 0, 11); (3, 1, 2)]
  /\ (exists obuf, u8arr bsegs mm DST obuf /\ Z.of_nat (length obuf) = dcap)
  /\ (exists sbuf, bytes_at bsegs mm SS sbuf /\ Z.of_nat (length sbuf) = n)
  /\ rw_cells bsegs mm (SP + 128) [C8 (Z_to_bv 64 DT4)]
  /\ DT4 mod 4 = 0
  /\ unpoisoned mm DBL DBH /\ DBL <= DT4 /\ DT4 + 8192 <= DBH
  /\ unpoisoned mm DST (DST + dcap)
  /\ unpoisoned mm SBL SBH /\ SBL <= SS /\ SS + n <= SBH
  /\ rng RNG DT4 8192 /\ rng RNG DST dcap /\ rng RNG SS n /\ rng RNG SP 528 /\ rng_aimg RNG
  /\ rng RNG (shad DBL) (shlen (DBH - DBL + 7)) /\ rng RNG (shad DST) (shlen (dcap + 7))
  /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7))
  /\ DBL mod 8 = 0 /\ DST mod 8 = 0 /\ SBL mod 8 = 0
  /\ 0x60d000 <= DT4 /\ DT4 + 8192 <= 2^47 /\ 0x60d000 <= DST /\ DST + dcap <= 2^47
  /\ 0x60d000 <= SS /\ SS + n <= 2^47 /\ 0x10007fff8000 <= SP /\ SP + 528 <= 2^47
  /\ 0x60d000 <= DBL /\ DBH <= 2^47 /\ 0x60d000 <= SBL /\ SBH <= 2^47
  /\ apart DST dcap 0x7fff8000 17592186044416 /\ apart DST dcap DT4 8192 /\ apart DST dcap SS n /\ apart DST dcap SP 528.

Ltac z4kx_intro C :=
  let MI := fresh "MI" in let tbl := fresh "tbl" in let TB := fresh "TB" in let TL := fresh "TL" in let TF := fresh "TF" in
  let obuf := fresh "obuf" in let OB := fresh "OB" in let OL := fresh "OL" in
  let sbuf := fresh "sbuf" in let SB := fresh "SB" in let SL := fresh "SL" in
  destruct C as (MI & (tbl & TB & TL) & TF & (obuf & OB & OL) & (sbuf & SB & SL) & ?FR1 & ?FR2 & ?UT & ?UT1 & ?UT2 & ?UD
                 & ?US & ?US1 & ?US2 & ?WT & ?WD & ?WS & ?WF & ?WI & ?WTS & ?WDS & ?WSS & ?A8a & ?A8b & ?A8c
                 & ?R1 & ?R2 & ?R3 & ?R4 & ?R5 & ?R6 & ?R7 & ?R8 & ?R9 & ?R10 & ?R11 & ?R12 & ?AB & ?AT & ?AS & ?AF).

(* [comment removed for export] *)
Ltac z4_rng :=
  lazymatch goal with
  | |- ?lo <= bv_unsigned (ev ?E ?j) <= ?hi => let H := fresh "H" in kx_range (EVar j) H; exact H
  end.

Ltac z4ez :=
  repeat lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end.
Ltac z4br :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      z4ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia;
      first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
            | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
  end.

Lemma z4_idx_bound : forall w : word, 0 <= bv_unsigned (alu64 ALU_SRL (alu64 ALU_SRL w (Z_to_bv 64 51)) (Z_to_bv 64 2)) < 2048.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R.
  rewrite <- (Z_to_bv_bv_unsigned w), !srl_lit_ez, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616 in *.
  change (51 mod 64) with 51. change (2 mod 64) with 2. change (2^51) with 2251799813685248. change (2^2) with 4.
  change (2^64) with 18446744073709551616.
  set (u := bv_unsigned w) in *. clearbody u. Z.div_mod_to_equations. lia.
Qed.

Ltac z4w KXA :=
  repeat (match goal with |- context [ev ?E ?j] => rewrite (KXA j) by (cbn; lia) end); cbn [nth];
  try lazymatch goal with |- context [alu64 ALU_SRL (alu64 ALU_SRL ?w (Z_to_bv 64 51)) (Z_to_bv 64 2)] =>
    let IB := fresh "IB" in pose proof (z4_idx_bound w) as IB;
    let X := fresh "X" in set (X := alu64 ALU_SRL (alu64 ALU_SRL w (Z_to_bv 64 51)) (Z_to_bv 64 2)) in *; clearbody X end;
  rewrite ?alu_add, ?m_mul; unfold v_add, v_mul, PropExec.v_addi;
  change (bv_unsigned (Z_to_bv 64 4)) with 4;
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
  repeat match goal with |- context [?a mod 18446744073709551616] =>
    lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end.

Definition z4_T_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 b : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + 2 <= DST + dcap ->
    (forall (mm' : amem) (a0 a1 a3 t1 t5 : word) (nb len : Z),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       0 <= nb <= 11 -> 1 <= len <= 2 ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) x9 a0 a1 (Z_to_bv 64 (p + len)) a3 x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 (Z_to_bv 64 (bv_unsigned b + nb)) x28 x29 t5 x31)
                            F (Z_to_bv 64 0x87680) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DT4) x9 x10 x11 (Z_to_bv 64 p) x13 x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 b
                             x28 x29 x30 x31)
                        F (Z_to_bv 64 0x875e0) fc None mm (seg_rom bsegs)).

Theorem z4_T : z4_T_case.
Proof.
  intros Q RNG mm F fc c gp tp x5 x6 x7 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 b
    SP DT4 DBL DBH DST dcap SS n SBL SBH p C P1 P2 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  kx_runFm [0x87680] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - p) 2 (2^47); KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWr p 2; KZDisj p 2 DT4 8192; KZDisj p 2 2147450880 17592186044416]
    [(DT4, 8192)] [(p, 2)] [(DT4, 8192); (p, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; apply (proj2 (proj2 WT)); lia end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ _ ?a0 ?a1 (Z_to_bv 64 ?pl) ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a0 a1 a3 t1 t5 (bb - bv_unsigned b) (pl - p))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Definition z4_L_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x29 x30 x31 b : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + 1 <= DST + dcap ->
    (forall (mm' : amem) (a0 a1 a3 : word),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DT4) x9 a0 a1 (Z_to_bv 64 (p + 1)) a3 x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 b (Z_to_bv 64 2) x29 x30 x31)
                            F (Z_to_bv 64 0x875a8) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DT4) x9 x10 x11 (Z_to_bv 64 p) x13 x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 b
                             (Z_to_bv 64 2) x29 x30 x31)
                        F (Z_to_bv 64 0x8755c) fc None mm (seg_rom bsegs)).

Theorem z4_L : z4_L_case.
Proof.
  intros Q RNG mm F fc c gp tp x5 x6 x7 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x29 x30 x31 b
    SP DT4 DBL DBH DST dcap SS n SBL SBH p C P1 P2 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  kx_runFm [0x875a8] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - p) 1 (2^47); KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWr p 1; KZDisj p 1 DT4 8192; KZDisj p 1 2147450880 17592186044416]
    [(DT4, 8192)] [(p, 1)] [(DT4, 8192); (p, 1)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; apply (proj2 (proj2 WT)); lia end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p, 1)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a0 ?a1 _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a0 a1 a3)]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (lia).
Time Qed.

Definition z4_D2_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p B : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + 2 <= DST + dcap -> 0 <= B <= 7 ->
    (forall (mm' : amem) (a1 a3 s1 t1 t5 : word) (nb len : Z),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       0 <= nb <= 11 -> 1 <= len <= 2 ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 x10 a1 (Z_to_bv 64 (p + len)) a3 x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 (Z_to_bv 64 (B + nb)) x28 x29 t5 x31)
                            F (Z_to_bv 64 0x874f0) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 p) x13 x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 (Z_to_bv 64 B)
                             x28 x29 x30 x31)
                        F (Z_to_bv 64 0x8744c) fc None mm (seg_rom bsegs)).

Theorem z4_D2 : z4_D2_case.
Proof.
  intros Q RNG mm F fc c gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B C P1 P2 P3 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x874f0] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - p) 2 (2^47); KZRange B 0 7; KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWord (SP + 128) 8 DT4; KZWr p 2; KZDisj p 2 DT4 8192; KZDisj p 2 SP 528; KZDisj p 2 2147450880 17592186044416]
    [(DT4, 8192); (SP + 128, 8)] [(p, 2)] [(DT4, 8192); (p, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; first [apply (proj2 (proj2 WT)); lia | apply (proj2 (proj2 WF)); lia] end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ ?s1 _ ?a1 (Z_to_bv 64 ?pl) ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a1 a3 s1 t1 t5 (bb - B) (pl - p))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Lemma z4_sum5_bound : forall lo hi a b c d e, lo <= a <= hi -> lo <= b <= hi -> lo <= c <= hi -> lo <= d <= hi -> lo <= e <= hi ->
  5 * lo <= a + (b + (c + (d + e))) <= 5 * hi.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4kx ()) [] "h04__x1h14__x2h24__x3h34__x4h44__x5h54__x6h64__x7h77__arithh84__ffh98__varmaph:5__with;1ah<1bh=1ch>1dh?1eh@2hihA2lop;2p;1p;3p;4p;7p;8g009Dj26Tg00MXj11Tg00c9j2;Tg02[Oj2DTg00;;j1PTg00;[j3BTg00>Wj1ITg02X^j27Tg02\;j4@Tg00Wmj1XTg00XKj1UTg00_\j2FTg007`j1=Tg005Xj1>Tg00BSj1STg009`j1RTg00Y6j2QTg0297j3CTg02Y<j38Tg00YYj2OTg00Z;j2LTg00ZUj2KTg00_Bj3JTg00[Aj3HTg00[`j4MTg022Aj2ATg00:>j2:Tg00Jij2?Tg02Zfj3<Tg02Vkj4GTg02WVj7TTg02X:j7WTg02ZBj8VTf2R0f1R1'6f0R2'?p=Yf3R3/601612'?p=2g02aSR41;41;<2p=E1;401;41=<425<4p=91F42p=4P0g02doR5g02eNR6P6g02enR7P4P1g02fNP2CGg02g5FTp=0P0P5P6P6P7P1P2FWp=3P3P5P6P6P7P0P1P2GVp=51612,?0p=Nf6R5f4R8f5R9,68R:3Yf7R;P8P8P5C2f8R<P8P8P;C2f9R=P8P8P<C2f:R>P8P8P=C2g02jOR?g038VR@#1RA#1RB#1RC#1RD#1RE#1RF#1RG#1RH#1RI1;4@R@,EA99EC79Gg02icRG'D%1I1EB@99FD79H/DG%P?5B?3B%I?P4P41748P01745C@P1P41749P3174;C@C@%X4%U4R?g037TRG,F4RH%=GRF#>#4RD50?%=F#4R@90?D53?%S6R6P?%>GRG#=RB#4RI90?HA0?I@53?P6P?%>G#4RE90?HA0?E@53?P6P?%4FRF90?HA0?F@53?P6P?%4GRG90?HA0?G@53?P6%RBRB,Q4R6=C4HA84ID984E984F984GRG50?AC46@90?G53?C5C5C5C5C51O?7P2P0g02gUR?g02h5R7'L1K20=J?7dg02bf=H41CMb8b9b:X04X14X24X34X44X54X64P2P9P9P5C2P1P9P9P;C2P0P9P9P<C2P3P9P9P=C2AN:9>1AB91:=>,:<,:;,:5R:P:f;R:,ABC2[[[[[^04^14^24^34^44^54^64P2P:P5P;P<P=P>f<P1P0P3P8P9O<b7UUUUUX?4X>4X=4X<4X;4X@4XA4o"). Qed.

Ltac z4_rng5 :=
  lazymatch goal with
  | |- ?lo <= bv_unsigned (ev ?E ?j1) + (bv_unsigned (ev ?E ?j2) + (bv_unsigned (ev ?E ?j3) +
            (bv_unsigned (ev ?E ?j4) + bv_unsigned (ev ?E ?j5)))) <= ?hi =>
      let H1 := fresh "H" in let H2 := fresh "H" in let H3 := fresh "H" in let H4 := fresh "H" in let H5 := fresh "H" in
      kx_range (EVar j1) H1; kx_range (EVar j2) H2; kx_range (EVar j3) H3; kx_range (EVar j4) H4; kx_range (EVar j5) H5;
      exact (z4_sum5_bound _ _ _ _ _ _ _ H1 H2 H3 H4 H5)
  | |- _ => z4_rng
  end.

Lemma z4_shad_apart : forall DST dcap lo hi, apart DST dcap 0x7fff8000 17592186044416 -> 0 <= lo <= hi -> hi <= 2^47 ->
  disjoint_from [(DST, DST + dcap)] (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof.
  intros DST dcap lo hi A L H. unfold shad, ASHOFF, KXGoM.apart in *. rewrite !Z.shiftr_div_pow2 by lia.
  cbn [disjoint_from]. split; [|exact I]. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma z4_ztab_tr : forall mm mm' A N st fs tbl W,
  bytes_at bsegs mm A tbl -> Z.of_nat (length tbl) = N -> ztab_fact bsegs mm A N st fs ->
  munch W mm mm' -> disjoint_from W A N -> ztab_fact bsegs mm' A N st fs.
Proof.
  intros mm mm' A N st fs tbl W TB TL TF MU D z Z lo hi FF.
  destruct (TF z Z lo hi FF) as (b & RD & RB). exists b; split; [|exact RB].
  assert (TB' : bytes_at bsegs mm' A tbl) by (eapply bytes_at_transport; [exact TB | exact MU | rewrite TL; exact D]).
  pose proof (bytes_at_bound bsegs mm A tbl TB) as BB.
  assert (E : Z_to_bv 64 z = wa (A + Z.of_nat (Z.to_nat (z - A)))) by (unfold wa; f_equal; lia).
  rewrite E in RD |- *.
  rewrite (bytes_at_rdn bsegs mm A tbl (Z.to_nat (z - A)) 1 TB) in RD by lia.
  rewrite (bytes_at_rdn bsegs mm' A tbl (Z.to_nat (z - A)) 1 TB') by lia. exact RD.
Qed.

Lemma z4kx_ctx_tr : forall RNG mm mm' SP DT4 DBL DBH DST dcap SS n SBL SBH,
  z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
  munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
  (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
  z4kx_ctx RNG mm' SP DT4 DBL DBH DST dcap SS n SBL SBH.
Proof.
  intros RNG mm mm' SP DT4 DBL DBH DST dcap SS n SBL SBH C MU WM MI' OB'.
  z4kx_intro C. unfold z4kx_ctx.
  assert (DT : disjoint_from [(DST, DST + dcap)] DT4 8192) by (cbn [disjoint_from]; unfold KXGoM.apart in *; split; [lia | exact I]).
  assert (DS : disjoint_from [(DST, DST + dcap)] SS n) by (cbn [disjoint_from]; unfold KXGoM.apart in *; split; [lia | exact I]).
  repeat match goal with |- _ /\ _ => split end.
  all: first [ assumption
    | lazymatch goal with
      | |- exists t, bytes_at _ _ _ t /\ _ =>
          first [ exists tbl; split; [eapply bytes_at_transport; [exact TB | exact MU | rewrite TL; exact DT] | exact TL]
                | exists sbuf; split; [eapply bytes_at_transport; [exact SB | exact MU | rewrite SL; exact DS] | exact SL] ]
      | |- ztab_fact _ _ _ _ _ _ => exact (z4_ztab_tr mm mm' DT4 8192 4 _ tbl _ TB TL TF MU DT)
      | |- rw_cells _ _ _ _ => eapply rw_cells_transport; [exact FR1 | exact MU | exact WM |];
            cbn [disjoint_from cells_size csize Z.of_nat]; unfold KXGoM.apart in *; split; [lia | exact I]
      | |- unpoisoned _ ?lo ?hi => eapply unpoisoned_munch; [eassumption | exact MU | apply z4_shad_apart; [assumption | lia | lia]]
      end ].
Qed.

Definition z4_D5a_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p B : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + 2 <= DST + dcap -> 0 <= B <= 7 ->
    (forall (mm' : amem) (a1 s1 t1 t5 : word) (nb len : Z),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       0 <= nb <= 11 -> 1 <= len <= 2 ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 x10 a1 (Z_to_bv 64 p) (Z_to_bv 64 len) x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 (Z_to_bv 64 (B + nb)) x28 x29 t5 x31)
                            F (Z_to_bv 64 0x86df4) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 p) x13 x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 (Z_to_bv 64 B)
                             x28 x29 x30 x31)
                        F (Z_to_bv 64 0x86d54) fc None mm (seg_rom bsegs)).

Theorem z4_D5a : z4_D5a_case.
Proof.
  intros Q RNG mm F fc c gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B C P1 P2 P3 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x86df4] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - p) 2 (2^47); KZRange B 0 7; KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWord (SP + 128) 8 DT4; KZWr p 2; KZDisj p 2 DT4 8192; KZDisj p 2 SP 528; KZDisj p 2 2147450880 17592186044416]
    [(DT4, 8192); (SP + 128, 8)] [(p, 2)] [(DT4, 8192); (p, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; first [apply (proj2 (proj2 WT)); lia | apply (proj2 (proj2 WF)); lia] end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ ?s1 _ ?a1 _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a1 s1 t1 t5 (bb - B) (bv_unsigned a3))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (symmetry; apply Z_to_bv_bv_unsigned).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Definition z4_D5m_case (E X : Z) : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x9 x10 x11 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p B L : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + L + 2 <= DST + dcap -> 0 <= B <= 51 -> 1 <= L <= 2 ->
    (forall (mm' : amem) (a1 s1 t1 t5 : word) (nb len : Z),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       0 <= nb <= 11 -> 1 <= len <= 2 ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 x10 a1 (Z_to_bv 64 (p + L)) (Z_to_bv 64 len) x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 (Z_to_bv 64 (B + nb)) x28 x29 t5 x31)
                            F (Z_to_bv 64 X) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DT4) x9 x10 x11 (Z_to_bv 64 p) (Z_to_bv 64 L) x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 (Z_to_bv 64 B)
                             x28 x29 x30 x31)
                        F (Z_to_bv 64 E) fc None mm (seg_rom bsegs)).

Theorem z4_D5b : z4_D5m_case 0x86df4 0x86e94.
Proof.
  unfold z4_D5m_case; intros Q RNG mm F fc c gp tp x5 x6 x7 x9 x10 x11 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B L C P1 P2 P3 P4 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x86e94] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - (p + L)) 2 (2^47); KZRange B 0 51; KZRange L 1 2; KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWord (SP + 128) 8 DT4; KZWr (p + L) 2; KZDisj (p + L) 2 DT4 8192; KZDisj (p + L) 2 SP 528; KZDisj (p + L) 2 2147450880 17592186044416]
    [(DT4, 8192); (SP + 128, 8)] [(p + L, 2)] [(DT4, 8192); (p + L, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; first [apply (proj2 (proj2 WT)); lia | apply (proj2 (proj2 WF)); lia] end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8; change (2^64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p + L, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ ?s1 _ ?a1 _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a1 s1 t1 t5 (bb - B) (bv_unsigned a3))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (symmetry; apply Z_to_bv_bv_unsigned).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Theorem z4_D5c : z4_D5m_case 0x86e94 0x86f34.
Proof.
  unfold z4_D5m_case; intros Q RNG mm F fc c gp tp x5 x6 x7 x9 x10 x11 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B L C P1 P2 P3 P4 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x86f34] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - (p + L)) 2 (2^47); KZRange B 0 51; KZRange L 1 2; KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWord (SP + 128) 8 DT4; KZWr (p + L) 2; KZDisj (p + L) 2 DT4 8192; KZDisj (p + L) 2 SP 528; KZDisj (p + L) 2 2147450880 17592186044416]
    [(DT4, 8192); (SP + 128, 8)] [(p + L, 2)] [(DT4, 8192); (p + L, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; first [apply (proj2 (proj2 WT)); lia | apply (proj2 (proj2 WF)); lia] end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8; change (2^64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p + L, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ ?s1 _ ?a1 _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a1 s1 t1 t5 (bb - B) (bv_unsigned a3))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (symmetry; apply Z_to_bv_bv_unsigned).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Theorem z4_D5d : z4_D5m_case 0x86f34 0x86fd4.
Proof.
  unfold z4_D5m_case; intros Q RNG mm F fc c gp tp x5 x6 x7 x9 x10 x11 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B L C P1 P2 P3 P4 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x86fd4] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - (p + L)) 2 (2^47); KZRange B 0 51; KZRange L 1 2; KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWord (SP + 128) 8 DT4; KZWr (p + L) 2; KZDisj (p + L) 2 DT4 8192; KZDisj (p + L) 2 SP 528; KZDisj (p + L) 2 2147450880 17592186044416]
    [(DT4, 8192); (SP + 128, 8)] [(p + L, 2)] [(DT4, 8192); (p + L, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; first [apply (proj2 (proj2 WT)); lia | apply (proj2 (proj2 WF)); lia] end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8; change (2^64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p + L, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ ?s1 _ ?a1 _ ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a1 s1 t1 t5 (bb - B) (bv_unsigned a3))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ => repeat f_equal end).
  all: try (symmetry; apply Z_to_bv_bv_unsigned).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Definition z4_D5e_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x9 x10 x11 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p B L : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + L + 2 <= DST + dcap -> 0 <= B <= 51 -> 1 <= L <= 2 ->
    (forall (mm' : amem) (a1 a3 s1 t1 t5 : word) (nb len : Z),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       0 <= nb <= 11 -> 1 <= len <= 2 ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 x10 a1 (Z_to_bv 64 (p + L + len)) a3 x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 (Z_to_bv 64 (B + nb)) x28 x29 t5 x31)
                            F (Z_to_bv 64 0x87078) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DT4) x9 x10 x11 (Z_to_bv 64 p) (Z_to_bv 64 L) x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 (Z_to_bv 64 B)
                             x28 x29 x30 x31)
                        F (Z_to_bv 64 0x86fd4) fc None mm (seg_rom bsegs)).

Theorem z4_D5e : z4_D5e_case.
Proof.
  intros Q RNG mm F fc c gp tp x5 x6 x7 x9 x10 x11 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B L C P1 P2 P3 P4 K.
  z4kx_intro C.
  set (ND := 2^64 - 1 - DT4) in *.
  assert (NDR : 18446603336221196288 <= ND <= 18446744073709547519) by (unfold ND; lia).
  clearbody ND.
  pose proof (SysStep.rw_cells_bytes_at bsegs mm (SP + 128) _ FR1) as FRB.
  assert (FRL : Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 DT4)])) = 8) by (rewrite cells_bytes_length; [reflexivity | cbn; tauto]).
  kx_runFm [0x87078] 60%nat
    [KZRange DT4 4096 (2^47); KZRange (DT4 + 8192) 4096 (2^47); KZAlign DT4 4; KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange p 4096 (2^47);
     KZRange SP 4096 (2^47); KZRange (DST + dcap - (p + L)) 2 (2^47); KZRange B 0 51; KZRange L 1 2; KZRange ND 18446603336221196288 18446744073709547519;
     KZTab DT4 8192 4 [(2, 0, 11); (3, 1, 2)];
     KZWord (SP + 128) 8 DT4; KZWr (p + L) 2; KZDisj (p + L) 2 DT4 8192; KZDisj (p + L) 2 SP 528; KZDisj (p + L) 2 2147450880 17592186044416]
    [(DT4, 8192); (SP + 128, 8)] [(p + L, 2)] [(DT4, 8192); (p + L, 2)].
  all: try (z4br).
  all: try ((lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end)).
  all: try ((lazymatch goal with |- accP _ _ _ =>
          unfold accP, adenot; cbn [a_base a_off edenot fst snd]; z4w KXA; first [apply (proj2 (proj2 WT)); lia | apply (proj2 (proj2 WF)); lia] end)).
  all: try ((lazymatch goal with |- branch_taken _ _ _ = _ =>
          unfold branch_taken; rewrite ?bv_ltu_Z; cbn [edenot]; z4w KXA; apply Z.ltb_ge; lia end)).
  all: try ((lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off edenot]; z4w KXA;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          change (3 mod 64) with 3; change (2^3) with 8; change (2^64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          rewrite ?alu_add; unfold v_add; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          repeat match goal with |- context [?a mod 18446744073709551616] =>
            lazymatch a with context [_ mod 18446744073709551616] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end;
          unfold KXGoM.apart in *; Z.div_mod_to_equations; lia end)).
  kx_post_regs_keep.
  pose proof (munch_refl [(DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(p + L, 2)].
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?t1 _ _ ?s1 _ ?a1 (Z_to_bv 64 ?pl) ?a3 _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bb) _ _ ?t5 _) _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| apply (K (mem_denot E m l) a1 a3 s1 t1 t5 (bb - B) (pl - (p + L)))]
  end.
  all: try exact MUW.
  all: try exact WMr.
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OL] end).
  all: try (lazymatch goal with |- @eq machine_state _ _ =>
    (repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal])) end).
  all: try (symmetry; apply Z_to_bv_bv_unsigned).
  all: try (lia).
  all: (lazymatch goal with |- _ <= _ <= _ =>
    match goal with |- context [ev ?E ?j] => let H := fresh "RG" in kx_range (EVar j) H end; lia end).
Time Qed.

Definition z4_D5_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (c gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word)
         (SP DT4 DBL DBH DST dcap SS n SBL SBH p B : Z),
    z4kx_ctx RNG mm SP DT4 DBL DBH DST dcap SS n SBL SBH ->
    DST <= p -> p + 10 <= DST + dcap -> 0 <= B <= 7 ->
    (forall (mm' : amem) (a1 a3 s1 t1 t5 : word) (nbs d : Z),
       munch [(DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       (exists obuf', u8arr bsegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
       0 <= nbs <= 55 -> 5 <= d <= 10 ->
       evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 t1 x7 (Z_to_bv 64 DT4) s1 x10 a1 (Z_to_bv 64 (p + d)) a3 x14 x15
                                 (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26
                                 (Z_to_bv 64 (B + nbs)) x28 x29 t5 x31)
                            F (Z_to_bv 64 0x87078) fc None mm' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR c (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 p) x13 x14 x15
                             (Z_to_bv 64 (2^64 - 1 - DT4)) x17 x18 x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 (Z_to_bv 64 B)
                             x28 x29 x30 x31)
                        F (Z_to_bv 64 0x86d54) fc None mm (seg_rom bsegs)).

Theorem z4_D5 : z4_D5_case.
Proof.
  intros Q RNG mm F fc c gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
    SP DT4 DBL DBH DST dcap SS n SBL SBH p B C P1 P2 P3 K.
  eapply z4_D5a; [exact C | lia | lia | lia |].
  intros m1 a1 s1 t1 t5 nb1 l1 MU1 WM1 MI1 OB1 NB1 L1.
  pose proof (z4kx_ctx_tr _ _ _ _ _ _ _ _ _ _ _ _ _ C MU1 WM1 MI1 OB1) as C1.
  eapply z4_D5b; [exact C1 | lia | lia | lia | lia |].
  clear a1 s1 t1 t5. intros m2 a1 s1 t1 t5 nb2 l2 MU2 WM2 MI2 OB2 NB2 L2.
  pose proof (z4kx_ctx_tr _ _ _ _ _ _ _ _ _ _ _ _ _ C1 MU2 WM2 MI2 OB2) as C2.
  eapply z4_D5c; [exact C2 | lia | lia | lia | lia |].
  clear a1 s1 t1 t5. intros m3 a1 s1 t1 t5 nb3 l3 MU3 WM3 MI3 OB3 NB3 L3.
  pose proof (z4kx_ctx_tr _ _ _ _ _ _ _ _ _ _ _ _ _ C2 MU3 WM3 MI3 OB3) as C3.
  eapply z4_D5d; [exact C3 | lia | lia | lia | lia |].
  clear a1 s1 t1 t5. intros m4 a1 s1 t1 t5 nb4 l4 MU4 WM4 MI4 OB4 NB4 L4.
  pose proof (z4kx_ctx_tr _ _ _ _ _ _ _ _ _ _ _ _ _ C3 MU4 WM4 MI4 OB4) as C4.
  eapply z4_D5e; [exact C4 | lia | lia | lia | lia |].
  clear a1 s1 t1 t5. intros m5 a1 a3 s1 t1 t5 nb5 l5 MU5 WM5 MI5 OB5 NB5 L5.
  replace (p + l1 + l2 + l3 + l4 + l5) with (p + (l1 + l2 + l3 + l4 + l5)) by lia.
  replace (B + nb1 + nb2 + nb3 + nb4 + nb5) with (B + (nb1 + nb2 + nb3 + nb4 + nb5)) by lia.
  apply (K m5 a1 a3 s1 t1 t5 (nb1 + nb2 + nb3 + nb4 + nb5) (l1 + l2 + l3 + l4 + l5)); [| | exact MI5 | exact OB5 | lia | lia].
  - eapply munch_trans; [exact MU1 |]. eapply munch_trans; [exact MU2 |]. eapply munch_trans; [exact MU3 |].
    eapply munch_trans; [exact MU4 | exact MU5].
  - eapply wmono_trans; [exact WM1 |]. eapply wmono_trans; [exact WM2 |]. eapply wmono_trans; [exact WM3 |].
    eapply wmono_trans; [exact WM4 | exact WM5].
Time Qed.
