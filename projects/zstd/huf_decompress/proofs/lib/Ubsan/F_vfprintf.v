(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (towrite_g_proof, towrite_proof, arg_ok_vf and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_memset F_memcpy Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_printf_iface F_printf_core.

From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_vfprintf () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib5Ubsan:F_vfprintf;gfile_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02I47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib3Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorK4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem4core01C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:F_vfprintf>towrite_g_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface<towrite_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface6arg_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5UbsanDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg04C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03I47Corelib4Init5Logic4True00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5Ubsan>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:F_vfprintf9arg_ok_vfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat9add_assocC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith4Znat5Nat2Z6inj_lt".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
  [C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Lemma file_cells_g : forall flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
  file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail
  = gfile_cells flags 0 0 0x23e88 wend wpos wbase writefn 0x24044 buf bufsize fd mode (Z_to_bv 64 0xffffffff) lbf ++ [C4 z64; CB 80 tail].
Proof.
ltac2:(KReplay.run1 (kr_t_F_vfprintf ()) [] "h03bufh17bufsizeh22fdh35flagsh43lbfh54modeh64tailh75wbaseh84wendh94wposh:7writefnp;1p;2p;?p;3p10000p4p710R0p1000Mp4p710p8P0p1000ip4p710R0p8p1001Gp4p7210P0p8g0023j13Tg002Xj19Tg0036j17Tg003Yj1;Tg0049j11Tg004^j16Tg005<j28Tg005bl?=Tg006cj1<Tg007Xj2BTg008Mj1ATg008mj3:Tg009Mj3@Tg009jj2?Tg00:Dj10Tf0R0#3#3p=2%10#1#1#1p=4%10#1p=>%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=5g00:cR1#3#2R2#3#2#9R3#7R4g00;HR5%92#7#;g00;fR2#;f:g00<[R6P6%31#2#1#4#3#1#3#2#1#3#2#6f9f8f7f6%21#1#3#2#2#2#1#3#2#1#2#6f5f4f3f2%11#>#4#4#4#4#4#4#4#6,83f1M?=1836#<g00=9#5#5#5#5#5/B0%A25:25:25@2'?W6X45X54X25X15X05X:5X75X95W8W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_g_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
    rw_cells usegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ rw_cells usegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x23c50) fc None m (seg_rom usegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
  unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold gfile_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem towrite_proof : towrite_stmt.
Proof.
  unfold towrite_stmt. intros until tail. intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | fail] end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & D5). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact D5].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells usegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
  rw_cells usegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post [[Hwf Hb] Hw] WF.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells usegs m A cs -> A = A' -> rw_cells usegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells usegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
