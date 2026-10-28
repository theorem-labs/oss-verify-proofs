(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface Printf_outsA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_printf_iface F_printf_core F_vfprintf.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_pieces Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ITreeA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_vfprintf_stdout Printf_bridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg Stdio_kit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 rds2_cert_ok (v : constr) : bool :=
  let rec peel c := match Constr.Unsafe.kind c with Constr.Unsafe.Lambda _ b => peel b | _ => c end in
  match Constr.Unsafe.kind (peel v) with
  | Constr.Unsafe.LetIn _ w r1 =>
    match Constr.Unsafe.kind r1 with
    | Constr.Unsafe.LetIn _ _ r2 =>
      match Constr.Unsafe.kind r2 with
      | Constr.Unsafe.LetIn _ f _ =>
        if Bool.and (Constr.Unsafe.closedn 0 w) (Constr.Unsafe.closedn 0 f) then
          let chk := Constr.Unsafe.make (Constr.Unsafe.App constr:(Stdlib.micromega.ZMicromega.ZTautoChecker) (Array.of_list [f; w])) in
          Constr.equal (Std.eval_vm None chk) constr:(true)
        else false
      | _ => false
      end
    | _ => false
    end
  | _ => false
  end.
Ltac2 rds2_prove (t : constr) : constr := constr:(ltac2:(ltac1:(intros; lia)) : $t).
Ltac2 rec rds2_relia (c : constr) : bool * constr :=
  let mk := Constr.Unsafe.make in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.LetIn b v body =>
    let (cb, body') := rds2_relia body in
    let is_arith := match Constr.Binder.name b with Some id => Ident.equal id @__arith | None => false end in
    if Bool.and is_arith (Constr.Unsafe.closedn 0 (Constr.Binder.type b)) then
      if rds2_cert_ok v then (if cb then (true, mk (Constr.Unsafe.LetIn b v body')) else (false, c))
      else (true, mk (Constr.Unsafe.LetIn b (rds2_prove (Constr.Binder.type b)) body'))
    else
      let (cv, v') := rds2_relia v in
      if Bool.or cv cb then (true, mk (Constr.Unsafe.LetIn b v' body')) else (false, c)
  | Constr.Unsafe.Lambda b body =>
    let (cb, body') := rds2_relia body in
    if cb then (true, mk (Constr.Unsafe.Lambda b body')) else (false, c)
  | Constr.Unsafe.App f args =>
    let (cf, f') := rds2_relia f in
    let ch := { contents := cf } in
    let args' := Array.map (fun a => let (ca, a') := rds2_relia a in (if ca then ch.(contents) := true else ()); a') args in
    if ch.(contents) then (true, mk (Constr.Unsafe.App f' args')) else (false, c)
  | Constr.Unsafe.Cast c1 k t =>
    let (c1c, c1') := rds2_relia c1 in
    if c1c then (true, mk (Constr.Unsafe.Cast c1' k t)) else (false, c)
  | Constr.Unsafe.Case ci rt iv scr brs =>
    let (cs, scr') := rds2_relia scr in
    let ch := { contents := cs } in
    let brs' := Array.map (fun a => let (ca, a') := rds2_relia a in (if ca then ch.(contents) := true else ()); a') brs in
    if ch.(contents) then (true, mk (Constr.Unsafe.Case ci rt iv scr' brs')) else (false, c)
  | Constr.Unsafe.Fix recs i bs bds =>
    let ch := { contents := false } in
    let bds' := Array.map (fun a => let (ca, a') := rds2_relia a in (if ca then ch.(contents) := true else ()); a') bds in
    if ch.(contents) then (true, mk (Constr.Unsafe.Fix recs i bs bds')) else (false, c)
  | _ => (false, c)
  end.
Ltac2 rec rds2_sub (f : constr -> constr option) (c : constr) : bool * constr :=
  match f c with
  | Some c' => (true, c')
  | None =>
    let mk := Constr.Unsafe.make in
    let sb b :=
      let (ch, t) := rds2_sub f (Constr.Binder.type b) in
      if ch then (true, Constr.Binder.unsafe_make (Constr.Binder.name b) (Constr.Binder.relevance b) t) else (false, b) in
    let arr a :=
      let ch := { contents := false } in
      let a' := Array.map (fun x => let (cx, x') := rds2_sub f x in (if cx then ch.(contents) := true else ()); x') a in
      (ch.(contents), a') in
    let barr a :=
      let ch := { contents := false } in
      let a' := Array.map (fun x => let (cx, x') := sb x in (if cx then ch.(contents) := true else ()); x') a in
      (ch.(contents), a') in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.LetIn b v body =>
      let (c1, b') := sb b in let (c2, v') := rds2_sub f v in let (c3, body') := rds2_sub f body in
      if Bool.or c1 (Bool.or c2 c3) then (true, mk (Constr.Unsafe.LetIn b' v' body')) else (false, c)
    | Constr.Unsafe.Lambda b body =>
      let (c1, b') := sb b in let (c2, body') := rds2_sub f body in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.Lambda b' body')) else (false, c)
    | Constr.Unsafe.Prod b body =>
      let (c1, b') := sb b in let (c2, body') := rds2_sub f body in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.Prod b' body')) else (false, c)
    | Constr.Unsafe.App h args =>
      let (c1, h') := rds2_sub f h in let (c2, args') := arr args in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.App h' args')) else (false, c)
    | Constr.Unsafe.Cast c1 k t =>
      let (x1, c1') := rds2_sub f c1 in let (x2, t') := rds2_sub f t in
      if Bool.or x1 x2 then (true, mk (Constr.Unsafe.Cast c1' k t')) else (false, c)
    | Constr.Unsafe.Case ci (rt, rr) iv scr brs =>
      let (c1, rt') := rds2_sub f rt in let (c2, scr') := rds2_sub f scr in let (c3, brs') := arr brs in
      if Bool.or c1 (Bool.or c2 c3) then (true, mk (Constr.Unsafe.Case ci (rt', rr) iv scr' brs')) else (false, c)
    | Constr.Unsafe.Fix recs i bs bds =>
      let (c1, bs') := barr bs in let (c2, bds') := arr bds in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.Fix recs i bs' bds')) else (false, c)
    | Constr.Unsafe.CoFix i bs bds =>
      let (c1, bs') := barr bs in let (c2, bds') := arr bds in
      if Bool.or c1 c2 then (true, mk (Constr.Unsafe.CoFix i bs' bds')) else (false, c)
    | Constr.Unsafe.Proj p r c1 =>
      let (x1, c1') := rds2_sub f c1 in
      if x1 then (true, mk (Constr.Unsafe.Proj p r c1')) else (false, c)
    | _ => (false, c)
    end
  end.
Ltac2 rec rds2_lit (subs : (constr * constr) list) (c : constr) : constr option :=
  match subs with [] => None | (a, b) :: r => if Constr.equal c a then Some b else rds2_lit r c end.
Ltac2 rds2_fix (subs : (constr * constr) list) (c : constr) : constr :=
  let (_, c) := rds2_relia c in
  match subs with [] => c | _ => let (_, c) := rds2_sub (rds2_lit subs) c in c end.
Ltac2 rds2_run (subs : (constr * constr) list) (tab : string) (secs : string list) (s : string) : unit :=
  KReplay.kr_revert ();
  let ph := { contents := [] } in
  let c := KReplay.decode_ph (Some ph) tab (KReplay.kr_secs secs) s in
  Std.exact_no_check (rds2_fix subs c);
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check (rds2_fix subs b))) (ph.(contents)).
Ltac2 rds2_run1 (tab : string) (secs : string list) (s : string) : unit := rds2_run [] tab secs s.
Ltac2 kr_t_F_vfprintf_stderr () := "C47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface?sink_frame_stmtC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface;SINK_stderrC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_libDForall_disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;GLOBALS_TOPI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stdoutEfile_cells_flags_byteC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stdout<land_mod_lowC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface?sink_flags_stmtK46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stdout=land_sub_maskC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32c5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderr9flags40_8C5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stdout9land_low7C5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stdout;sx32_mod128C56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z8land_0_rc5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderr:flags40_32C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z@land_lor_distr_rC56Stdlib6ZArith6BinInt1Z7lor_0_rC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW=Printf_bridge<FLUSH_stderrC5ARocqVerifyHarness?AgentSubmission5BothW<Printf_outsABprintf_model_outsAC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdio_writeC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface@printf_core_stmtc5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderrAstderr_sink_frameC5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_coreAprintf_core_proofC5ARocqVerifyHarness?AgentSubmission6Common=Printf_pieces5outskC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF6implAMC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model<printf_modelC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5implFC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface:OUT_stderrC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceCfwritex_stderr_stmtC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceFstdio_write_flush_postC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceFstdio_write_flush_stmtC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA6epostFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA;implF_ebindC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<stderr_wfileC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model8pass1_okC5ARocqVerifyHarness?AgentSubmission5BothW9F_pop_arg7va_areaC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface7args_okC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model=printf_piecesK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission6Common<Printf_model8fp_callsC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles9ssp_cellsC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6ashenvC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngc5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderrDvfprintf_stderr_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit9appW_consC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4appWC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kitAashsafe_cons_fileC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kitAashsafe_cons_highC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7ashsafeC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9zb_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<OUTFP_stderrC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sK46Stdlib9micromega=RingMicromega5Psatz02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast=munch_write_nC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC47Corelib5Lists7ListDef5skipnK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@ashenv_transportC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@rclean_transportC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAprintf_core1_postC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderr>sflags_noerr_8C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec<Z_land_rangeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init5Logic5proj1K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common<rw_CB_lengthK46Stdlib9micromega7EnvRing5PExpr05c5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderrAstderr_sink_flagsC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface@printf_core_postc5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderr?sflags_noerr_32C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW:F_vfprintf:args_ok_vfC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface;fpcall_stmtK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface:TOPOK_noneC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface2SRC4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_splitC5ARocqVerifyHarness?AgentSubmission4LibA6NodesA8at_nodeAI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C5ARocqVerifyHarness?AgentSubmission3Lib5ITree5ebindC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF5postFC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW:F_vfprintf6rwc_eqC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releasec5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderr?sflags_final_40c5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderr>sflags_olderr0C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF;implAM_retFC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF?implAM_from_evtC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF;implAM_bindC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFastFbytes_at_write_other_nK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast@rw_cells_frame_nC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast;stk_write_nK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure<rw_cells_appK6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc02K5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree01C45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<STATIC_SPLITC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5msize03C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C5ARocqVerifyHarness?AgentSubmission5BothW6AProto6fstepSC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00I5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg00C5ARocqVerifyHarness?AgentSubmission5BothW:F_vfprintf8VF_FRAMEC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface8VF_DEPTHC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8appW_nilC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit;ashsafe_nilC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_coreBprintf_core1_proofC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAprintf_core1_stmtC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface8PC_DEPTHK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission5BothW:F_vfprintf=towrite_proofC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<towrite_stmtC5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stdout:topok_noneC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface9OUT_DEPTHK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c5ARocqVerifyHarness?AgentSubmission5BothWAF_vfprintf_stderrDvfprintf_stderr_stmt".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := ienterF.
Ltac ileave := ileaveF.
(* [comment removed for export] *)
Ltac hide_low :=
  repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
    lazymatch A with Zpos _ => idtac | _ => fail end;
    lazymatch eval vm_compute in (A <? 0x200000)%Z with true => idtac | false => fail end;
    lazymatch type of H with ?T => change T with (sf_hide T) in H end
  end.
Ltac zs_canary := hide_low; zs; sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section StderrSinkProofs.
  Context {St : Type}.
  Variable B : Z.
  Let SINK := SINK_stderr (St:=St) B.

  Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
Proof using .
    unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) MU WM D1 D2.
    exists flags, mode, tail, rest.
    split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
Proof using B.
    unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. exact FL32.
  Qed.
End StderrSinkProofs.

(* [comment removed for export] *)
Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof using Type. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof using Type. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof using Type.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
Lemma sflags_noerr_32 : forall (flags : word),
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof using Type.
  intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof using Type. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof using Type.
  intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
  replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stderr.
  Context {St : Type}.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.
  Hypothesis HSTRN : strnlen_a_stmt.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary.

  Definition vfprintf_stderr_stmt : Prop :=
    forall RNG (rstk rfmt : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 RNG m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk bsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->       (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      (* [comment removed for export] *)
      (KHIGH <= lo) -> ashenv m ->
      rclean m rstk -> r_lo rstk <= lo -> q <= r_hi rstk ->
      rclean m rfmt -> inreg rfmt A (zlength fmt) -> inreg rfmt 68436 9 ->
      rng RNG lo (q - lo) -> rng_aimg RNG -> rng RNG VA (8 * zlength slots) -> rng0 RNG ->
      rrng RNG rstk -> rrng RNG rfmt ->
      implAM RNG (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xa7c98) fc None m (seg_rom bsegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
Proof using FLS FWE HSTRN.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
           KH ENV RCS RSlo RShi RCF RFM RPF RGstk RGimg RGva RG0 RRS RRF.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    assert (RGfmt : rng RNG A (Z.of_nat (length fmt))) by (eapply rng_sub'; [exact RGimg | unfold zlength in *; lia]).
    assert (RGF : rng RNG RSTDERR 232) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_ashsafe.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    apply (printf_model_outsA OUT_stderr (OUTFP_stderr (St:=St)) RNG fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- implAM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV1.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS1. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF1.
    eapply evtF_cut.
    { eapply (PC1 RNG rstk rfmt); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia
        | exact KH | exact ENV1 | exact RCS1 | lia | lia | exact RCF1 | exact RFM | exact RPF
        | eapply rng_sub'; [exact RGstk | lia] | exact RGimg | exact RGfmt | eapply rng_sub'; [exact RGstk | lia] | exact RRS | exact RRF ]. }
    clear ENV1 RCS1 RCF1.
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evtF_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption | exact RGF ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB bsegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    ileave.
    pose proof (printf_core_proof (list Z * St) RSTDERR B 80 rstk (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
                  (stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B rstk) HSTRN) as PC2.
    pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
    assert (RBI : inreg rstk B 80) by (unfold inreg; subst B; lia).
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implAM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGfmt
                     | exact RRS | exact RRF
                     | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
      - unfold SINK_stderr. cbn [fst].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
        change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
        split; [exact FCt|]. rewrite unsigned_lit by lia.
        split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
        unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
      - exact BY.
      - exact HF.
      - reflexivity.
      - exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1 ENV2 RCS2 RCF2.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, implAM. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 2368) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply implF_ebind.
    { unfold implAM in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 2368) (canary := canary) (RNG := RNG); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
      all: try lia.
      all: try first [ exact RGimg | exact RG0 | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
      - exact SNK3.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact ST4b.
      - split; [exact SSP1 | exact SSP2].
      - assumption. }
    cbv beta. intros [[] st4] RNG' ms' [ERNG P]. subst RNG'.
    unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m4 MUc WMc; clear MUc WMc end.
    apply implAM_retF. cbn [fst snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    do 9 zs.
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 2368)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 2368)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evtF_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
      split; [unfold file_cells; exact FC4|].
      rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
      rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
    split; [exact SSP1 | exact SSP2].
  Qed.
End Stderr.
End CANSEC1.
