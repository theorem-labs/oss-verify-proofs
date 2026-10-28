(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth BothEntry.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABytes StdioFiles Stdio_kit Stdio_iface F_syscalls AF_atexit AExit F_module_dtor ADriver_iface.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require AsanHexScan.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ARepInit_kit ARepInit_B.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
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
Ltac2 rds2_prove (t : constr) : constr := constr:(ltac2:(ltac1:(repeat match goal with H : _ |- _ => clear H end; intros; lia)) : $t).
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
Ltac2 bins1_fix2 (subs : (constr * constr) list) (c : constr) : constr :=
  let (_, c) := rds2_sub (rds2_lit subs) c in let (_, c) := rds2_relia c in c.
Ltac2 bins1_run2 (subs : (constr * constr) list) (tab : string) (secs : string list) (s : string) : unit :=
  KReplay.kr_revert ();
  let ph := { contents := [] } in
  let c := KReplay.decode_ph (Some ph) tab (KReplay.kr_secs secs) s in
  Std.exact_no_check (bins1_fix2 subs c);
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check (bins1_fix2 subs b))) (ph.(contents)).
Ltac2 kr_t_AD_handoff0 () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:firstn_nilK5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact01C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib4Init5Logic2eq00C56Stdlib5Arith8PeanoNat3Nat6eqb_eqK47Corelib4Init5Logic2eq01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact03K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact04C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8zexp_eqbC5ARocqVerifyHarness?AgentSubmission2AS:MainExport;zexp_eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0<ho_pfact_eqbC47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pfact_okI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0?ho_pfact_eqb_eqC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8mfact_okC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission3Lib5CellsBcells_bytes_lengthC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission2AS:MainExport:mimg_coverC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_image0C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure?rw_cells_recastK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00C47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:aimg_chunkK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth>asan_mem_factsC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9so_activeC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio6so_bufC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio8so_firstC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9so_lbf_nlC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio8to_bytesC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initC47Corelib4Init5Peano2ltC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6NArith6BinNat1N3subK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_003C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z9leb_spec0C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC46Stdlib9micromega;ZifyClasses3injK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0@canary_seg_bytesC5ARocqVerifyHarness?AgentSubmission5BothW4BImg@a_find_segment_1C5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wa_unsignedI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z;inj_sub_maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_000C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_001C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_002C46Stdlib9micromega8ZifyInst7Inj_N_ZK46Stdlib9micromega:ZMicromega;ZArithProof01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact03C5ARocqVerifyHarness?AgentSubmission2AS:MainExport9mfact_eqbC5ARocqVerifyHarness?AgentSubmission2AS:MainExport:mfact_findC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8is_cellwC5ARocqVerifyHarness?AgentSubmission2AS:MainExport;cellw_bytesC5ARocqVerifyHarness?AgentSubmission2AS:MainExport5cellwC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_wfK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0<canary_wr_atC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith4Znat5Z2Nat2idC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC46Stdlib5Lists4List@nth_error_repeatC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure<rw_cells_appC47Corelib4Init5Logic5proj2C46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z7inj_addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C47Corelib4Init5Logic7f_equalC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission2AS:MainExport5zerosC47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW4BImg?ref_mrd_overlayC5ARocqVerifyHarness?AgentSubmission2AS:MainExport2zvK5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp03K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp04K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp05K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp06c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff07zlit_ofc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:mzero_covbK5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact02c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:zlit_of_zvC56Stdlib6ZArith6BinInt1Z6leb_lec5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0@zchunk_pointwiseK5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact04K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact05K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact06K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact07K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact08K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact09c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff07mknownbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib4Bool4Bool8orb_propC46Stdlib9micromega;ZifyClasses8or_morphc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0?cellw_bytes_lenc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff09mrd_high0I47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List>forallb_forallC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;mknown_someC47Corelib4Init9Datatypes:option_mapC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor6gdescsC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4succc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;gdesc_cellsc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;gdescs_imgbC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor5gdescK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0Aimg_chunk_of_noneK47Corelib4Init9Datatypes4prod01c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0?gdescs_img_nonec5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;mzero_coverc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:wr_at_sub'c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0<run_rw_cellsC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;known_chunkc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:fill_chunkc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:gdescs_imgC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor8AGLOBALSC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor?AGLOBALS_lengthC5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit:atx_stateAc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0Dbytes_eq_of_unsignedc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff08rw_C8_C4C5ARocqVerifyHarness?AgentSubmission5BothW5AExit;stdin_cellsc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0@atx_stateA0_initc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0=ho_pfact_findC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth?asan_pure_factsC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow<shadow_bytesC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7hinv_bmc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff08sh_zero1c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff07sh_sub0C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_LOC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_HIC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff08sh_zero4C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBunpoisoned_of_zeroC56Stdlib6ZArith6BinInt1Z6moduloK5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region01C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC56Stdlib6ZArith6BinInt1Z;le_preorderC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGC5ARocqVerifyHarness?AgentSubmission2AS;AsanHexScan6zscanZC4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothUTgt_huf_decompress_both_seg_bytes_003C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface6ASTAGEC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit4SEG3C56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N6leb_leC56Stdlib6NArith6BinNat1N3powC56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith4Znat3N2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission2AS;AsanHexScan<zscanZ_soundC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B?zscanN_completeC56Stdlib6ZArith4Znat3N2Z6inj_ltc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:astg_scanZC56Stdlib6NArith6BinNat1N3ltbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;hex_byte_atC56Stdlib6NArith6BinNat1N6ltb_ltC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit<zscanN_soundC47Corelib7Strings:PrimString6lengthC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms4to_ZC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit@a_find_segment_3c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:astg_scanNC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit@seg3_chunk_bytesC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit9seg3_baseC56Stdlib6ZArith4Znat5Nat2Z3injC46Stdlib9micromega;ZifyClasses6eq_iffC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit6zshapeC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit>img_zero_cellsC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:ASTAGE_LENC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<ASTAGE_LEN_Zc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:astg_wr_atC5ARocqVerifyHarness?AgentSubmission3Lib7SysStepArw_cells_bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission2AS:MainExport5two64C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef5skipnC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem7pad_lenC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMemFflatten_strings_lengthC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem>raw_len_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem;struct_sizec5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff04SBLKC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8str_basec5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;SBLK_lengthC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8wrap_memC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem@init_stack_bytesC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9raw_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9rnd_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMemDbuild_stack_bytes_eqC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem4argcC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9argv_ptrsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9envp_ptrsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:auxv_wordsC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init3Nat3mulC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8str_ptrsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8env_baseC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?str_ptrs_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0>bytes_at_agreeC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC5ARocqVerifyHarness?AgentSubmission5BothW4BImg7b_phdrsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem<str_ptrs_nthC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem>bytes_at_slicec5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0@firstn_add_splitC46Stdlib5Lists4List;skipn_skipnC46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List9skipn_appC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_extC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff09SBLK_mod8c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff07SBLK_atC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pagedownC5ARocqVerifyHarness?AgentSubmission2AS:MainExport6pageupC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8allow_ofc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0@page_base_of_valC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission4LibA5ExecFArng_fp_ok_allowedC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth8asan_visC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List;in_flat_mapC46Stdlib5Lists4List<nth_error_Inc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0<allow_in_appc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0;vis_rng_genC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff07vis_rngc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:vis_rng_shC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF5fp_okC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4LibA8AcctCore7page_okC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9rng_fp_okC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:arg_stringc5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:round_dn64c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0:round_up64c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff0Bstack_shclean_initC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00c5ARocqVerifyHarness?AgentSubmission5BothW;AD_handoff07span_ge".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ho_pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma ho_pfact_eqb_eq : forall f g, ho_pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma ho_pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (ho_pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply ho_pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Ltac mf V m HM f H := pose proof (mfact_find bsegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (ho_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma aimg_chunk : forall V m (l : list mfact) A cs,
  Forall (mfact_ok bsegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> rw_bytes_b bsegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells bsegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

(* [comment removed for export] *)
End CANSEC2.
Ltac aimg V m HM A cs H :=
  pose proof (aimg_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Lemma stderr_wfile0_init : forall V m, Forall (mfact_ok bsegs V m) asan_mem_facts -> stderr_wfile0 m.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [| split; [vm_compute; reflexivity| split; [left; reflexivity| lia]]].
  aimg V m HM 0xb66f8 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x60d998 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) H. exact H.
Qed.

Lemma stdout_file_init : forall V m, Forall (mfact_ok bsegs V m) asan_mem_facts -> stdout_file m stdout_init.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  cbn [so_active so_buf so_lbf_nl so_first stdout_init Prelim.zlength length Z.of_nat Z.add].
  split. { aimg V m HM 0xb67e8 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDOUT_WRITE 0x60d9a0 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) H. exact H. }
  split; [vm_compute; reflexivity|].
  split. { aimg V m HM 0x60d9a0 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] H. exact H. }
  split; [reflexivity|]. split; [unfold zlength; cbn; lia| intros _; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma canary_seg_bytes : forall k, (k < 8)%nat ->      (* [comment removed for export] *)
  segment_byte_at (seg_bytes AsanUbsan_segment_003) (0x60d2d0 - 0xb3000 + N.of_nat k)%N = Some (Z_to_bv 8 0).
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
Lemma canary_wr_at : forall m, wr_at bsegs m 0x60d2d0 8.
Proof.
  intros m. split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
  destruct (m (wa (0x60d2d0 + i))) as [b|] eqn:E; [discriminate|].
  rewrite wa_unsigned by lia. rewrite a_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 (0x60d2d0 + i)); destruct (Z.leb_spec0 (0x60d2d0 + i + 1) 0x30000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x30000 (0x60d2d0 + i)); destruct (Z.leb_spec0 (0x60d2d0 + i + 1) 0xb1000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xb1000 (0x60d2d0 + i)); destruct (Z.leb_spec0 (0x60d2d0 + i + 1) 0xb3000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xb3000 (0x60d2d0 + i)); destruct (Z.leb_spec0 (0x60d2d0 + i + 1) 0x60f000); cbn [andb]; try lia.
  replace (seg_writable AsanUbsan_segment_003) with true by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0xb3000 by (vm_compute; reflexivity).
  replace (Z.to_N (0x60d2d0 + i - 0xb3000)) with (0x60d2d0 - 0xb3000 + N.of_nat (Z.to_nat i))%N by lia.
  rewrite canary_seg_bytes by lia. discriminate.
Qed.
Lemma ssp_guard_init : forall V m, Forall (mfact_ok bsegs V m) asan_mem_facts -> rw_cells bsegs m ssp_guard [C8 (Z_to_bv 64 (V 45%nat))].
Proof.
  intros V m HM. mf V m HM (MRo (ZLit 6345424) 8 (ZV 45)) H. unfold ssp_guard.
  pose proof (cellw_bytes 8 (V 45%nat) eq_refl) as (Cb & Cs & Cwf). change (cellw 8 (V 45%nat)) with (C8 (Z_to_bv 64 (V 45%nat))) in Cb, Cs, Cwf.
  split.
  - split; [cbn; split; [exact Cwf| exact I]|]. cbn [cells_bytes]. rewrite app_nil_r, Cb. exact H.
  - cbn [cells_size]. rewrite Cs. apply canary_wr_at.
Qed.

Lemma errno_init : forall V m, Forall (mfact_ok bsegs V m) asan_mem_facts -> rw_cells bsegs m 0x5ed1ec [C4 z64].
Proof. intros V m HM. aimg V m HM 0x5ed1ec [C4 z64] H. exact H. Qed.
(* [comment removed for export] *)
Lemma run_rw_cells : forall m A n (b : byte),
  0 <= n -> (forall i, 0 <= i < n -> m (wa (A + i)) = Some b) -> wr_at bsegs m A n ->
  rw_cells bsegs m A [CB (Z.to_nat n) (repeat b (Z.to_nat n))].
Proof.
  intros m A n b Hn Hz (W1 & W2 & W3). split.
  - split; [cbn; split; [rewrite repeat_length; reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite repeat_length, Z2Nat.id by lia; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite (nth_error_repeat b Hi).
    unfold mrd. rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. exact W3.
Qed.

Lemma rw_cells_join : forall m A n1 n2 (j1 j2 : list byte),
  rw_cells bsegs m A [CB n1 j1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 j2] ->
  rw_cells bsegs m A [CB (n1 + n2)%nat (j1 ++ j2)].
Proof.
  intros m A n1 n2 j1 j2 H1 H2.
  pose proof H1 as [[[L1 _] _] _]. pose proof H2 as [[[L2 _] _] _]. cbn in L1, L2.
  assert (H : rw_cells bsegs m A ([CB n1 j1] ++ [CB n2 j2])).
  { apply (proj2 (rw_cells_app bsegs m A [CB n1 j1] [CB n2 j2])). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  eapply rw_cells_recast; [exact H| cbn; split; [rewrite app_length; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rw_C1_CB : forall m A (b : byte), rw_cells bsegs m A [C1 b] -> rw_cells bsegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity]. Qed.

Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hb Hbs. f_equal; [apply bv_eq; exact Hb| apply IH; exact Hbs].
Qed.

(* [comment removed for export] *)
Lemma rw_C8_C4 : forall m A (v lo hi : word),
  rw_cells bsegs m A [C8 v] -> cells_bytes [C4 lo; C4 hi] = cells_bytes [C8 v] -> rw_cells bsegs m A [C4 lo].
Proof.
  intros m A v lo hi H E.
  assert (H' : rw_cells bsegs m A ([C4 lo] ++ [C4 hi])).
  { eapply rw_cells_recast; [exact H| cbn; tauto| exact E| reflexivity]. }
  apply (proj1 (rw_cells_app bsegs m A _ _)) in H'. exact (proj1 H').
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at bsegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

End CANSEC3.
Ltac norm_addr := match goal with |- rw_cells _ _ ?A _ => let a := eval vm_compute in A in change A with a end.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma zchunk_pointwise : forall m A n, rw_cells bsegs m A [CB (Z.to_nat n) (zeros n)] -> 0x60f000 <= A ->
  forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n [[_ B] _] HA i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  unfold zeros in B1, B. rewrite repeat_length in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)).
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

(* [comment removed for export] *)
Definition zlit_of (e : zexp) : option Z := match e with ZLit z => Some z | _ => None end.
Lemma zlit_of_zv : forall V e z, zlit_of e = Some z -> zv V e = z.
Proof. intros V e z H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.
Definition mzero_covb (lo n : Z) (f : mfact) : bool :=
  match f with
  | MZero a n' => match zlit_of a with Some a' => (a' <=? lo) && (lo + n <=? a' + n') | None => false end
  | MZeroC a n' => match zlit_of a with Some a' => (0x60f000 <=? a') && ((a' <=? lo) && (lo + n <=? a' + n')) | None => false end
  | _ => false
  end.
Lemma mzero_cover : forall V m (l : list mfact) lo n,
  Forall (mfact_ok bsegs V m) l -> existsb (mzero_covb lo n) l = true ->
  forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros V m l lo n HM HE i Hi. apply existsb_exists in HE as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) HM f Hin) as K.
  destruct f as [? ? ?|a k|? ? ?|a k|? ? ?|? ?|? ?|? ?|? ?]; try discriminate; cbn [mzero_covb] in Hf;
    destruct (zlit_of a) as [a'|] eqn:E; try discriminate; apply (zlit_of_zv V) in E; cbn [mfact_ok] in K; rewrite E in K.
  - apply andb_prop in Hf as [H0 Hf]. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
    replace (lo + i) with (a' + (lo + i - a')) by lia. apply (zchunk_pointwise m a' k K); lia.
  - apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    replace (lo + i) with (a' + (lo + i - a')) by lia. apply K. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mknownb (l : list mfact) (a : Z) : bool :=
  existsb (fun f => match f with
    | MZero (ZLit a0) n => (a0 <=? a) && (a <? a0 + n)
    | MZeroC (ZLit a0) n => (a0 <=? a) && (a <? a0 + n)
    | MFill (ZLit a0) n _ => (a0 <=? a) && (a <? a0 + n)
    | MCell (ZLit a0) w _ => (a0 <=? a) && (a <? a0 + Z.of_nat w) && (Nat.eqb w 1 || Nat.eqb w 2 || Nat.eqb w 4 || Nat.eqb w 8)
    | _ => false
    end) l.

Lemma cellw_bytes_len : forall w z, (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%nat -> length (cbytes (cellw w z)) = w /\ csize (cellw w z) = w.
Proof. intros w z [ -> | [ -> | [ -> | -> ] ] ]; cbn; split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mrd_high0 : forall m a, 0x60f000 <= a < 2^64 -> mrd bsegs m (wa a) = m (wa a).
Proof. intros m a Ha. apply ref_mrd_overlay. rewrite wa_unsigned by lia. lia. Qed.

Lemma mknown_some : forall V m l a, Forall (mfact_ok bsegs V m) l -> 0x60f000 <= a < 2^64 -> mknownb l a = true ->
  exists b, m (wa a) = Some b.
Proof.
  intros V m l a HF HA HK. apply existsb_exists in HK as (f & Hin & Hf). pose proof (proj1 (Forall_forall _ _) HF f Hin) as OK.
  destruct f as [e w v|e n|e w v|e n|e n c|lo hi|e n|e n|e n]; try discriminate; destruct e; try discriminate; cbn [mfact_ok zv] in OK.
  - apply andb_prop in Hf as [Hf HW]. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    assert (W : (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%nat).
    { repeat (apply orb_prop in HW as [HW|HW]); apply Nat.eqb_eq in HW; lia. }
    destruct (cellw_bytes_len w (zv V v) W) as [LB _].
    destruct OK as [[_ [_ [_ B]]] _]. cbn [cells_bytes] in B. rewrite app_nil_r in B.
    specialize (B (Z.to_nat (a - z)) ltac:(rewrite LB; lia)). rewrite Z2Nat.id in B by lia. replace (z + (a - z)) with a in B by lia.
    rewrite (mrd_high0 m a) in B by lia.
    destruct (nth_error (cbytes (cellw w (zv V v))) (Z.to_nat (a - z))) as [b|] eqn:E; [exists b; exact B|].
    apply nth_error_None in E. rewrite LB in E. lia.
  - apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct OK as [[[WF _] [_ [_ B]]] _]. cbn [cells_bytes cbytes cells_wf cell_wf] in B, WF. rewrite app_nil_r in B.
    specialize (B (Z.to_nat (a - z)) ltac:(lia)). rewrite Z2Nat.id in B by lia. replace (z + (a - z)) with a in B by lia.
    rewrite (mrd_high0 m a) in B by lia.
    destruct (nth_error (zeros n) (Z.to_nat (a - z))) as [b|] eqn:E; [exists b; exact B|].
    apply nth_error_None in E. lia.
  - apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    exists (Z_to_bv 8 0). specialize (OK (a - z) ltac:(lia)). replace (z + (a - z)) with a in OK by lia. exact OK.
  - apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    exists (Z_to_bv 8 c). specialize (OK (a - z) ltac:(lia)). replace (z + (a - z)) with a in OK by lia. exact OK.
Qed.

Lemma known_chunk : forall V m l A n, Forall (mfact_ok bsegs V m) l -> 0x60f000 <= A -> 0 <= n -> A + n <= 2^64 ->
  forallb (fun i => mknownb l (A + Z.of_nat i)) (seq 0 (Z.to_nat n)) = true -> wr_at bsegs m A n ->
  exists j, rw_cells bsegs m A [CB (Z.to_nat n) j].
Proof.
  intros V m l A n HF H0 H1 H2 HK W.
  set (j := map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
  assert (LJ : length j = Z.to_nat n) by (subst j; rewrite length_map, length_seq; reflexivity).
  exists j. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LJ| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite LJ; lia|].
    intros i Hi. rewrite LJ in Hi.
    pose proof (proj1 (forallb_forall _ _) HK i ltac:(apply in_seq; lia)) as Ki.
    destruct (mknown_some V m l (A + Z.of_nat i) HF ltac:(lia) Ki) as [b Hb].
    rewrite (mrd_high0 m (A + Z.of_nat i)) by lia. subst j. rewrite nth_error_map, nth_error_seq.
    try replace ((i <? Z.to_nat n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [option_map]. try replace (0 + i)%nat with i by lia. rewrite Hb. reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

(* [comment removed for export] *)
Definition gdesc_cells (b sz swr nm md : Z) : list cell :=
  [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615)].
Fixpoint gdescs_imgb (d : Z) (G : list (Z * Z * Z * Z * Z)) : bool :=
  match G with
  | [] => true
  | (b, sz, swr, nm, md) :: G' =>
      rw_bytes_b bsegs d (cells_bytes (gdesc_cells b sz swr nm md)) && rw_bytes_b bsegs (d + 16) [Z_to_bv 8 swr]
      && gdescs_imgb (d + 64) G'
  end.

Lemma img_chunk_of_none : forall m A cs, cells_wf cs ->
  (forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None) ->
  rw_bytes_b bsegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 -> rw_cells bsegs m A cs.
Proof.
  intros m A cs WF R HB HA HHI. pose proof (cells_bytes_length cs WF) as LEN.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

Lemma gdescs_img_none : forall m G d, (forall i, d <= i < d + 64 * Z.of_nat (length G) -> m (wa i) = None) ->
  gdescs_imgb d G = true -> 0 <= d -> d + 64 * Z.of_nat (length G) <= 2^64 -> gdescs m d G.
Proof.
  intros m G. induction G as [|[[[[b sz] swr] nm] md] G IH]; intros d R HB H0 H1; cbn [gdescs gdescs_imgb length] in *; [exact I|].
  rewrite Nat2Z.inj_succ in R, H1. apply andb_prop in HB as [HB H3]. apply andb_prop in HB as [HB1 HB2].
  split; [split|].
  - change 18446744073709551615 with (2^64 - 1) in HB1. unfold gdesc_cells in HB1.
    apply (img_chunk_of_none m d _); [cbn; repeat split; exact I | intros i Hi; apply R; cbn in Hi; lia | exact HB1 | lia | cbn; lia].
  - apply (img_chunk_of_none m (d + 16) [C1 (Z_to_bv 8 swr)]); [cbn; tauto | intros i Hi; apply R; cbn in Hi; lia | exact HB2 | lia | cbn; lia].
  - apply IH; [intros i Hi; apply R; lia | exact H3 | lia | lia].
Qed.

Lemma gdescs_img : forall V m l G d, Forall (mfact_ok bsegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? d) && (d + 64 * Z.of_nat (length G) <=? hi') | _ => false end) l = true ->
  gdescs_imgb d G = true -> 0 <= d -> d + 64 * Z.of_nat (length G) <= 2^64 -> gdescs m d G.
Proof.
  intros V m l G d HF HE HB H0 H1. apply gdescs_img_none; [| exact HB| exact H0| exact H1].
  exact (mimg_cover bsegs V m l d (d + 64 * Z.of_nat (length G)) HF HE).
Qed.

Section HandoffFacts.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.

  (* [comment removed for export] *)
  Let WSH : wr_at bsegs m 0x7fffa000 0xbfe00.
  Proof. mf V m HM (MWr (ZLit 2147459072) 785920) H. exact H. Qed.
  (* [comment removed for export] *)
  Lemma sh_zero1 : forall i, 0 <= i < 8641 -> m (wa (2147459072 + i)) = Some (Z_to_bv 8 0).
Proof. mf V m HM (MZero (ZLit 2147459072) 8641) H. exact H. Qed.
  (* [comment removed for export] *)
  Lemma sh_zero4 : forall i, 0 <= i < 2148244992 - 2147544454 -> m (wa (2147544454 + i)) = Some (Z_to_bv 8 0).
Proof. exact (mzero_cover V m _ 2147544454 (2148244992 - 2147544454) HM ltac:(vm_compute; reflexivity)). Qed.

  (* [comment removed for export] *)
  Lemma zrun_chunk : forall base len A n,
    (forall i, 0 <= i < len -> m (wa (base + i)) = Some (Z_to_bv 8 0)) ->
    base <= A -> 0 <= n -> A + n <= base + len -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xbfe00 ->
    rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
    intros base len A n Hz H1 H2 H3 H4 H5. apply run_rw_cells; [lia| | eapply wr_at_sub'; [exact WSH| lia| lia| lia]].
    intros i Hi. replace (A + i) with (base + (A - base + i)) by lia. apply Hz. lia.
  Qed.
  Lemma fill_chunk : forall A n c,
    (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 c)) -> 0 <= n -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xbfe00 ->
    rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
Proof. intros A n c Hf H2 H4 H5. apply run_rw_cells; [lia| exact Hf| eapply wr_at_sub'; [exact WSH| lia| lia| lia]]. Qed.

  (* [comment removed for export] *)
  Lemma astat_shG : exists j, rw_cells bsegs m 0x7fffc1c0 [CB 144 j].
Proof.
    apply (known_chunk V m _ 0x7fffc1c0 144 HM); [lia| lia| lia| vm_compute; reflexivity|].
    eapply wr_at_sub'; [exact WSH| lia| lia| lia].
  Qed.
  Lemma astat_shD : exists j, rw_cells bsegs m 0x8000ed3e [CB 72 j].
Proof.
    apply (known_chunk V m _ 0x8000ed3e 72 HM); [lia| lia| lia| vm_compute; reflexivity|].
    eapply wr_at_sub'; [exact WSH| lia| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma gdescs_init : gdescs m 0xb69f0 AGLOBALS.
Proof.
    apply (gdescs_img V m _ AGLOBALS 0xb69f0 HM); [vm_compute; reflexivity| vm_compute; reflexivity| lia|].
    rewrite AGLOBALS_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_stateA0_init : atx_stateA false m.
Proof.
    unfold atx_stateA, atx_cellsA, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG. cbn [negb].
    repeat match goal with |- _ /\ _ => split end.
    - aimg V m HM 0x60d2e0 [C1 (Z_to_bv 8 0)] H. exact H.
    - aimg V m HM 0x60d2e4 [C4 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6345448) 4 (ZLit 1)) H. exact H.
    - mf V m HM (MCell (ZLit 6345456) 8 (ZLit 6345464)) H. exact H.
    - aimg V m HM 0x60d2f8 [C8 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6345472) 8 (ZLit 662512)) H. exact H.
    - mf V m HM (MCell (ZLit 6345728) 8 (ZLit 456012)) H. exact H.
    - aimg V m HM 0x60d308 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0x60d408 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0x5ec954 [C1 (Z_to_bv 8 0)] H. exact H.
    - aimg V m HM 0x14c1a0 [C1 (Z_to_bv 8 0)] H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma astat_cells :
      rw_cells bsegs m 0x5ed1e8 [C4 (Z_to_bv 64 (V 44%nat))]
    /\ rw_cells bsegs m 0x60d500 [C4 (Z_to_bv 64 0)]
    /\ (exists cdt thr sec tm1, rw_cells bsegs m 0x60d520 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ (exists reg : bool, atx_stateA reg m)                     (* [comment removed for export] *)
    /\ rw_cells bsegs m 0xb6c90 [C1 (Z_to_bv 8 0)]
    /\ (exists dso, rw_cells bsegs m 0xb3e40 [C8 dso])
    /\ rw_cells bsegs m 0x60d988 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0xb69c0 [C8 (Z_to_bv 64 0xb68d8)]
    /\ rw_cells bsegs m 0xb68d8 stdin_cells
    /\ rw_cells bsegs m 0xb68d0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs m 0xb67e0 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs m 0xb7b10 [C4 (Z_to_bv 64 1)]
    /\ rw_cells bsegs m 0xb6c40 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs m 0xb7bb0 [C8 (Z_to_bv 64 0)].
Proof.
    repeat match goal with |- _ /\ _ => split end.
    - mf V m HM (MCell (ZLit 6214120) 4 (ZV 44)) H. exact H.
    - aimg V m HM 0x60d500 [C4 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6346016) 1 (ZLit 1)) H. aimg V m HM 0x60d521 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] H2.
      exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
      apply (proj2 (rw_cells_app bsegs m 0x60d520 [C1 (Z_to_bv 8 1)] _)). split; [exact H| exact H2].
    - exists false. exact atx_stateA0_init.
    - aimg V m HM 0xb6c90 [C1 (Z_to_bv 8 0)] H. exact H.
    - exists (Z_to_bv 64 0xb3e40). aimg V m HM 0xb3e40 [C8 (Z_to_bv 64 0xb3e40)] H. exact H.
    - aimg V m HM 0x60d988 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0xb69c0 [C8 (Z_to_bv 64 0xb68d8)] H. exact H.
    - unfold stdin_cells. aimg V m HM 0xb68d8 [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xa7008); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0xa7034); C8 z64; C8 (Z_to_bv 64 0xa714c); C8 (Z_to_bv 64 0x60dda8); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)] H. exact H.
    - aimg V m HM 0xb68d0 [C8 (Z_to_bv 64 RSTDOUT)] H. exact H.
    - aimg V m HM 0xb67e0 [C8 (Z_to_bv 64 RSTDERR)] H. exact H.
    - mf V m HM (MCell (ZLit 752400) 8 (ZLit 72340168526266369)) H. eapply (rw_C8_C4 _ _ _ _ (Z_to_bv 64 0x1010100)); [exact H| apply bytes_eq_of_unsigned; vm_compute; reflexivity].
    - mf V m HM (MCell (ZLit 748608) 8 (ZLit 1)) H. exact H.
    - mf V m HM (MCell (ZLit 752560) 8 (ZLit 0)) H. exact H.
  Qed.
End HandoffFacts.
Section HandoffFacts2.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  (* [comment removed for export] *)
  Notation usp := (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)).
  (* [comment removed for export] *)
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.

  Lemma tid_range : 1 <= V 44%nat <= 4194303.
Proof. clear HAT. pf V HP (PVar 44 1 4194303) H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma sh_sub0 : forall base len lo hi,
    (forall i, 0 <= i < len -> m (wa (base + i)) = Some (Z_to_bv 8 0)) ->
    base <= lo -> lo <= hi -> hi <= base + len -> 0 <= base -> base + len <= 2^64 ->
    shadow_bytes m lo hi (fun _ => 0).
Proof.
    clear HAT. intros base len lo hi Hz H1 H2 H3 H4 H5. split; [lia|]. split; [lia|]. intros s Hs.
    replace s with (base + (s - base)) by lia. apply Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rodata_sh0_init' : rodata_sh0 m.
Proof.
    clear HAT. unfold rodata_sh0.
    replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x20dc0) with 2147467704 by reflexivity.
    split. { apply (sh_sub0 _ _ _ _ (sh_zero1 V m HM)); lia. }
    split. { mf V m HM (MWr (ZLit 2147459072) 785920) W. eapply wr_at_sub'; [exact W| lia| lia| lia]. }
    unfold hinv_bm. mf V m HM (MZeroC (ZLit 2147467716) 32) HZ.
    replace (shad AHBM_LO) with 2147467732 by reflexivity. replace (shad AHBM_HI) with 2147467748 by reflexivity.
    apply (sh_sub0 2147467716 32 _ _ (zchunk_pointwise m 2147467716 32 HZ ltac:(lia))); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rclean_stdout_buf_init : rclean m RBstdout.
Proof.
    clear HAT. unfold RBstdout, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
    mf V m HM (MWr (ZLit 2147459072) 785920) W.
    replace (shad 0x60d980) with 2148244272 by reflexivity. replace (shad 0x60ddc0) with 2148244408 by reflexivity.
    split; [| lia]. split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m 2148244276 2148244404 (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
      apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
    - unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
    - eapply wr_at_sub'; [exact W| lia| lia| lia].
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rclean_stage_init : rclean m RSTG.
Proof.
    clear HAT. unfold RSTG, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
    mf V m HM (MWr (ZLit 2147459072) 785920) W.
    replace (shad 0x5dc940) with 2148219176 by reflexivity. replace (shad 0x5ec980) with 2148227376 by reflexivity.
    split; [| lia]. split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m 2148219176 2148227376 (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
      apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
    - unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
    - eapply wr_at_sub'; [exact W| lia| lia| lia].
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma astg_scanZ : AsanHexScan.zscanZ AsanUbsan_seg_bytes_003 (ASTAGE - ARepInit_kit.SEG3) 65536 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma astg_scanN : ARepInit_kit.zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (ASTAGE - ARepInit_kit.SEG3)) 65536%N = true.
Proof.
    clear.
    apply (ARepInit_B.zscanN_complete _ 63); [apply N.leb_le; vm_compute; reflexivity|].
    intros i Hi. apply (AsanHexScan.zscanZ_sound _ _ _ astg_scanZ). unfold ASTAGE, ARepInit_kit.SEG3. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma astg_wr_at : wr_at bsegs m ASTAGE 65536.
Proof.
    clear HAT HM HP V.
    unfold ASTAGE. split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    destruct (m (wa (0x5dc950 + i))) as [b|] eqn:E; [discriminate|].
    rewrite wa_unsigned by lia. rewrite (ARepInit_kit.a_find_segment_3 (0x5dc950 + i)) by lia.
    replace (seg_writable AsanUbsan_segment_003) with true by (vm_compute; reflexivity).
    rewrite ARepInit_kit.seg3_base.
    cbn [seg_bytes AsanUbsan_segment_003 segment_byte_at]. rewrite ARepInit_kit.seg3_chunk_bytes.
    replace (Z.to_N (0x5dc950 + i - 0xb3000) <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
    replace (Z.to_N (0x5dc950 + i - 0xb3000)) with (Z.to_N (0x5dc950 - 0xb3000) + Z.to_N i)%N by lia.
    rewrite (ARepInit_kit.zscanN_sound _ 64 _ 65536%N astg_scanN (Z.to_N i)) by lia. discriminate.
  Qed.
  Lemma astg_init : ASTG m.
Proof.
    clear HAT. exists (repeat (Z_to_bv 8 0) ASTAGE_LEN).
    assert (E : ASTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite ASTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E.
    apply (ARepInit_kit.img_zero_cells (Z.to_N (ASTAGE - ARepInit_kit.SEG3)) 65536%N m ASTAGE).
    - exact astg_scanN.
    - reflexivity.
    - unfold ASTAGE. lia.
    - intros i Hi. apply (mimg_cover bsegs V m _ 6146378 6214080 HM); [vm_compute; reflexivity| unfold ASTAGE in Hi; lia].
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact astg_wr_at.
    - vm_compute. reflexivity.
    - cbn [cells_size csize]. lia.
  Qed.



  (* [comment removed for export] *)
  Lemma atrun_cells0_init' : rw_cells bsegs m 0x5ec950 [C1 (Z_to_bv 8 0)].
Proof. clear HAT. aimg V m HM 0x5ec950 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma stage2_word_init : bytes_at bsegs m (usp + -8) (le8 z64).
Proof.
    clear HAT. mf V m HM (MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8))) 8 (ZLit 0)) H.
    apply rw_cells_bytes_at in H. cbn [cells_bytes cbytes app] in H. rewrite app_nil_r in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma argv_ptrs_init :
       bytes_at bsegs m (usp + 8) (word_to_le_bytes 8 (Z_to_bv 64 (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (16 * V 6%nat + 4096 * V 10%nat))) + 184)))
    /\ bytes_at bsegs m (usp + 16) (word_to_le_bytes 8 (Z_to_bv 64
         (Z.b2z ((1 mod two64) <? (V 1%nat mod two64)) * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 185)))).
Proof.
    clear HAT. split.
    - mf V m HM (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))) H. exact H.
    - mf V m HM (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8 (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185)))) H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shclean_init : forall lo hi RLO RHI,
    ATOP <= RLO -> RLO <= lo -> lo < hi -> hi <= RHI -> hi + 8 <= KEND -> RHI <= KEND -> RLO mod 64 = 0 -> RHI mod 64 = 0 ->
    shclean m lo hi RLO RHI.
Proof.
    intros lo hi RLO RHI H1 H2 H3 H4 H5 H5' H6 H7. unfold KEND in *.
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    mf V m HM (MWrS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) W0.
    mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
    assert (W : wr_at bsegs m (shad ATOP) (17594333495296 - shad ATOP)).
    { rewrite shad_div. unfold AsanEmbed.ASHOFF. eapply wr_at_sub'; [exact W0| | |]; clear - HAT P0 P6 P10; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    assert (ZR : forall i, 0 <= i < 17594333495296 - shad ATOP -> m (wa (shad ATOP + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite shad_div in Hi |- *. unfold AsanEmbed.ASHOFF in Hi |- *.
      match goal with |- m (wa ?a) = _ =>
        replace a with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) by (clear; lia) end.
      apply ZW. clear - HAT P0 P6 P10 Hi. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    clear W0 ZW.
    split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m (shad lo) (shad (hi - 1) + 1) (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
      apply (sh_sub0 _ _ _ _ ZR); rewrite ?shad_div; unfold AsanEmbed.ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
    - unfold hull64, Shadow.KEND. repeat split; lia.
    - eapply wr_at_sub'; [exact W| ..]; rewrite !shad_div; unfold AsanEmbed.ASHOFF; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.
End HandoffFacts2.
(* [comment removed for export] *)
Lemma firstn_add_split : forall {A} (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a b l. revert l. induction a as [|a IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity| f_equal; apply IH].
Qed.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs,
  bytes_at bsegs m a bs -> (forall z, a <= z < a + Z.of_nat (length bs) -> m' (wa z) = m (wa z)) -> bytes_at bsegs m' a bs.
Proof.
  intros m m' a bs (A & B & H) AG. split; [exact A|]. split; [exact B|]. intros i Hi.
  unfold mrd. rewrite (AG (a + Z.of_nat i)) by lia. apply (H i Hi).
Qed.

Section StringBlock.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : word -> option byte).   (* [comment removed for export] *)
  Notation usp := (bv_unsigned sp).
  Notation m0 := (wrap_mem b_phdrs sp argv envp uid hw draw).
  (* [comment removed for export] *)
  Definition SBLK : list byte := flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) (Z.to_nat (pad_len argv envp)).
  Notation SB := (str_base sp argv envp).
  Lemma SBLK_length : Z.of_nat (length SBLK) = total_arg_bytes argv + total_arg_bytes envp + pad_len argv envp.
Proof.
    unfold SBLK. rewrite !length_app, repeat_length. pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    pose proof (raw_len_nonneg argv envp). lia.
  Qed.

  Hypothesis SPLO : stack_max_size <= usp.
  Hypothesis IMGHI : usp + Z.of_nat (length (entry_stack_image b_phdrs sp argv envp uid hw draw)) <= 2^64.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis VARGV : valid_argv argv.
  (* [comment removed for export] *)
  Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length SBLK) -> m (wa z) = m0 (wa z).

  Lemma SBLK_mod8 : (SB + Z.of_nat (length SBLK)) mod 8 = 0 /\ SB mod 8 = 0.
Proof.
    clear SPLO IMGHI VARGV HID. rewrite SBLK_length. unfold str_base, struct_size, pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc.
    pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4). unfold struct_size, Lib.InitMem.argc, Lib.InitMem.envc in R1.
    split; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

  Lemma SBLK_at : bytes_at bsegs m SB SBLK.
Proof.
    eapply bytes_at_agree; [| exact HID].
    pose proof (init_stack_bytes bsegs b_phdrs sp argv envp uid hw draw SPLO IMGHI) as B. rewrite build_stack_bytes_eq in B.
    unfold raw_bytes in B. set (U := u64s _) in B. set (FA := flatten_strings argv) in B. set (FE := flatten_strings envp) in B.
    set (PAD := repeat _ _) in B. set (RND := rnd_bytes draw) in B.
    replace ((U ++ FA ++ FE) ++ PAD ++ RND) with (U ++ ((FA ++ FE ++ PAD) ++ RND)) in B by (rewrite <- !app_assoc; reflexivity).
    apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
    assert (LU : Z.of_nat (length U) = struct_size argv envp).
    { subst U. rewrite u64s_length. cbn [length]. rewrite !length_app. cbn [length].
      unfold argv_ptrs, envp_ptrs. rewrite !map_length, !str_ptrs_length.
      match goal with |- context [length (auxv_words ?a ?b ?c ?d ?e ?f)] => change (length (auxv_words a b c d e f)) with 20%nat end.
      unfold struct_size, Lib.InitMem.argc, Lib.InitMem.envc. lia. }
    unfold SBLK. subst FA FE PAD. replace SB with (usp + Z.of_nat (length U)); [exact B|].
    unfold str_base. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arg_string : forall i s, nth_error argv i = Some s ->
    exists off, nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off /\
      let P := SB + off in
      let k := (- (P + Z.of_nat (length s) + 1)) mod 8 in
      exists slack : list byte, zlength slack = k /\ P + Z.of_nat (length s) + 1 + k <= SB + Z.of_nat (length SBLK)
        /\ bytes_at bsegs m P (s ++ Z_to_bv 8 0 :: slack).
Proof.
    intros i s Hn. destruct (str_ptrs_nth argv SB i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists off. split; [exact Hp|]. split; [exact Ho|]. cbv zeta.
    pose proof SBLK_mod8 as [M1 M2]. pose proof SBLK_length as SL. pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4).
    set (k := (- (SB + off + Z.of_nat (length s) + 1)) mod 8).
    assert (Hk : 0 <= k < 8) by (subst k; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
    assert (FIT : SB + off + Z.of_nat (length s) + 1 + k <= SB + Z.of_nat (length SBLK)).
    { subst k. Z.div_mod_to_equations. nia. }
    exists (firstn (Z.to_nat k) (skipn (Z.to_nat off + (length s + 1)) SBLK)).
    assert (LS : (Z.to_nat off + (length s + 1) + Z.to_nat k <= length SBLK)%nat) by lia.
    split. { unfold zlength. rewrite firstn_length, length_skipn. lia. }
    split; [exact FIT|].
    pose proof (bytes_at_slice bsegs b_phdrs sp argv envp uid hw draw m SB SBLK (Z.to_nat off) (length s + 1 + Z.to_nat k) SBLK_at ltac:(lia)) as B.
    rewrite Z2Nat.id in B by lia. rewrite firstn_add_split in B. rewrite skipn_skipn in B || rewrite <- skipn_add in B || idtac.
    eapply bytes_at_ext; [exact B|].
    replace (length s + 1 + Z.to_nat off)%nat with (Z.to_nat off + (length s + 1))%nat by lia.
    replace (firstn (length s + 1) (skipn (Z.to_nat off) SBLK)) with (s ++ [Z_to_bv 8 0]); [rewrite <- app_assoc; reflexivity|].
    symmetry. unfold SBLK. rewrite skipn_app, firstn_app.
    pose proof (flatten_strings_length argv) as FL.
    rewrite Hf. rewrite length_skipn.
    replace (length s + 1 - (length (flatten_strings argv) - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
  Qed.
End StringBlock.
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC4.
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC5. Context {rc : runConstT}.
Section VisRng.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  (* [comment removed for export] *)
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.

  (* [comment removed for export] *)
  Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
Proof.
    clear A0I HP HAT. intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

  Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng (fp_ok lz AL) lo len.
Proof.
    clear HP HAT. intros b n lo len HIN H1 H2 H3 H4. apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->      (* [comment removed for export] *)
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
Proof.
    clear A0I HP HAT. intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng (fp_ok lz AL) lo len.
Proof. clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng (fp_ok lz AL) lo len.
Proof.
    clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4.
    eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8));
      [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  (* [comment removed for export] *)
  Lemma rng_image : forall lo len, 0x10000 <= lo -> lo + len <= 0x60f000 -> rng (fp_ok lz AL) lo len.
Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng 11); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
  Lemma rng_image_sh : forall lo len, 0x7fffa000 <= lo -> lo + len <= 0x800b9e00 -> rng (fp_ok lz AL) lo len.
Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng_sh 11); [reflexivity| cbn; lit_divs; lia| cbn; lit_divs; lia| lia| lia]. Qed.
  Lemma rng_stackside : forall lo len, ATOP <= lo -> lo + len <= 2^47 -> rng (fp_ok lz AL) lo len.
Proof.
    intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    eapply (vis_rng 12); [reflexivity| cbn; lia| cbn; lia| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma rng_stackside_sh : forall lo len, shad ATOP <= lo -> lo + len <= 17594333495296 -> rng (fp_ok lz AL) lo len.
Proof.
    intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    rewrite shad_div in H1. unfold AsanEmbed.ASHOFF in H1.
    eapply (vis_rng_sh 12); [reflexivity| cbn -[Z.div Z.mul Z.add]; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])| cbn -[Z.div Z.mul Z.add]; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma rng_fake : forall (P393 : 4096 <= 4096 * V 377%nat /\ 4096 * V 377%nat + 11571200 <= ATOP),
    rng (fp_ok lz AL) (4096 * V 377%nat) 11571200 /\ rng (fp_ok lz AL) (shad (4096 * V 377%nat)) (shlen 11571200).
Proof.
    clear HP HAT. intros P393. atop_facts. split.
    - eapply (vis_rng 3); [reflexivity| cbn; lia| cbn; lia| lia| lia].
    - rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      eapply (vis_rng_sh 3); [reflexivity| cbn -[Z.div Z.mul]; lia| cbn -[Z.div Z.mul]; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])| lia| (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])].
  Qed.
  Lemma rng_dtls : forall (P310 : 4096 <= 4096 * V 310%nat /\ 4096 * V 310%nat + 4096 <= ATOP), rng (fp_ok lz AL) (4096 * V 310%nat) 4096.
Proof. clear HP HAT. intros P310. atop_facts. eapply (vis_rng 4); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
  Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng (fp_ok lz AL) b 0.
Proof. clear A0I HP HAT. intros b Hb. apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.
End VisRng.
(* [comment removed for export] *)
Section ArgPack.
  Variables (V : nat -> Z) (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : word -> option byte).
  Notation usp := (bv_unsigned sp).
  Notation SB := (str_base sp argv envp).
  Hypothesis HM : Forall (mfact_ok bsegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis SPLO : stack_max_size <= usp.
  Hypothesis IMGHI : usp + Z.of_nat (length (entry_stack_image b_phdrs sp argv envp uid hw draw)) <= 2^64.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis SPW : ATOP + 8388608 <= usp.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
  Hypothesis FITS : usp + entry_stack_span argv envp <= 2^47.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length (SBLK argv envp)) -> m (wa z) = wrap_mem b_phdrs sp argv envp uid hw draw (wa z).

  Definition round_dn64 (x : Z) : Z := x / 64 * 64.
  Definition round_up64 (x : Z) : Z := (x + 63) / 64 * 64.

  Lemma span_ge : SB + Z.of_nat (length (SBLK argv envp)) + 16 <= usp + entry_stack_span argv envp /\ usp + 192 <= SB.
Proof.
    clear HM HP SPLO IMGHI SP16 SPW FITS HID. rewrite SBLK_length. unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc, entry_stack_span, pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc.
    pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4). unfold pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in R4.
    destruct VARGV as (A1 & _). change (Z.of_nat auxv_size) with 160.
    split; [| lia]. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

  Lemma arg_pack : forall i s, nth_error argv i = Some s ->
    exists off (slack : list byte) (r : region),
      nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off
      /\ bytes_at bsegs m (SB + off) (s ++ Z_to_bv 8 0 :: slack)
      /\ (- (SB + off + Z.of_nat (length s) + 1)) mod 8 <= zlength slack
      /\ usp + 24 <= SB + off
      /\ shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r) /\ r_lo r < r_hi r
      /\ inreg r (SB + off) (Z.of_nat (length s) + 1 + zlength slack)
      /\ usp + -112 <= r_rlo r /\ ATOP <= r_rlo r /\ r_rhi r <= 2^47
      /\ SB + off + Z.of_nat (length s) + 1 + zlength slack <= 2^47.
Proof.
    intros i s Hn.
    destruct (arg_string sp argv envp uid hw draw m SPLO IMGHI SP16 HID i s Hn) as (off & Hp & Ho & slack & SL & FIT & BY).
    cbv zeta in SL, FIT.
    pose proof span_ge as [SG1 SG2]. pose proof (SBLK_mod8 sp argv envp SP16) as [M1 M2]. atop_facts.
    assert (LS : 0 <= zlength slack) by (unfold zlength; lia).
    assert (HE : SB + off + Z.of_nat (length s) + 1 + zlength slack <= 2^47 - 16) by lia.
    assert (D1 : SB + off - 63 <= round_dn64 (SB + off) <= SB + off /\ round_dn64 (SB + off) mod 64 = 0) by (unfold round_dn64; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
    assert (U1 : SB + off + Z.of_nat (length s) + 1 + zlength slack <= round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack) <= 2^47
                 /\ round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack) mod 64 = 0) by (unfold round_up64; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
    exists off, slack, (mkRegion (SB + off) (SB + off + Z.of_nat (length s) + 1 + zlength slack)
                                 (round_dn64 (SB + off)) (round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack))).
    cbn [r_lo r_hi r_rlo r_rhi]. unfold inreg. cbn [r_lo r_hi].
    repeat match goal with |- _ /\ _ => split end; try exact Hp; try exact BY; try lia.
    apply (stack_shclean_init V m HM HP HAT); unfold Shadow.KEND; lia.
  Qed.
End ArgPack.
End CANSEC5.
