(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
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
Ltac2 rec rds2_prefix (c : constr) (a : constr) (b : constr) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h cargs =>
    match Constr.Unsafe.kind a with
    | Constr.Unsafe.App ha aargs =>
      let n := Array.length aargs in
      if Bool.and (Int.lt n (Array.length cargs)) (Constr.equal h ha) then
        let rec same i := if Int.ge i n then true else if Constr.equal (Array.get aargs i) (Array.get cargs i) then same (Int.add i 1) else false in
        if same 0 then
          match Constr.Unsafe.kind b with
          | Constr.Unsafe.App hb bargs =>
            if Int.equal (Array.length bargs) n then
              let rec pairs i :=
                if Int.ge i n then []
                else let x := Array.get aargs i in let y := Array.get bargs i in
                     if Constr.equal x y then pairs (Int.add i 1) else (x, y) :: pairs (Int.add i 1) in
              let ps := pairs 0 in
              let rest := Array.map (fun x => let (_, x') := rds2_sub (rds2_lit ps) x in x')
                            (Array.sub cargs n (Int.sub (Array.length cargs) n)) in
              Some (Constr.Unsafe.make (Constr.Unsafe.App hb (Array.append bargs rest)))
            else None
          | _ => None
          end
        else None
      else None
    | _ => None
    end
  | _ => None
  end
with rds2_lit (subs : (constr * constr) list) (c : constr) : constr option :=
  match subs with
  | [] => None
  | (a, b) :: r =>
    if Constr.equal c a then Some b
    else match rds2_prefix c a b with Some x => Some x | None => rds2_lit r c end
  end.
Ltac2 rds2_fix (subs : (constr * constr) list) (c : constr) : constr :=
  let c := match subs with [] => c | _ => let (_, c) := rds2_sub (rds2_lit subs) c in c end in
  let (_, c) := rds2_relia c in c.
Ltac2 rds2_run (subs : (constr * constr) list) (tab : string) (secs : string list) (s : string) : unit :=
  KReplay.kr_revert ();
  let ph := { contents := [] } in
  let c := KReplay.decode_ph (Some ph) tab (KReplay.kr_secs secs) s in
  Std.exact_no_check (rds2_fix subs c);
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check (rds2_fix subs b))) (ph.(contents)).
Ltac2 rds2_run1 (tab : string) (secs : string list) (s : string) : unit := rds2_run [] tab secs s.
Ltac2 rds2_anc (anchors : constr list) (x : constr) : bool :=
  List.exist (fun a =>
    if Constr.equal a x then true
    else match Constr.Unsafe.kind a with
      | Constr.Unsafe.App ha aa =>
        match Constr.Unsafe.kind x with
        | Constr.Unsafe.App hx xa =>
          let n := Array.length aa in
          if Bool.and (Int.lt n (Array.length xa)) (Constr.equal ha hx) then
            let rec same i := if Int.ge i n then true else if Constr.equal (Array.get aa i) (Array.get xa i) then same (Int.add i 1) else false in
            same 0
          else false
        | _ => false
        end
      | _ => false
      end) anchors.
Ltac2 rds2_scoped (anchors : constr list) (nolast : bool) (subs : (constr * constr) list) : constr -> constr option :=
  let rec go c :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App h args =>
      if Array.exist (rds2_anc anchors) args then
        let n := Array.length args in
        let args' := Array.mapi (fun i x =>
          if rds2_anc anchors x then x
          else if Bool.and nolast (Int.equal i (Int.sub n 1)) then (let (_, x') := rds2_sub go x in x')
          else (let (_, x') := rds2_sub (rds2_lit subs) x in x')) args in
        Some (Constr.Unsafe.make (Constr.Unsafe.App h args'))
      else None
    | _ => None
    end in go.
Ltac2 rds2_fixx (scs : (constr list * bool * (constr * constr) list) list) (subs : (constr * constr) list) (c : constr) : constr :=
  let c := match subs with [] => c | _ => let (_, c) := rds2_sub (rds2_lit subs) c in c end in
  let c := List.fold_left (fun c (anc, nl, ss) => let (_, c) := rds2_sub (rds2_scoped anc nl ss) c in c) c scs in
  let (_, c) := rds2_relia c in c.
Ltac2 rds2_runx (scs : (constr list * bool * (constr * constr) list) list) (subs : (constr * constr) list) (tab : string) (secs : string list) (s : string) : unit :=
  KReplay.kr_revert ();
  let ph := { contents := [] } in
  let c := KReplay.decode_ph (Some ph) tab (KReplay.kr_secs secs) s in
  Std.exact_no_check (rds2_fixx scs subs c);
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check (rds2_fixx scs subs b))) (ph.(contents)).
Ltac2 kr_t_AD_main_B2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure<rw_cells_appC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib4Init5Logic5proj2C47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01K5ARocqVerifyHarness?AgentSubmission4Spec5ProgA6AAlloc01C5ARocqVerifyHarness?AgentSubmission4Spec5Monad4msysI5ARocqVerifyHarness?AgentSubmission4Spec6Driver7IOStyle00I5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result00C5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF;implA_implSC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5implFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA6epostFC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5enodeC5ARocqVerifyHarness?AgentSubmission4LibA6NodesA8at_nodeAI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C5ARocqVerifyHarness?AgentSubmission5BothW6AProto6fstepSC5ARocqVerifyHarness?AgentSubmission3Lib5ITree4nretK47Corelib4Init9Datatypes6option01K6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc02C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoK5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree02I5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree00K5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree01K6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00I5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission3Lib5ITree4respI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA6NodesA6fstepAC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStC5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_diagI5ARocqVerifyHarness?AgentSubmission4Spec6Driver5rd_st00C5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B1=afprintf_exitc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B2;implMA_msysC46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B13BUFC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B15STAGEC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A5AARGVC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A4RNGSC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3ALOC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init9Datatypes3sum00C47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B18POSTBODYC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6aps_okC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps;aptr_addr_MC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7AMFRAMEC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun_cells0C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ASTATC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6ashenvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3ioAK5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg03K5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result01K47Corelib4Init9Datatypes3sum02C5ARocqVerifyHarness?AgentSubmission4Spec6Driver<u8s_of_bytesK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission5BothW6I_read;read_i_postC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node04C5ARocqVerifyHarness?AgentSubmission3Lib6Decode8dec_readC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_subK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW6I_read;read_i_specC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls8read_retC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC47Corelib5Lists7ListDef5skipnI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3WOKC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC46Stdlib9micromega;ZifyClasses9not_morphC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx;ABASE_munchC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A;AARGV_munchC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA:fp_le_reflC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA9rng_fp_leC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit@drv_got_of_aheapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7astringC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=astring_factsC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_rC56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregC5ARocqVerifyHarness?AgentSubmission5BothW7AD_diag:adiag_argsC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8aat_exitC56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic9False_indK5ARocqVerifyHarness?AgentSubmission3Lib6Decode8read_ans01C47Corelib4Init3Nat3subC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission3Lib7SysStepArw_cells_bytes_atC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:block_hullC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit7hull_loC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit7hull_hiC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:hull_propsC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAablock_unpoisonedK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission5BothW8I_memcpy=memcpy_i_postC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablk_app_blkC5ARocqVerifyHarness?AgentSubmission5BothW8I_memcpy=memcpy_i_specC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportK47Corelib4Init9Datatypes3sum01C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat7eqb_neqc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B2@rw_cells_CB_joinC46Stdlib5Lists4List7map_appC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B15RDINVC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B15RDBRKK5ARocqVerifyHarness?AgentSubmission3Lib6Decode8read_ans02C5ARocqVerifyHarness?AgentSubmission4Spec6Driver:rd_contentC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6rd_bufC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6rd_capC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ABASEC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B1<rd_read_partK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stdout_fileK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07K5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result02K5ARocqVerifyHarness?AgentSubmission4Spec6Driver5rd_st01K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission4Spec6Driver9MAX_INPUTC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RFMTI5ARocqVerifyHarness?AgentSubmission3Lib6Decode8read_ans00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface6ASTAGEK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:ASTAGE_LENC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>errno_addr_ATPC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<AGOT_STDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8ASTDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>AGOT_FUZZ_INITC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<ASTAGE_LEN_ZC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface;ASTAGE2_RETC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_rangesC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:AFUZZ_INITK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats;FMT_READERRI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;GLOBALS_TOPK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses>impl_ReflexiveC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B2<rd_read_coreK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).



Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells bsegs m A [CB 0%nat []].
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B2 ()) ["CANSEC1"] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with61xh72Hah81ih91Ah:1Hh;2Hih<3Hi0h=6__sat2h>6__sat3h?1mh@1yp;1p;2p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0p1002Qp4p710R1p9P0p1002op4p710p9P0p1003gp4p710p8p1004>p4p710R0p1004[p4p710p8P0P1p8p10057p4p7210P1p8p1005cp4p7210P1p8g006@j14Tg006ej1GTg007Cj1DTg007fj1KTg008Hj1ETg008fj2TTg009Cj27Tg009_j21Tg00::j1:Tg00:Zj2JTg00;Oj3ITg00;oj4HTg00<fj1jTg00=_R1j1>Tg00>?j4YTg00?1j1XTg00?hj1VTg00@bj4UTg00AWj35Tg00B1j23Tg00BKj46Tg00Bfj4QTg00C_j29Tg00D<R0j20Tg00DXj1CTg00EGj3?Tg00FDj1@Tg00Ffj1BTg00G?j1PTg00G_j2OTg00H=j1LTg00H[j1MTg00IFj2ATg00Iij2NTg00JLj6RTg00K0j2iTg00KRj2hTg00L>j3gTg00L]j4fTg00MOj2eTg00N7j3aTg00N[j3ZTg00O>j3[Tg00Oaj3\Tg00PGj1WTg00Pel<^Tg00QJj6_Tg00R3j4`Tg00RZj4FTg00SEj7bTg00Sij7cTg00TMj8dTg00U1l<STg00UVR2f0R3'7p=2g00V4R4f1R5g00VRP3CFp==P5g00W9R6g00WXR7P7g00X8R8P3g00XXFbp=8f2R9P6P7P7P8P5P3Fcp=;f3R:P6P7P7P8P9P5P3Gdp=<g00Y8R;P4P4P4P1P1P:P9P5g00YWR1P2P3M<Sp=]g00Z6R<#4R=#4#4R>#4#4#4R?#GR@#D%G>#DR>#KRA[%23RB%E=R=%E?R?'TRC,73RD'1g00Z[REP9P5g00[PRF%:>,J1%:F3IRFCHPEP9P5%jF#>CYRG%XFRHPEP9P5%VFCURFA5;11g00\ERI13;1g00\aC6PHePEP9P5P3CQPFeC6%25RF%>1R1,95/7CRH1031,1BRJf4RK19:5#C5?E%@>R>55A#B[^84RL'1p-0RM11B5RNg00]=RO#:RP%PORO1O45RQ%L4RR%M4RS1A42RT1N4<R<'=,8SRUPSP6P7P7P8P:ERR65;S%@7R7PUC<1iS8R8P3P9g00]iRVg00^IRW'31h39=5VWdAg425CfRWb3b4b5X14X0MPF\N^14^0MRNP3P:P9P5O3RVb2UX14W0PNePNP3179CP9P5O3b2PHPL115DRD1e=?102=%2?102C[[%2=RLAa=?5VIW7%2C\I^7LPPPOPQPRPS1A4==Z4@R@,=<,8S9;S6P7A[4<T/=@,8SC<P8PWb3b4b5X14X0M1952/7C\D^14^0MRDP3f5RCPKP:O3b2b=b>UX14X0MPDePDP3%29P9P5O3b21051RD,1F1052,1FRKPFPDPFP3X64RDP2O1R@,0513MFA5MFFe9\FFP4P4P0PDP01053#WX@4X64P5P51345P1P@PDPD%>3,34X6;1342C]M<^E_P3C`PK1032,1BRBPPPOPQPRPSP4P<g00^iPTCF,8S9;SUP7P6C<P8PWb3b4b5X14X0MP9\B^14^0MRBPVb2UX14X0MPBePBP3f619C:#C5?E=5A>#BP:P5O3b2b<X;JX84C6C6PGeC6W:X94W?o"). Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells bsegs m A [CB n1 b1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells bsegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B2 ()) ["CANSEC1"] "h01Hh12L0h24__x1h34__x2h41xh52HBh67__arithh74__ffh88__varmaph95__with:4__x3h;4__x4h<4cstrh=5cstr0h>5cstr1h?5cstr2h@1lhA1nhB1yhC1AhD2H1hE2H2hF2HWhG3HwfhH2L1hI2L2hJ2_HhK2b1hL2b2hM1mhN2n1hO2n2hP1zp&0p;1p;2p;5p;6p;4p;3p;<p;Bp;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0g002QR1p4p710R2p9P0p1002op4p710p9P0p1003gp4p710p8g00_PR0p4p710R3g004[R4p4p710p8P3P2p8p10057p4p7210P2p8p1005cp4p7210P2p8g006@j1=Tg006ej1aTg007Cj1WTg007fj1hTg00G?j1dTg00::j1STg00=_R2j11Tg00C_R3j22Tg009_R5j2@Tg00_ok502Tg00a2R6k201Tg00aRk100TP1j6NTg00BKj4CTg00b6j4xTg00;oj4LTg00>?j4>Tg00bQj26Tg00bhj38Tg00?1j1HTg00?hj1QTg00cEj23Tg00AWj1Vj3KTg00cej2iTg00dHj3gTg00R3j4UTg00dej1PTg009Cj2FTg00eJj1fTg00ehj2eTg00fIj1cTg00fhj2TTg00gQj3bTg00h:j3ATg00hcj2`Tg00;Oj3RTg00G_j2OTg00iOj1~Tg00imj4MTg00H=j1{Tg00H[j1zTg00Iij2BTg00jKj1yTg00FDj1wTg00O>j3?Tg00K0j2tTg00B1j2JTg00KRj2sTg00L>j3rTg00L]j4qTg00k0j4YTP0j3pTg00k[j2[TP4j6XTg00PGj1oTg00Pel<^Tg00IFj2nTg00:Zj2mTg00l9j4uTg00<fj1vTg00@bj4lTg00lolB_Tg00RZj4kTg00SEj7jTg00TMj8|Tg00U1l<}Tg00[PR4f2R0f1R1'mf0R73Rp=0g00Z[R8P0P1P7Cup=4A8417p=7%v7#1p=:P8P0P1P7Clp=<g00Y8R9?K17p=9g00V4R:?K17p=51J:7p=;P9P9P9P:P:P:P6P2P2P2P3g00mUR;f5R<f4R=f3R>P0P1P7MB_p=IP9P:P7P2P1P0P>P=P<f6R?f7R@f8RAM<^p=GP:P1g00n8P7Ckp=EP1g00W9RBg00WXRCPCg00X8RDP7g00XXFjp=DP>PBPCPCPDP0P1P7G|p=]P9P9P9P:P:P:P6P2P2P2P3P;P>P0P1g00YWR;g00UVR3P7MB_p=ZP9P:P:P:P2P2P<P=P>P0P1P7M<}p=\g00Z6R2#=R6#=RB#=RE#=#=#=#a#W%aE#WRE#h[%dERF%S4R490>1RG94<=%1=,2<=4?GA0<>4RGA0=04RH'794@?RIA0?=4RJ94A@%:J,2@=4AG'@[A4@?GRK%:G,2?=4@HRL'@17JGRJ94A@[P8P@P?PGPHI02PKPLP1P9P<%17RK,2@=4AGXA9P7201<;&00<ENPLeCCCxPIP5P8PAP@PJCLP8PAP@%:JC>f9RJ16@?A8E<=;0474AP7P8f:RIPJA0A?4RLA0@<4'7CLP5A0J@4R@/7LRL#Hf;RG%QL7<IP8f<RLPGA0IA4RH/7@#:C>f=R@16GIA8EJA;0474L[P7A0GJ4RA/7H#Hf>RHA0LI4RI/7A#Q7<@P8f?RAPHA0@G4/7I#:C>P513EL/9H13EG/9@g00\ERG'@fARIf@RM16AHA8E@L;0434P013EH/9MRH1@HGP513EA/9IPGfERAfDR5fCRHfB'6A8EIM;0434P713EI/9HP8fHRIfGRMfFR@/6ARLA8E5HRN;04ROCLP8PIPM%:ORPC>%HORQ%QO9<IMROP913E5RR13EHRS'6RT16M@RU,97/@GXA919TLRVPGPV%1RRV%1SRW'2RX%1@RY%1ARZ'2R['5%V9R\%V:R]%11/5K19171i173gXB9X49R^PTPXPRPV%;VPSPW%;WRVEIPLP[P@PY%;YRRPAPZ%;ZRXEIRTM9G19SA15WZR_P\P]P^PSPWPVPAPZPXM9GP1CURVP_13EARW/9M%1WRS%1MR`'5RaP\P]P^PWPS%;SPMP`%;`M9GP?CUR`Pa%PIRS%1I,F3RWPSPW13EMR^#PR\%1^,F3R^fIRb,3ERc#PRd%1c,F3Rcg00]=Re%f2,e:Rf%c;Rg#c,T:Rh5b:1T:gRg9b:f1T:;Rf5A:5A:g00n_Ri'`AA:gf9A:h/`i%SeRi5Re3R%deReP:P:1O:=P0%~:RhCMP11O:>CM%{:Rf%z:Rg1B:2Rj%y2,B:R2'E,Dg%wCRCPg1B:6R61B:BRB'E,DgPCA?:j6RCA?:2B'E,DgC]C]1tgDRDP7P0g00]iRBg00^IR2'J1s70=KB2dAr:31CqR2b7b8b9X2:X3:X::X;:1570150=120>12=<'5[[^2:^3:^::^;:P7fL#1R=fM#1R>fJRB,3E#1fK,3E#1P<P?O6b6b?b>b=b<b1b1CYg00\aCC13ENApE5HENPQePFPNA<bI7X@FPF%SERQ98EHA8EA79<bIX@FPJPH1[EHEXA<IMNP7b5A8ENQ1[ENENPOeCC16A;RO,6@RN#1RQ16L;R;#1RI'512Z3R?,2YR<12[3Rk'5P:P:P]P7X4:RlP]1517#oXB:X4:PQP<PlPl%;KX49RKPNP<P@PYPRPOP?PAPZPX1J:3RXCZEIE\PIPkPlPlPKP;PkPLP[PTPXCZE\M<^PVP_P`PaPSPWPSPWP\P^PdPcPiPeP:1O:0P1PhCMPf1n:3Rf9?:69?:jA?:Cf'E,DgPDP2b7b8b9X2:X3:1213,271271/23'5^2:^3:P7P=P>O2b6b?b>b=b<b1b1CYA0@54R@A0AH4'7#:/5PRPePPP:A0MA4/7@#:P8PBPbP7C>XP:PJA8EA5=0U4#:P7EXb0CCXJGWIP1P7O2n2001000000121000000W0WHP1P7O2n2001000000121000000WFW5WGP1P7O2n2001000000121000000W0P1P7O2n2001000000121000000b0WEWDXLFWKXO9XN9XC:WMo"). Qed.

(* [comment removed for export] *)
Lemma implMA_msys : forall {A} RNG n (dec : resp -> option A) (s : APS) (Q' : A -> footprint -> machine_state -> Prop) ms,
  implA bsegs RNG (enode n dec) (epostF Q') ms ->
  implMA RNG (msys n dec) s (fun a s' RNG' ms' => s' = s /\ Q' a RNG' ms') ms.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B2 ()) ["CANSEC1"] "p'0h04RNG'h13ms'h23rsph31ph42Hkh53ms1h61Hh71ai001ah81Ah92H0h:2HFh;2HQh<3Hath=2Q'h>3RNGh?3dech@2mshA1nhB1oi011ohC1shD2s'i021xp;1p;4p;2p;9p;6p;5p;7p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0p1002Qp4p710R1p9P0p1002op4p710p9P0p1003gp4p710p8p100oKp4p710R0g010CR2p4p710R3p8P0p10117p4p710R0p8p1004>p4p710R4p1004[p4p710p8P4P1p8P0P3p8p10121p4p710R3p1012mp4p7210p8P3p1013^p4p7210p8P3g014RR0p4p710R4p8P3p1015Mp4p73110p8P3p1016Bp4p710p8P3p1017Ap4p7210p8P3p1018Ap4p710p8p1019Fp4p70P3p8p200R3P4p8P3P2p4p7210p8P3g01:=R4p4p710p8P3g01:ZR5p4p710p8P3g01;WR6p4p7511110p8P3g01<MR7p4p710p8P3g01=DR8p4p7210p8p10057p4p7210P1p8p1005cp4p7210P1p8g007fR1j19Tg01>8j1Zj4MTg01?1j10TP8j4FTP7j2Aj4Jj5ITP6l9CTP5j6XTg01?iR5j4=Tg01@aj26Tg009_R6j2<Tg01ATj2@Tg00FDj1?Tg01B6j2>Tg00B1j2VTg00BKj4HTg01Bnj7GTg01Cgj4TTP2j4PTP0j6NTg01D]j2QTg01ESj3DTg01FIj1LTg01GAj2RTg01Gaj4STg01HAj3YTP4j3KTg00AWj3ETg01H^R4g00Z[R0f5R2P5f4R7f3R8f2R9f1R:f0R;M9Cp=BP0P9P:P;CMp=;1Q4;p=41>:;9D49p=5%L;9D4:p=3P4P0f6R<P5P2P7P81A9:P;M9Cp=1g01ISR5,R;p=2P9P5P:P;CSp=:AY:5;p=7AK859=E5:/<;p=8AK95:=E5;p=WAD4:;p=UAE59:/<;p=Og01JOR=g01KHR>%98[g01L;R?p-0[\=\7P4P0%Z0R@g01MB%0<P2P4P<P7P8CF1A<:P;M9Cf7RA#0RBP<P4PAP2P7CFRC1AA9RDP:P;EXP@PBP<PCPDP:EBP0PAf8RD=;A;RCf9RBP:f:REP;C=RFP@f<RG#0RHP:P1PGf=RI#0RJ#4PBP9O1RKA5JI;13HGn10110200021010000PGPA1689RHF1[^0=^2>'<X5?P@%2GRL#0RMP:P1PL%2IRN#0RO#4P1PG%9NPKA:I;B,@N%?Ln10110200021010000A5ON;13MLn10110200021010000PLf?RMP9f;ROPE17M9P:P;O3C8X1?X0=X3LPHF1\F^0=^2>,<CX5?P9P;A;DB;PEP:POP;C=RCP@PJP:P1PIf>RF#0RL#4PEP9O1A5LF;13JIn10110200021010000RL1AIDRNPHEB[^0=^2>'<X5?P;O1P6A;DB:P@PJP:PLPN1679EB\C^0=^2>A;BE9POP:PGP;C=P@%2FRC#0RNP:P1PC%2MRL#0RJ#4P1PF%9LPOP9O1A:M;O,@L%?Cn10110200021010000A5JL;13NCn10110200021010000PCfARNP9PIPG17N9P:P;O3C8X1?X0=X3C1629F1[^0=^2>'<P;A;EO8PIP:PFP;C=P@f@RC#0RJP:P1PC%0NRL#4PIP9O1A5LN;13JCn10110200021010000PCPO16A9F1[^0=^2>A;GI2PFP:PMP;C=RJP@%2NR6#0RHP:P1P6fBRK#2RP#0RQ#4P1PN%9PPFP9O1RRA:K;F,@P%?6n10110200021010000A5QP;13H6n10110200021010000P6fDRHP9PCPM17H9P:P;O3C8X1?X0=X3616D9R6F1[^0=^2>P:P8P9P:P;O3P@PLP:P1PN%0KRQ#4PRA5QK;13LNn10110200021010000PNPGP6F1PMP8O1%9KP1fCR6P@%0HRLP7P1PHfERQ#0RR#4P;A5RQ;RP13LHn10110200021010000PHPM16O2RMF1P@%2QRL#0RSP2P1PLfFRT#2RU#0RV#4P1PQ%9UP:A:T;K,@U%?Ln10110200021010000A5VU;13SLn10110200021010000PLfHRSP9PHP617S9P:P;O3C8X1?X0=X3L16G<RGF1]4P;P@PRP2PPPQPCPGF1P0P<PTPN1>T:P<CJPUfIRNP9PQPH17N9P:P;O3C8X1?X0=X3URNA:T:K,>URQP<CJ16IARIP;fGR0PK1>09PAP;DIRGA:S8HRC=WSHP617SCPDP:O31V5HP;CHW;X1?%2SRSfKRPP9P0PT17P9P:P;O3C8X1?X0=X3S1>SCPDP:DI\G^1?eFGP@PVP<1UVQPUPNPIF1eW4X7HP;O1P@%06RIP813I6P6PF16E7F1P;P@%2HRH#0RFP713FHPHP0P9P6PK1709P:P;O3C8X1?X0=X3HPMF1eW4n10110100021010000P:O1bBb4X:JX0=X2>CHW4W<P:P;O2n2001000000121000000W9X5?FGP@%2DR@#0RJPAP4PJP<P1%2BRJ%2ERM#0RH#4P1PB%9MP<P;O1A:E;<,@M%?Jn10110200021010000A5HM;%0J/3Jn10110200021010000X2>CTP@POP9PAP<17O9P:P;O3C8X1?X0=X3@P9F1ePDPAP5PDP<P2CPP7PAP8P:P;O39O9DX1?X0=XD5X7DP9ENeb6W6X@?W=XC5W?XA4W>X83o"). Qed.

(* [comment removed for export] *)
Section B2.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmtB AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).
  (* [comment removed for export] *)
  Variable J8 : list byte.
  Notation ABASE' := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK canary).
  Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  (* [comment removed for export] *)
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x7fb40] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x7fb94] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x7fbb8] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x7fce8] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x7fe20] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x7feb4] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).
  Notation BUF' := (BUF AI L).
  Notation RDINV' := (RDINV AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation RDBRK' := (RDBRK AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation POSTBODY' := (POSTBODY AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  Lemma rd_read_core : forall (fd : Z) (st1 : rd_st) (s : APS) RNG x1 t0 t1 t2 a1 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : amem) (A CNT : Z) (DATA junk sj : list byte),
    3 <= fd < 2^32 ->
    rd_content st1 = map bv_unsigned DATA -> BUF' mm s RNG (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj -> Z.of_nat (length DATA) < rd_cap st1 ->
    CNT = (if 65536 <? rd_cap st1 - Z.of_nat (length DATA) then 65536 else rd_cap st1 - Z.of_nat (length DATA)) ->
    ABASE' stdout_init mm -> AARGV' mm -> RNGS' RNG -> frm0 fc ->
    implMA RNG (rd_read_part fd arg1 st1) s (POSTBODY' fd)
      (GST 0x7fbc8 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 65536) a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 (Z.of_nat (length DATA))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until sj. intros FD HC BU SJ LT ECNT0 BA ARG RG FRM.
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. atop_facts.
destruct BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). pose proof BR as (BR1 & BR2 & BR3 & BR4).
pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF).
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & RG1).
assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
unfold MAX_INPUT in CAPR.
assert (CNTR : 1 <= CNT <= 65536 /\ CNT <= rd_cap st1 - Z.of_nat (length DATA)).
{ rewrite ECNT0.
destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); lia. }
pose proof ASTAGE_LEN_Z as STGZ.
pose proof (ASHENV _ _ _ _ _ P0h) as ENV. pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & _).
pose proof RSG as [(SUNP & SHUL & SWR & SAPP) _]. unfold RSTG in SUNP, SHUL, SWR, SAPP. cbn [r_lo r_hi r_rlo r_rhi] in SUNP, SHUL, SWR, SAPP.
unfold rd_read_part. cbv zeta. rewrite LENZ, <- ECNT0.
unfold AMFRAME in FR. rewrite errno_addr_ATP in ERR. unfold STAGE, ASTAGE in SJ.
apply implMA_from_evtF.
zstep. zstep. zstep.
zstep.
apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [Z.to_nat CNT; (ASTAGE_LEN - Z.to_nat CNT)%nat]) in SJ; [| cbn; lia].
cbn [mk_CB_cells app] in SJ.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in SJ. destruct SJ as [SJ1 SJ2]. cbn [cells_size csize Nat.add] in SJ2.
apply evtF_done.
set (LEN := Z.of_nat (length DATA)) in *.
assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. clearbody LEN. assert (LEN0 : 0 <= LEN) by lia.
eapply implMA_bind.
{ set (w1 := Z_to_bv 64 ASTAGE). unfold ASTAGE in w1.
replace ASTAGE with (bv_unsigned w1) by (subst w1; unfold ASTAGE; rewrite unsigned_lit; lia).
eapply implMA_msys.
eapply (read_i_spec RNG) with (lo := LO) (junk := firstn (Z.to_nat CNT) sj) (errv := errv) (RLO2 := 0x5dc940) (RHI2 := 0x5ec980); subst w1;
rewrite ?(unsigned_lit (usp + -128)) by lia; rewrite ?(unsigned_lit 6146384) by lia; rewrite ?errno_addr_ATP; unfold ATP; rewrite ?unsigned_lit by lia;
try reflexivity;
first [ exact MI | exact ST | exact Hgot | exact Hshb | exact Hini | exact Hlay | exact Hrread | exact SJ1 | exact ERR | exact SWR | exact RGimg
| idtac ].
all: first [ lia
| unfold KHIGH; lia
| unfold app_blk, KLOW, KHIGH, KEND; lia
| eapply unpoisoned_sub; [exact SUNP| lia| lia]
| unfold KEND; repeat match goal with |- _ /\ _ => split end; lia
| replace (shad 0x5dc940) with 0x800b3928 by reflexivity; replace (shad 0x5ec980) with 0x800b5930 by reflexivity;
first [ exact SWR | eapply rng_sub'; [exact RGimsh| lia] ]
| eapply rng_sub'; [exact RGstk| lia]
| eapply rng_sub'; [exact RGimg| lia] ]. }
cbv beta. intros a s' RNG' ms' [-> [-> PO]].
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
unfold ATP in MUc, RES. rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in RES by lia.
change (6214288 + -164) with 6214124 in MUc, RES.
transport_after_call bsegs mm m2 MUc WMc.
fix_ret.
rename ST2 into ST2'.
assert (WOKW : Forall (WOK usp) [(usp + -128 - 2208, usp + -128); (6146384, 6146384 + Z.of_nat (Z.to_nat CNT)); (6214124, 6214124 + 4)]).
{ unfold WOK, WOKb, ALO, ASTAGE, ablk, AIMG_HI, KLS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
assert (P2 : AHEAP AI L RNG (aps_m s) [HB (rd_buf st1) A (rd_cap st1)] m2).
{ eapply (AI_frame AI); [exact P0h| exact MUc| exact WMc|].
pose proof (AI_layout AI _ _ _ _ _ P0h) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
- left. left. lia.
- left. right; left. exists (0x5dc940, 0x5ec980). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia].
- left. right; left. exists (0x5ed1e8, 0x5ed1f0). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
assert (ERR2 : exists errv', rw_cells bsegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv']).
{ rewrite errno_addr_ATP. destruct a as [e|bs]; destruct RES as (_ & X & _); eexists; exact X. }
assert (BA2 : ABASE' stdout_init m2).
{ eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| exact ST2'| | exact ERR2].
destruct SE as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]. intros a' Ha'. cbn in Ha' |- *. lia. }
assert (ARG2 : AARGV' m2) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG]).
remember (firstn (ASTAGE_LEN - Z.to_nat CNT) (skipn (Z.to_nat CNT) sj)) as JR eqn:EJR. clear EJR.
pose proof (rng_fp_le _ _ _ _ (fp_le_refl RNG) RGA) as RGA2.
clear MUc WMc WOKW.
destruct a as [e|bs]; cbn [read_ret] in *.
-
destruct RES as (SJ1' & ERRe & He).
pose proof BA2 as (ST3 & MI3 & _). pose proof (drv_got_of_aheap AI _ _ _ _ _ P2) as (GSE & PSE & _). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
destruct ARG2 as (_ & _ & A1f). destruct (A1f ltac:(lia)) as [B1 A1]. pose proof (astring_facts usp _ _ _ _ _ A1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
apply implMA_from_evtF.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
cbn [io_diag ioA io_S].
eapply afprintf_exit with (LB := [HB (rd_buf st1) A (rd_cap st1)]) (d := DReadError arg1);
lazymatch goal with
| |- adiag_args _ _ _ _ _ _ _ => idtac
| |- forall ms'', aat_exit _ _ _ ms'' -> _ => intros ms'' AE; apply implMA_ret; apply evtF_done; exact AE
| |- _ => eassumption
end.
cbn [adiag_args]. split; [reflexivity|]. exists slack1, RA1. destruct A1 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
rewrite ?unsigned_lit by lia. unfold GLOBALS_TOP, FmtFp.INT_MAX. destruct (RG1 ltac:(lia)) as [RGa1 RRa1].
repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
- destruct RES as (SJ1' & ERRe & Hbs).
pose proof (bytes_at_bound _ _ _ _ (proj2 (proj1 SJ1'))) as BB. cbn [cells_bytes cbytes app] in BB. rewrite !length_app, length_skipn in BB.
apply implMA_from_evtF.
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 CNTR LENR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. if_cases K1; zify_cond K1.
+
pose proof BA2 as (ST3 & MI3 & FR3 & AS3 & SE3 & GU3 & TR3 & HI3 & ROD3 & RCS3 & RCB3 & RSG3 & [errv3 ERR3] & SOF3).
rewrite errno_addr_ATP in ERR3.
pose proof RSG3 as [(SUNP3 & _ & SWR3 & _) _]. unfold RSTG in SUNP3, SWR3. cbn [r_lo r_hi r_rlo r_rhi] in SUNP3, SWR3.
pose proof (ASHENV _ _ _ _ _ P2) as ENV2. pose proof ENV2 as (Hgot2 & Hric2 & Hshb2 & Hini2 & Hlay2 & Hrmem2 & _).
pose proof (AI_block AI _ _ _ _ _ (rd_buf st1) A (rd_cap st1) P2 ltac:(left; reflexivity)) as (_ & _ & _ & _ & SHA2 & WRA2 & _ & (RLO' & RHI' & Ar1' & Ar2' & Ar3' & Ar4' & ARR' & ARW')).
apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SJ1'. destruct SJ1' as [SJa SJb]. cbn [cells_size csize Nat.add] in SJb.
pose proof (rw_cells_bytes_at _ _ _ _ SJa) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
pose proof BLK as BLK2. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK2. destruct BLK2 as [BLK1 BLK2].
cbn [cells_size csize Nat.add] in BLK2. replace (length DATA + 0)%nat with (length DATA) in BLK2 by lia.
apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [length bs; (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat]) in BLK2; [| cbn; lia].
cbn [mk_CB_cells app] in BLK2.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in BLK2. destruct BLK2 as [BLK2 BLK3]. cbn [cells_size csize Nat.add] in BLK3.
pose proof (block_hull RNG m2 (A + LEN) (Z.of_nat (length bs)) RLO' RHI' ltac:(lia) Ar1' Ar2' ltac:(lia) ltac:(lia) ltac:(lia) ARR' ARW') as (HR & HW & Hh1 & Hh2 & Hh3 & Hh4 & Hh5 & Hh6).
pose proof (hull_props (A + LEN) (Z.of_nat (length bs)) ltac:(lia)) as (_ & _ & _ & _ & Hp5 & Hp6).
assert (UPD : unpoisoned m2 (A + LEN) (A + LEN + Z.of_nat (length bs))).
{ eapply unpoisoned_sub; [apply (ablock_unpoisoned m2 A (rd_cap st1) SHA2); first [lia | clear -BR4; Z.div_mod_to_equations; lia] | lia | lia]. }
assert (UPS : unpoisoned m2 6146384 (6146384 + Z.of_nat (length bs))) by (eapply unpoisoned_sub; [exact SUNP3| lia| lia]).
unfold ASTAGE.
zstep. zstep. zstep. zstep.
zstep.
eapply evtF_cut.
{ eapply (memcpy_i_spec RNG) with (lo := LO) (src := bs) (junk := firstn (length bs) junk)
(RLO1 := 0x5dc940) (RHI1 := 0x5ec980) (RLO2 := hull_lo (A + LEN)) (RHI2 := hull_hi (A + LEN) (Z.of_nat (length bs)));
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- mem_inv _ _ => exact MI3
| |- stk _ _ _ _ => exact ST3
| |- bytes_at _ _ _ _ => exact SRCB
| |- rw_cells _ _ _ [CB _ _] => replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact BLK2
| |- rw_cells _ _ _ _ => assumption
| |- length _ = _ => lia
| |- app_blk _ _ => first [ eapply ablk_app_blk; [eapply ablk_sub; [exact BR1| lia| lia]| lia] | unfold app_blk, KLOW, KHIGH, KEND in *; lia ]
| |- unpoisoned _ _ _ => assumption
| |- wr_at _ _ (shad 0x5dc940) _ => exact SWR3
| |- wr_at _ _ _ _ => assumption
| |- rng_aimg _ => exact RGimg
| |- rng _ (shad 0x5dc940) _ => replace (shad 0x5dc940) with 0x800b3928 by reflexivity; replace (shad 0x5ec980) with 0x800b5930 by reflexivity;
eapply rng_sub'; [exact RGimsh| lia]
| |- rng _ (shad _) _ => assumption
| |- rng _ LO _ => eapply rng_sub'; [exact RGstk| lia]
| |- rng _ 6146384 _ => eapply rng_sub'; [exact RGimg| lia]
| |- rng _ (A + LEN) _ => eapply rng_sub'; [exact RGA2| lia]
| |- _ /\ _ => unfold KEND in *; repeat match goal with |- _ /\ _ => split end; lia
| |- _ => unfold KHIGH in *; lia
end. }
cbv beta. intros ms'' PO.
destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUd & WMd & MI4 & ST4 & NB & _).
rewrite !(unsigned_lit (A + LEN)) in MUd, NB by lia. rewrite !(unsigned_lit (Z.of_nat (length bs))) in MUd, NB by lia.
rewrite ?(unsigned_lit (usp + -128)) in MUd, ST4 by lia.
transport_after_call bsegs m2 m3 MUd WMd.
fix_ret.
assert (WOKD : Forall (WOK usp) [(usp + -128 - 2240, usp + -128); (A + LEN, A + LEN + Z.of_nat (length bs))]).
{ unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia| constructor; [| constructor]].
cbn [fst snd]. right; right; right; left. eapply ablk_sub; [exact BR1| lia| lia]. }
assert (P3 : AHEAP AI L RNG (aps_m s) [HB (rd_buf st1) A (rd_cap st1)] m3).
{ eapply (AI_frame AI); [exact P2| exact MUd| exact WMd|].
pose proof (AI_layout AI _ _ _ _ _ P2) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
constructor; [| constructor; [| constructor]]; cbn [fst snd].
- left. left. lia.
- right; left. exists (HB (rd_buf st1) A (rd_cap st1)). split; [left; reflexivity| cbn; lia]. }
assert (BA3 : ABASE' stdout_init m3).
{ eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA2| exact WOKD| exact MUd| exact WMd| exact MI4| exact ST4| |].
- destruct SE3 as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
eapply rw_cells_magree; [eapply magree_of_munch; [exact MUd| exact WMd]| exact Hc|]. intros a' Ha'. cbn in Ha' |- *. lia.
- exists errv3. rewrite errno_addr_ATP.
first [ exact ERR3 | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUd| exact WMd]| exact ERR3|]; intros a' Ha'; cbn in Ha' |- *; lia ]. }
assert (ARG3 : AARGV' m3) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKD| exact MUd| exact WMd| exact ARG2]).
clear MUd WMd WOKD.
zstep. zstep.
apply evtF_done.
replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; intros E; rewrite E in K1; apply K1; reflexivity).
apply implMA_ret. apply evtF_done. cbn [POSTBODY]. unfold RDINV. cbn [rd_content rd_cap rd_buf].
assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
{ unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
rewrite LEN'.
pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact NB)) as BLK1'.
replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) in BLK1' by lia.
assert (BLK' : rw_cells bsegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk))]).
{ apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [exact BLK1'|]. cbn [cells_size csize Nat.add].
replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + Z.of_nat (length DATA) + Z.of_nat (length bs + 0)) by lia.
replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact BLK3. }
pose proof (rw_cells_CB_join _ _ _ _ _ _ SJb ltac:(replace (6146384 + Z.of_nat (length bs + 0) + Z.of_nat (Z.to_nat CNT - length bs)) with (6146384 + Z.of_nat (Z.to_nat CNT + 0)) by lia; exact SJ2)) as SJc.
pose proof (rw_cells_CB_join _ _ _ _ _ _ SJa ltac:(replace (6146384 + Z.of_nat (length bs)) with (6146384 + Z.of_nat (length bs + 0)) by lia; exact SJc)) as SJ'.
do 17 eexists. exists F, fc, m3, A, (DATA ++ bs), (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk)).
exists (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) sj) ++ JR)), 0x7fb74.
split; [replace (Z.of_nat (length bs) + LEN) with (LEN + Z.of_nat (length bs)) by lia; reflexivity|].
split; [left; split; reflexivity|].
split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
split; [| split; [| split; [exact BA3| split; [exact ARG3| split; [exact RG| exact FRM]]]]].
{ split; [exact P3|]. split; [exact SO0|]. split; [exact RK|]. split; [exact HA|]. split; [exact BLK'|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|].
split; [rewrite length_app; lia|]. split; [exact BR|]. split; [exact RGA2| exact RGAS]. }
{ unfold STAGE, ASTAGE. replace ASTAGE_LEN with (length bs + (Z.to_nat CNT - length bs + (ASTAGE_LEN - Z.to_nat CNT)))%nat at 1 by lia. exact SJ'. }
+
assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
cbn [length Nat.eqb]. apply evtF_done.
apply implMA_ret. apply evtF_done.
cbn [POSTBODY]. unfold RDBRK.
do 17 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk.
split; [rewrite LENZ; cbn [Z.of_nat]; reflexivity|].
split; [exact HC|]. split; [| split; [exact BA2| split; [exact ARG2| split; [exact RG| exact FRM]]]].
split; [exact P2|]. split; [exact SO0|]. split; [exact RK|]. split; [exact HA|]. split; [rewrite <- ELEN; exact BLK|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|].
split; [lia|]. split; [exact BR|]. split; [exact RGA2| exact RGAS].
Qed.

  (* [comment removed for export] *)
  Lemma rd_read : forall (fd : Z) (st1 : rd_st) (s : APS) RNG x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : amem) (A : Z) (DATA junk sj : list byte),
    3 <= fd < 2^32 ->
    rd_content st1 = map bv_unsigned DATA -> BUF' mm s RNG (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj -> Z.of_nat (length DATA) < rd_cap st1 ->
    ABASE' stdout_init mm -> AARGV' mm -> RNGS' RNG -> frm0 fc ->
    implMA RNG (rd_read_part fd arg1 st1) s (POSTBODY' fd)
      (GST 0x7fbb8 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B2 ()) ["CANSEC1"; "B2"] "p'0h01Hh14__x1h21kh34__x2h41bi001bh52KWh64__p1h77__arithh87__sat49h97__sat50h:7__sat51h;7__sat52h<7__sat53h=4cstrh>1zh?2Hah@1mhA4__ffhB8__varmaphC5__withD5cstr0hE4errvhF3ms'hG1ni011nhH1xhI1yhJ2H2hK2H3hL2H4hM2H5hN7__sat54hO7__sat55hP2H6hQ2H7hR2H8hS2_HhT3_H0hU1li021lhV1AhW3ARGhX2BAhY2BUhZ4CAPKh[4CAPRh\4DATAh]1Fh^2FDh_3FRMh`2H0ha2H1hb2HChc4LENRhd4LENZhe2LThf2MIhg2RGhh3RNGhi2SJhj3_H1hk3_H2hl3_H3hm3_H4hn2a0ho2a1hp2a2hq2a3hr2a4hs2a5ht2a6hu2a7hv2fchw2fdhx4junkhy2mmhz1ri031rh{1sh|2sjh}3st1h~2t0i042t1i052t2i062t3i072t4i082t5i092t6i0:2x1i0;3x23p%0p%1p&0p&1p;1p;2p;4p;3p;;p;?p;9p;<p;7p;Mp;Op;6p;5p;>p;Up;:p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0g002QR1p4p710R2p9P0p1002op4p710p9P0p1003gp4p710p8p100oKp4p710R0p1012mR3p4p710R4p8P0p10117p4p710R0p8p1004>p4p710R5g004[R6p4p710p8P5P2p8P0P4p8g01RNR4p4p710R0P3p4p7210p8P0p1013^p4p7210p8P0g014RR3p4p710R5p8P0p1015Mp4p73110p8P0p1016Bp4p710p8P0p1017Ap4p7210p8P0g018AR7p4p710p8P0p101SFp4p7X1111111111111111111111111111111111111110p8g019FR8p4p70P0p8p101TIp6051001R0P5p8P0p1010Cp4p7210p8P0p101HAp4p710p8P0p101:Zp4p710p8P0p101;Wp4p7511110p8P0p101<Mp4p710p8P0p101=Dp4p7210p8g0057R0p4p7210P2p8g01UJR5p4p7210P2p8P4k11wTg006@j13Tg006ej1hTg007Ck10STg00jKj18TP0k21lTg007fk10>Tg00G?k10XTg008Hj1<Tg008fj2{Tg00D<j2:Tg01Uik11vj2]Tg04I\k40^Tg00AWj37Tg01VSm;0nTg01WLk21UTg04Kfm?0iTg01Xdm91GTg01Y^m<1BTg01ZWk11?Tg01cLk10fTg04M_k10dTg039@k30cTg00::j1pTg00;Oj3dTg01dHk70aTg01eFj1yTg01fCj3kTg00cEj2BTg00:Zj2aTg00=_j1CTg0121k11qTg01]Rk21oTg00fIk10ZTg01^1k41iTg01^MlMETg00eJk10rTg00C_j2QTg01_Kj20Tg01`1lOOTg00FDk10jTg01`ck11NTg01a\j79Tg009Cj2;Tg01\=k11;Tg04NXk40eTg04OJk207Tg01k^m;05Tg01m\k204Tg021Wk102Tg02>kk119Tg01lWj1}Tg01nSj1|Tg01oYk103Tg04P>k118Tg022[j2lTg04Q3j2zTg009_S00j24Tg020\k20RTg00B1j2ATP5k417TP1j6?Tg04L]k30PTP3k60OTg02Knk116Tg01ATj21Tg02L[j4=Tg0235j2FTg02MHk115Tg02NOk114Tg044Nk413Tg04V>j5vTg04Vgk30ATg04WNk30BTg04XYk20LTg05\]k212Tg02Qjj3uTg03J>k20JTg04[dk31uTg05]Tk21tTg04`8k20ITg04\Lk209Tg04]Nj1~Tg01GAk21sTg04^Nk10GTg04_?m>0:Tg02UWk111Tg02kRk20~Tg04cCk40\Tg05^Mk20|Tg02PJk20zTg03M`k21pTg05_9k11nTg03P=k51mTg02T2k30vTg05`0k11kTg05`gk30CTg03IRk41jTg02Q2k21hTg02S0k21gTg02W9k31fTg01XGj2YTg01bNk11dTg01[Gk11cTg00dej1tTg00MOk20[Tg00N7k30]Tg0286k21bTg01]2k21aTg028gk21`Tg00Ffk10oTg029Hk21^Tg02XTk21]Tg029ek21\Tg02:Lk21[Tg02;3k21ZTg02;Yk21YTg02<?k21XTg00fhk20=Tg00h:k30<Tg00hck20lTg00G_k20kTg00iOk11TTg00imk40?Tg00H=k11STg00H[k11RTg00Iik20UTg00JLk61QTg00IFk20@Tg04R4k31PTg00N[k31OTg00K0k21MTg00KRk21LTg00L>k31KTg00L]k41JTg03dIk20WTg03e@k20TTP6k60VTg05aTk21ITg03]Hk11HTg05b4k21VTg02k6k41WTg05bTmU0hTg04i_k50mTg0270k21FTg027SS01k21ETg04RWk61DTg00RZk40YTg04jXm:0FTP7k71CTg04Hak20MTg04J8k21ATg04Jok20qTg01g>k21@Tg02X4k11eTg00l9k40KTg01i=k30ETg02F8k10sTg03lYk10tTg01h@k30uTg024Ik20_Tg02OWk21>Tg04Tok31=Tg04YUk30wTg04Z\k20yTg01Gak41<Tg00SEk710Tg00Sik71rTg00TMk81:Tf2R7f1R6';f0R3'4p>0N20M83p>0`21A83p=T20q83p=21B63#Cp=@g04oSg04m_S02773p=xg00V4R121@63777p=cg00[PR5f3R0/F7$1e/a6;d3p=[g00Z[R4P0P7Ad563H0Kp=n%33#3#3#3#3#3#3#3p=jg00UVR2/;3p=>A7163,47p=If6R9f5R:f4R;40E&0s71Q63$0t60E0'4p=K1;:;B0u076/43'4p=L1;;0g050NR<,;7'41l16'4/43p=W1463,47,40,4;p=V%33#3p=N%33#<p=\20M83-0_1,06p=X%83#8p=H%83#8#8#8p=R%33#8#8#8p=^f7R=P9B0P:;0P7P6P3J0Op=M1a76=d53p>08P4P0P7P6H0K/43p>0;1463,47p>001;3<p>0p1l13p>0D1476/43p>0g1;761;3<'4p>0}&0s71Q63$0t60E0p>0xB0u9:;B0E076/43'4p>0{Ad563p>0bP4P6g053BP3H0Kp>01P4P7P6P3H0Kp>0620R76/43p=U20_13p>0QA7163p=SP;P01176P3C=p=DP9P:P;P0P7C=P6P3C=p=51063,17p=GP9P:P;P0P7P6P3C=C=p=6%83#3p=b%33#8p=o%33#3#3#3p=w21>63:1=07p=Jg01L;S03@0w63-0y7p=fQ03P=P9P:P;P0P7P6F9<0w3p=_20y76=703p=`g00]iR<g057cS04773p=Pg058CS05P1P6P3H1<p>0H1F63,07p=rg00^IS0697<3p=g20q86/F3p=sP1P6g00^iP3H0Yp=mP6g00W9S07g00WXR>P>g00X8S08P3g00XXR?K10p=iP7Q07P>P>Q08P1P6g00VRP3H0YP?K10p=eP7Q07P>P>Q08P6P3K1rp=qP0Q07P>P>Q08P7P6P3L1:p=Z20M83-0_1p>1_&1w8R?g01ISg01JOg00Z6R@#3S09#3S0:#3S0;#3S0<#3S0=#3S0>#hRA$0SRBQ09#8S0?#hRC01lBQ0=#hS0@$0SS0AQ0;#hRD$0SRE$0>\B&0XES0BQ0BQ0B%8@S0C#<fKRFQ09#<RGQ0=#<S0D'{S0E,:F40N&0X1S0F&0`FPEP1&1vDS0GP0H0^37p,2rcRDp,2AIRHp,1LRIP9PFfJRJfLRK#TP:%2KP;P0N;0n21U=01@E9fNR=#2':p,3uspR:p,3TIDRLp,2S0RMp,2S1RNp,2S2ROp,2S3RPp,2S4RQp,2S5RRp,2S6RSp,2S7RTp,2J8RUp,4RSTKRVp,6canaryRWQ02f9N?0iP:p,4argvRXp,2P0RYp,2P1RZp,6slack0R[p,6slack1R\p,3RA0R]p,3RA1R^f:R_N91Gp,6rng_fsR`P:PVPIPXPYPZP[P\P]P^fORaN<1Bf=Rb$1?P9PDPHPIPbfRR9fQS0HfSRc#Tf<Rd%2cf;S0IP_N;0nQ00PDPHPIP9&0fcg04nZR_fTS0J#TRe$0dQ0J#2Rf80cb%p_Rg3df>S0KK0a%yc#xAkDIcAcbceQ0KPb1BEdRe/adPf%CeReQ0I%p5R5C[CnQ0>#3Rd#3#jS0L#<RhPfPf%>3RifURj#2Rk1{G3Rl3IX21PePfPDPbPfP9PbPfP9PbPfQ0C#8S0M#<RfFKELDWDV&1q8-1o?R?PcfVR8PEP1Q0GQ0Bg00YWS0N$0ZS0OPX%pEH1iH0^RbPjQ0JPDPHP`P:PLPMPNPOPPPQPRPSPTp,2S8Rep,2S9Rmp,3S10Rnp,3S11RoPVPWPIPXPYPZP[P\P]P^PUP8MMEP9&0rd,Q:S0P,0ARdQ0<#8#N#j#\,0ARpg05GT,0ARqQ0HfPS0QPa10AGRrQ0K,0AP=fMRsPKPFPJfIRtfHRufGRv10AZS0R1XAj10A8S0S10Akg0568,0AS0TfFS0UPePmPnPofERkfDRwfCS0VfBS0WMOOfAS0X%8@#H#R#^#^#N#\S0Y,0ARxf@Ry&0jBRzf?S0Z&1N4R{F9GMP3PDPHPIQ0J&0fj%T8$0dQ0Z%2840c=d_gPyK0a%y8#xAkDI8fWRg#T9cy8Q0XPyQ0Z,BER_Q0Z'a%2gR|%C_R_Q0KP5C[CnPhP|P|fXR}#2R~=IilX21P_P|PDPyP|PjPyP|PjPyP|PfFKELDWDVQ00%yg#xAkDIgQ0X%T}7cgQ0WQ0X1BEyR|P~%C|S0[Q0ZP5C[808yPhP~P~fYR|#2R_=IilX21Q0[P~PDQ0XP~P8Q0XP~P8Q0XP~PfFKELDWH0;400P?PgfZR~PbP|P}PDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUP~MMEP8PdPpPqPjQ0JPcPrQ0W,0AP9Q0HQ0QPaP=PsPKPFQ0R1XA|10A~S0[10A_Q0TPJPePmPnPoPtPuPvQ0UMOOPkPxPwPzQ0VP{F9GMP3%y|#xAkDI~f[S0\#T9cw~PkPwQ0V,BER_Q0VQ0\#2S0]%C_S0^Q0WP5C[408PhQ0]Q0]f\S0_#2R_=IilX21Q0^Q0]PDPwQ0]P|PwQ0]P|PwQ0]PfFKELDWH0;400Q00Q0\9kDIQ0\Q0_#T5ckQ0UPk1BEwS0]/awP_Q0]#CS0]Q0VP5C[CnPhP_P_f]S0^#2Rw=IilX21Q0]P_PDPkP_P~PkP_P~PkP_PfFKELDW400P?Q0\f^R_PbQ0^Q0_PDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUP_MMEP~PdPpPqP|P}PgPrQ0U,0AP8PjQ0JPcP9Q0HQ0QPaQ0RQ0^,XA10A_10AwQ0TP=PePmPnPoPsPKPFPJMOOPtPxPuPzPvP{F9GMP3Q0^9kDIf_Rw#T9cu_PtPu1BEvRk/av%2wS0]%CkS0`Q0UP5C[CnPhQ0]Q0]f`S0U#2Rk=IilX21Q0`Q0]PDPuQ0]Q0^PuQ0]Q0^PuQ0]PfFKELDW400Q00Q0U#T9ctwPJPt1BEuS0]PkQ0]#CS0]PvP5C[808uPhPkPkfaRu#2Rv=IilX21Q0]PkPDPtPkP_PtPkP_PtPkPfFKELDWH0;P?PwfbRkPbPuQ0UPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUPkMMEP_PdPpPqQ0^Q0_Q0\Pr10AJP~P|P}PgP8PjQ0JPcQ0R1XAu10Ak10AvQ0TP9PePmPnPoQ0HQ0QPaP=MOOPsPxPKPzPFP{F9GMP3%Tk9cFuPsPK1BEFS0]fcRv#2RtQ0]#CS0]PJP5C[808FPhPtPtfdS0`#2RJ=IilX21Q0]PtPDPKPtPuPKPtPuPKPtPfFKELDWH0;Q00P=Ps1BEKRt/aKPJ%CtS0]PFP5C[CnPhPJPJfeRt#2RK=IilX21Q0]PJPDPsPJPkPsPJPkPsPJPfFKELDWP?PvffRJPbPtQ0`PDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUPJMMEPkPdPpPqPuQ0UPwPr10A=P_Q0^Q0_Q0\P~P|P}PgQ0R1XAt10AJ10AKQ0TP8PePmPnPoPjQ0JPcP9MOOQ0HPxQ0QPzPaP{F9GMP3Q0QPa1BE=RK/a=%2J%CKPsP5C[CnPhfgRs#2S0]Q0]fhRK#2R==IilX211@EaQ0]PDQ0QQ0]PtQ0QQ0]PtQ0QQ0]PfFKELDWQ001;h=&0p=fiRa#2S0]=IilX21$0D40gQ0Q,@EP=PDQ0HP=PJQ0HP=PJQ0HP=PfFKELP?PsfjR=PbPaPKPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUP=MMEPJPdPpPqPtQ0`PvPr10A9PkPuQ0UPwP_Q0^Q0_Q0\Q0R1XAa10A=Q0],0AQ0TP~PePmPnPoP|P}PgP8MOOPjPxQ0JPzPcP{F9GMP3%2=Rc,;h&0pcfkRc#2R8=IilX21$0D40gQ00B0}h88flS0]#2R8=IilX21$0DQ0J,@EP8PDPjP8P=PjP8P=PjP8PfFKELP?PcfnR8PbfmRjQ0]PDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUP8MMEP=PdPpPqPaPKPsPrQ0SPJPtQ0`PvPkPuQ0UPwQ0R1XAj10A8%2jR9,0AQ0TP_PePmPnPoQ0^Q0_Q0\P~MOOP|PxP}PzPgP{F9GM[P3B0}h99foR9#2S0S=IilX21$0D1@EgQ0SPDP}Q0SPjP}Q0SPjP}Q0SPfFKELQ001@E}fpR}#2Rg';PDP|PgP8P|PgP8P|PgPfH0xK0{P?P9frRgPbfqR|P}PDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUPgMMEP8PdPpPqPjQ0]PcPrQ0[P=PaPKPsPJPtQ0`PvQ0R1XA|10Ag%2|,0AQ0TPkPePmPnPoPuQ0UPwP_MOOQ0^PxQ0_PzQ0\P{F9GMP31@E~%2g';PDQ0_fsS0\#2R~P|Q0_P~P|Q0_P~PfH0xK0{Q0JP:PLPMPNPOPPPQPRPSPTPUPVPWQ02P_N?0iQ00P4Pw&1;:S0JQ0PH0e2074wP:PMPNPOPPPQPRPSPTPUPwN;05204Lw&02w&19W00b5R_-01w%}w%|w&03wg051HS0_g052ERfQ0U1]AqQ0?#3S0^#3S0[#8S0S#N$0r'QR~&18300b5R5406XEB,lBQ02,zw'45Uw5Uw9UwVDVDVP?ftS0HfwS0aPbfvRlfuS0bPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUQ0aMMEQ0\PdPpPqPgP|P}Pr10AwP9P8PjQ0]PcP=PaPKQ0R1XAlQ0a,0A%2l,0AQ0TPsPePmPnPoPJPtQ0`PvMOOPkPxPuPzQ0UP{F9GMP3P4PuQ0JQ0PH0e2074kP:PMPNPOPPPQPRPSPTPUPkN;05204Lk&02k201k_%}k%|k&03kQ0_B06v~5XEB,lBQ02,zk'49Ukf5Uk9UkVDVDVQ002074vP:PMPNPOPPPQPRPSPTPUPvN;05204Lv&02v201v_%}v%|v&03v20RvVQ0_Q0`@06~5XEB,lBQ02,zv'49Uvf5UvDVDVP?fxS0Pf{S0JPbfzS0UfyS0cPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUQ0JMMEQ0aPdPpPqPlQ0bQ0HPr10AvQ0\PgP|P}P9P8PjQ0]Q0RQ0U,XAQ0J,0AQ0U#2,0AQ0TPcPePmPnPoP=PaPKPsMOOPJPxPtPzQ0`P{F9GMP32074tP:PMPNPOPPPQPRPSPTPUPJN;05204LJ&02J201J_%}J%|J&03J20RJVQ0_B06s~5XEB,lBQ02,zJ'49UJf5UJDVDVQ0FPEP1Q0GPtH0^RfQ0F&0Q31@EJS0_'SWUg00Y8R51BEtR~%C3Q0_'SXG5%C~R~,A11B1fPEP1Q0GPtH17E?&0Qf/S~ef}S0G$0`RfPuE?&0Qf/S~P1Q0_P?Q0Gp+01AS0Fp+01@S0280PbR~f~S0dPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUQ0FMMERff|S0ePdPpPqQ0JQ0UQ0cPr10AKS0fQ0PQ0aPlQ0bQ0HQ0\PgP|Q0R10A3Q0F,0AS0gQ02#2S0h,0ARuQ0TP}PePmPnPoP9P8PjQ0]MOOPcPxP=PzPaP{F9J0OX>1P?Q0eQ02Q0d80PbQ0GPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUQ02MMEQ0JPdPpPqQ0UQ0cQ0PPr10AsR5Q0aPlQ0bQ0HQ0\PgP|P}Q0RQ0_,0AR_Q02,0ARkQ0d#2S0i,0ARwQ0TP9PePmPnPoP8PjQ0]PcMOOS0jP=PxPaPzPKP{F9S0kP4Q0eQ03P?Q0GP~Q0dPfP3J0OWFS0lQ0kPBPBPBPBPBPB&16BRfPBPcPfDD11BgS0mPfQ0P,1BS0nPBPfPBP9PfDDS0oF511BpS0pPBPBPf11B_Pf11BlS0qPBPfPBPoPfDDS0rF5Q0J,1BS0sPBPBPBPfPBP}PfDDS0t11B5PBPfPBPmPfDDS0uQ0U,1BS0vPBPBPf11BwPfQ0H,1BS0wPBPfPBPjPfDDS0xF5F5F5S0yPzPBPBPBPBPfPBP|PfDDS0z11BrS0{PBPfPBPePfDDS0|C=S0}11BqRqPBPBPfPBPkPfDDS0~1]AwS101]A_S11'F9GBAPBPfPBP8PfDDS12F611BdRdPBPBPBPfPBQ0RPfDDS0RQ0a,1BS13PBPfPBPnPfDDS14Q0c,1BS15PBPBPfPBQ0TPfDDS0TQ0\,1BS16PBPfPBQ0]PfDDS17C=S18F5S19F6P=%8@#H#R#^#^#b#\S1:,0AS1;PaPzPKP{F9S1<g058oS1=#pRk&0>B/AzS1>Q03$15Rr$14R5Q0:#<Rp,0AR~g05cVS1?PCQ0C#3S0C#3S1@#<S1APCQ0=#8S0=#3S1B#3#HS1C#8#o#oS1D#w#H#NS1E#<CJPCQ0^#8#<PCQ1D#<CJPCQ0:#H#<PCQ1C#<CJH13S1CQ0jP=PxPaPzDv40A>0B4K-0L{S0:PBPBPBPBPBQ17Q16PfQ15Q0tF5Q0pPBPBPf1@EsS17,0AS1D,1BPfQ13Q0rF5Q0e,1BS1FPBPBQ0zQ0f,1BQ0uQ0sPBPBPf11BuPfQ0b,1BS0fQ12F5F5F5S1GPzPBPBPBPBPfQ0mPfC=S0mQ0{Q0|C=S1HPqPBPBPfPBQ0gPfDDS0g1]AuQ1D,]AS1I'F9GBAQ0oF6PdPBPBQ0RQ0nQ14Q0vPBQ0TQ0wQ0xC=S0xF5S1JF6PcQ1;P=PzPaP{F9=frkS1K9753X@5PB212w_P5PrPBQ1GPzPBPBQ1HPqPBQ0g11B3S1LQ0oF6PdQ1JF6PcAuAx~S1MP=PzPaP{PkG_Q1KC`X4BPBQ0Y/Qp,0AP5PrPBQ1GPzPBPBQ1HPqPBQ0gQ1D-12u,1BQ0oF6PdQ1JF6PcP3P=PzPaP{PkG_Q1KC`X4BQ1<=frkRu,A5Q1MQ0Y00JpE?Q1?@1uw_21tw_E?Q0:=75ueQ0k-0I4P4Q0jP=PxPaPzPKP{Q0@Q1E#3#H#N#H#<RuQ0@PuCJRuQ1CPpQ0A$0>RwQ0A/1uR_'A2094x=7w_dQ04,A<S1E%~u#PdQ0501s1S05$0>R_Q05Q1C00Hp'1Rx'A&0Gu=7_xdN>0:E?Q1=Q0e$11+0~S1CP1Q0iP4Q0GQ03P?Q0dp+01BS0jPbQ0FQ02PDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUQ0jMMEP3GMWFRxPBQ1GPzPBPBQ1HPqPBQ0gQ1I,F39GBAQ0oF6PdQ1JF6PcQ1;P=PzPaP{F9H0\X>1P1Q0_P4Q0GPxPBQ1GPzPBPBQ1HPqPBQ0gQ0h/F39GBAQ0oF6PdQ1JF6PcQ1;P=PzPaP{F9H0\X>1P4Q0eQ0lPBQ0yPzPBPBQ0}PqPBQ0~Q0iQ0_5rAS0~,1BQ12F6RxPdQ19F6S19P=Q1;PaPzPKP{F9S12PBQ0yPzPBPxPdPBPBQ0R10AhS0y,1BS0}Q14C=S1JQ15Q18C=F6S18P=%8@#H#R#^#b#w#\S1I,0ARxPaPzPKP{F9S0kPkQ1>P5PCQ0^#<S0^PCQ1B#bS1B#<CJQ0[#hS0[Q0<#<RuQ0[PuCJS0<+0|S0:Q19P=Q1;PaPzDv60A~>0B4K-0L{S1?PBQ1GPzPBPBQ1HPqPBQ0gQ0hQ175rAS17,1BQ0oF6S0hPdPBQ1JQ0vQ0xC=F6S0gPcPxP=PzPaP{F9=frkS1H9753X@5PBQ0[Q0<+0zQ1A+1p$1nS0YP5PrPBQ1GPzPBQ0hPdPBPBQ0RQ1LQ14Q0vQ0xF5F6PcQ1;=uA~S1MP=PzPaP{PkG_Q1HC`X4BPBQ1:/Qp,0AP5PrPBQ1GPzPBQ0hPdPBPBQ0RQ0Y,1BS0RQ14Q0vQ0xF5F6PcP3P=PzPaP{PkG_Q1HC`X4BQ0k=frkS1H,A5Q1MQ1:00JpE?Q0@Q0@Q0[Q1@#hS1@Q0<Q1@/02I1m80vAS1@Q0<$1kS0[E?Q1?Q1H575eQ12-0I4P4Q19P=Q1;PaPzPKP{Q0@Q1B#3#H#^#<S1BQ0@Q1BCJS1BQ0:PpQ0AQ1B'1S19,AwQ1;-094Q1957wdQ1EQ1B#~#PdQ05Q0:00Hp'1S0:,A_Q1B$0GQ0:57_dN>0:E?Q1CP4Q0eQ0lQ0kQ18P=P<PBQ0~Q0y60CAS0~%8@#H#R#^#b#o#N#\,0AS0l%8@#H#R#^#b#N#b#\S0:,0AS1Bn0100000020000PaPzPKP{F9S19PkQ1>P5g05dBPCQ1APCQ0S#8#NS0S#<CJPCQ0^PCQ0^CJQ0C#8S0C#hS0^Q0;#<S0;Q0^Q0;CJS0;H1jS1;Q18P=PxPaPzDv60A~>0B4K-0L{S12Q0gPcP<PBQ17Q0y60CAS17Q0lQ1Bn0100000020000P=PzPaP{F9=frkS1H9753X@5PBQ0^Q0;+0zS1?-1hxS1:P5PrQ0gPcP<PBQ17P3AuAx~S1Mn0100000020000P=PzPaP{PkG_Q1HC`X4BPBQ1I/Qp,0AS0xP5PrQ0gPcP<PBQ17Q1:P3n0100000020000P=PzPaP{PkG_Q1HC`X4BPBQ1IQ1?'Q,0AP5PrQ0gPcP<PBQ17P3Q0xn0100000020000P=PzPaP{PkG_Q1HC`X4BQ19=frkS19,A51]AxQ1?'Q,0AQ1IQ1?+1gE?Q1MQ1I00JpE?Q0^Q0;80vA9uAxQ0^Q0;61fxE?Q12Q19575eQ0k-0I4P4Q18P=PxPaPzPKP{Q0@Q0S#8#b#o#N#o#b#N#H#<S0SQ0@Q0SCJS0SQ1;PpQ0AQ0S'1S18,Aw2094xQ1857wdQ1EQ0S#~#PdQ05Q1;00Hp'1Rx,A_Q0S$0G=7_xdN>0:E?Q1CQ0~P<1A<3Q17=7<3P<Q0j#21@Ea5rAQ0y60CA=7<3P4Q0FQ03P?Q0jp+01ES17Pbp+01DS0~p+01CS1CPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUQ17MMEP3GMWFPBPBPBPBPBQ0oQ0qPfC=Q1FPBPfQ16PfC=S16Q0pPBPBPf1@E=S0o9GBAPfQ0vQ0rF5F5Q02,1BS0SPBPBPBPfQ0wPfC=S0wAGBAcQ0uQ0d,1BS1;PBPBPfQ1C#2Rx9GBAPfQ0nQ0zF5F5PzPBPBPBPBPfQ0fPfC=S0fQ0{Q0|C=PqPBPBPfQ0~9GBAPfQ0o9rAxRx,1BQ0mF5PdPBQ1JQ0G,1BS0mPBQ0TQ13Q0tF6F5F5P8P<PBP6Q0lQ1Bn0100000020000PjPzQ0]P{F9H0\]5P6Q0F#21BEKS0t#CS0o5rAQ0y60CAS0z#g1A1hS18Q0y,]AS0y,ShS0kdS19Q0kP1Q0yQ0~1@Ec'sS12,0A,]AS0;/Y3S0^#gX>1P6PhP3E?1]Ax/YhS1I#gP1Q0;1Y3hS1M#gX>1P3Q12Q12Q12&1dDS1?Q0M#R#R#RS0M#3#R#R#N#w#j#j#\&1cDRxQ0M#8#R#R#N#w#j#j#\,;x40NS0MQ0B/BXRx#tS1H%Cx#>S0x1BEjRx#t%CxS0g#>Q0D-0[GS1:1:2GS14Q0D#>Q0E,:2[[S0h%>GS1Gg00\ERxQ0D>0]G6UW?S0DQ1GQ0E#>\x]?S0EQ0?#8#H#<S0?-0[GS1<Q14Q0?#>Q0?,{GS1K,:2[[S1DQ1GQ0?>0]G6VxW?S0?Q1GQ1K#>\x]?S1K21b:uS1N%>:%>u21a:uS1O#>S1P[[S1QQ0>#<S0>-0[GS1RQ14Q0>#>Q0>,{GS1S,:2[[S14Q1GQ0>>0]G6VxW?S0>Q1GQ1S#>\x]?S1Gp-0Rx%>6S1TQ0L#3#j#\S0L,;6,40S1U1:07S1VQ1?Q0MQ1HQ0xQ1<Q1DQ0?Q1KQ1NQ1QQ1RQ14Q0>Q1G21`:uS1WA71u2S1X$0o21^:uS1Y-1]uQ1O'Q,S:[S1Z21\:uS1[1:2uQ1PQ1O/:u'4[S1P21[:uS1\1:u2Q1O,:uQ1O/;2'4[S1]21Z:uS1^Q1XQ1Y=712[S1Y21Y:uS1_Q1XQ1O/S:[S1Xg00\a21X:uS1OeS1`Q1Og00]=S1aQ0O$0ZS1b-0=1S1cQ0O-0=1Q0N-0=1S0N60<160<1g00n_S0O+0lQ1a#pS1d3dQ1a$0XS1eP120k17S1fP6&1T1S1gH0?S1h&1S1S1i&1R1RuQ09-0U1S0920U1@R@'m,iu&0j>S1jPuPuQ07P>P>Q08P;J1QS1kQ0L-0@1S1l9eu@S1m5quQ1jPu20@12S1nQ095euQ1jQ1nQ09:1P1@S095euQ0920@1G>1O1AS1o'm,iu5quCZCZCZQ08-1MuS1pP3P7Q06,A<21L37#gdB1K126H1JR2bAbBbCX11X31X6x1:63RGQ1U%>0S061F0;R;#>Q1S,:;'4S1q[[[^11^31^6xP3Q0VQ0WQ0XQ0KQ0ZPyO6S0Kb7Q0X,FyR;#>Q1S,:;'4ebRbQbPbMbLbKb8b9b:b;b<b=bJUUUX11X31W6Q1TQ1UQ1VQ1q[[[^11^31^6xR;eP;P3p+01O#2R;,;h1@ElP;f8S1UQ0QP9O6b7b8b9b:b;b<bNbObDb=b0+0W+0TS0QJ0VQ12/YhS1q#gQ001Y63S0X#g1:76[S0W1Y76S1r#gR;\GQ1V\;21I63P6n2001000000120000000X@1XG1Q0W^@1^G1P3p+01FS0WQ0g'sR;PhP6O3S0g1:;hP4Q17Q03P?Q0Wp+01IR?Pbp+01HRbp+01GRGPDPHP`P:PLPMPNPOPPPQPRPSPTPePmPnPoPVPWPIPXPYPZP[P\P]P^PUP?MMEP3GMWFRUPBPBPBPBPBQ16Q0vPfQ0F,1BPBPfQ13PfC=R^F5Q0pPBPBPf1@E8R]9GBAPfQ1;Q0rF5Q0~,1BR\PBPBPBPfQ0nPfC=R[AGBA9Q0uQ1C,1BRZPBPBPf%2GRY9GBAPfQ1FQ0fF5F5F5RXPzPBPBPBPBPfQ15PfC=RIQ0{Q0|C=RWPqPBPBPfPB10AbPfDDRV1FY]Ro,0ARn,1BPBPfQ0qPfC=RmF6PdPBQ1JQ0j,1BRePBQ0TQ0sQ0wF6RTF6RSPgQ0lP|PzP}P{F9&1H],QY,0ARY,ABA7BnYP?PbPGQ0WQ17Q0~Q1CQ0jQ02Q0GQ0eQ0JQ0UQ0cQ0PQ0aPlQ0bQ0HQ0\PgP|P}%2bRY1@E9Rn'FR]P9P8PjQ0]PcP=PaPKP<1Yh]R]Q04Q00Q0X#P1;67RR[RQ1;36Q1r#PRP[RO1Y07#P\R21V63RRP3n2001000000120000000XI1XH1PO^I1^H1P3Ph1@E},s?RNQ1?Q0MQ1HQ0x1BEgRM#t%CMRM#>Q1:Q0hQ0DQ0EQ1<Q1DQ0?Q1KQ1NQ1QQ1dQ1eQ1hQ1iPuQ0920@1hRL'm,iuQ1jQ09=euLCZQ1pP2bAbBbCX11X311F36R:/:h1F67R`/;h[^11^31P3Q0c,@Ep+01R#2Q0IO3b7b8b9b:b;b<bDb=b0O3b0H1WQ04=7<]P<Q04p+01J#2RH1@E|S04'FRDP<P1P3PhPDn0100000020000'SX4<1A1N1YhNP3J0Vb0PsPJPtQ0`NU0hb0I0mb5b0b5b5b0W5Q0z#PQ19Q0kP1Q0yQ0^#PX>1P6PhP3E?Q1I#PP1Q0;Q1M#PX>1P3Q12Q0QJ0VQ1q#PQ00PQPO1;70\PPRP6n2001000000120000000XI1XH1PQ^I1^H1Q0g1;h;P4Q17PUPSPgQ1BP|PzP}P{F9R;PBPXPzPBPBPWPqPBPVQ0}PmF6PdPTF6PgQ0lP|PzP}P{F9RTPkQ1>P5PCQ1APCQ0=#8#NRC#<CJQ0<+0|RVPSPgQ1BP|PzDv60A~>0B4}-0L{RWPBPBPBPBPBQ0wQ0sPfPeP[F5Q0pPBPBPfAGBAnPfQ0SQ0rF5Q17,1BPBPBPIAGBA}Q0uP\PBPBPfAGBAYPfQ0mPmF5F5F5RmPzPBPBPBPBPfQ0vPfQ0{Q0|F5RYPqPBPBPfPB10A?PfDDRfQ0}P^F6PdPBQ1JPZPBQ0TQ1FQ0fF6RZF6Q0\Q0lPgPzP|P{F9=frkR?9753X@5PBQ0YP5PrPBPmPzPBPBPYPqPBPfQ1LP^F6PdPZF6Q0\Q1B=uA~R~PgPzP|P{PkG_P?C`X4BPBQ0:/Qp,0AP5PrPBPmPzPBPBPYPqPBPfQ0RP^F6PdPZF6Q0\P3PgPzP|P{PkG_P?C`X4BAfrTkRr,A5P~Q0:00JpE?Q1@Q0[E?A75Wre20I4;P4PSPgQ1BP|PzP}P{Q0@%3C#H#^#<RCQ0@PCCJRCPVPpQ0A/1CR{,AwQ1B-094=7w{dQ1E%~C#PdQ0520HVp'1RV,A_&0GC=7_VdN>0:E?Q1=Q17$11+0~P4Q17PUPTPbPGQ0WQ17Q0~Q1CQ0jQ0FQ0dQ0eQ0JQ0UQ0cQ0PQ0aPlQ0bQ0HQ0\PgP|P}P9PhP8PjQ0]PcP=PaPKPs21Fho1:ho1Yho+1EP]P<Q011:hNP<P1P6Php+01K/sMn0100000020000,ShP61:hDRDQ18WUP3O1&0oDQ1?Q0MQ1HQ0xQ0H,BERD#t%CD#>Q1:Q0hQ0DQ0EQ1<Q1DQ0?Q1KQ1NQ1QQ1WQ1ZQ1[Q1PQ1\Q1]Q1^Q1YQ1_Q1XQ1`Q1OQ1dQ1eQ1hQ1iPuPuQ07P>P>Q08Q09,mL,iuJ1DQ1jPuQ099euLQ1jP1PLg00n8Q09H0Y,iuCZCZQ1pP2bAbBbCX11X311:h:g05I@[1;h`1F70,Sh[[^11^31P3Q0j,@Ep+01Z#2Q0ZQ0VO4b7p+01YQ0F,@E's,ShebMbLbKbJbab`b8b9b:b;b<bDb=b0WGP3O1n10210010300021010211101b4bzPJPtQ0`PvNU0hI0mN:0Fb5b0b5b5b0W5n0110001020101P3O1b5b4N:0FN:0FQ11Q0_Q0_Q1?Q0MQ1HQ0xQ0t#tRvQ0o#>RtQ1:Q0hQ0DQ0EQ1<Q1DQ0?Q1KQ1NQ1QQ1RQ14Q0>Q1GQ0L,;7,40RJ1:70REQ1?Q0MQ1HQ0xQ1<Q1DQ0?Q1KQ1NQ1QQ1RQ14Q0>Q1GQ1WQ1ZQ1[Q1PQ1\Q1]Q1^Q1YQ1_Q1XQ1`Q1OQ1aQ1b$0Z-0=1Q1cQ0N60<160<1Q0O+0lQ1d3dQ1eP1Q1gP6P1P1Q1gP7Q1fH0?P7Q1gH0?H0?Q1iPuQ0C-0U1R`,m@,iuQ1jPuQ1kQ1l9eu`5quQ1jPuQ1n=eu@R`Q1jQ1o,m@,iu9qu`R`CZCZCZQ1pP2bAbBbCX11X31X6x1:36%>7Q06Q1S,:0'4R0[\J[^11^31^6xQ0Kb7%>yQ1S,:y'4ebRbQbPbMbLbKb8b9b:b;b<b=bJUUViX11X31X6xP0\E\J\i^11^31^6xRxePxP31;hHPHQ04Q1UPFP=O6b7b8b9b:b;b<bNbObDb=b0+0W+0TE?Q10Q0iQ0iQ1?Q0MQ1HQ0xPvPtQ1:Q0hQ0DQ0EQ1<Q1DQ0?Q1KQ1NQ1QQ1RQ14Q0>Q1GQ1dQ1e20k16Q1iPuAeuL@Q1m5quQ1jP`CZQ1pP2bAbBbCX11Q0L,;3:0Nh3Q1TQ1S,:6'4[^11P3PHPFO2b7b8b9b:b;b<bNbObDb=b0+0W+0TE?N:0FK1CQ0d$1_P3E?bdWTWfP6P3O2n2001000010121000000W0WSP6P3O2n2001000010121000000b0WmWcP6P3O2n2001000010121000000W0WZW[P6P3O2n2001000010121000000W0P6P3O2n2001000010121000000W0WlP6P3O2n2001000010121000000W0WkP6P3O2n2001000010121000000W0WjP6P3O2n2001000010121000000W0WTP6P3O2n2001000010121000000W0WSP6P3O2n2001000010121000000b0W_WgWWWXWeWiWYWbW^W|WxW\XV1WyWvW]Z09BZ08BZ07BZ06BZ0;BXuBXtBXsBXrBXqBXpBXoBXnBZ05BZ04BX~BY0:WhW{W}Xw1o"). Qed.
End B2.
End CANSEC1.
