(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A.
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
Ltac2 kr_t_AD_main_B1 () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC5ARocqVerifyHarness?AgentSubmission3Lib5Image:ro_bytes_bI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B16AS_OOMc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B15s_oomc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B18AS_SHORTc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B17s_shortc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B17AS_OVERc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B16s_overC46Stdlib7Strings6StringDlist_ascii_of_stringI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib7Strings5Ascii:N_of_asciiC56Stdlib6ZArith6BinInt1Z4of_NI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib4Init9Datatypes4list01C46Stdlib7Strings5Ascii?N_ascii_boundedK47Corelib7Numbers7BinNums1N02C56Stdlib6NArith6BinNat1N2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib5Lists7ListDef6Forall02K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio3strC47Corelib5Lists7ListDef3mapC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I46Stdlib7Strings5Ascii5ascii00I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib7Strings6String6string00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K5ARocqVerifyHarness?AgentSubmission4Spec5ProgA6AAlloc01I5ARocqVerifyHarness?AgentSubmission4Spec6Driver7IOStyle00C5ARocqVerifyHarness?AgentSubmission4Spec6Driver>read_loop_bodyI5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result00C5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mloopC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrI47Corelib4Init9Datatypes3sum00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK47Corelib4Init9Datatypes3nat02I5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I5ARocqVerifyHarness?AgentSubmission4Spec6Driver5rd_st00C5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStI47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B1<rd_grow_partC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6rd_capC5ARocqVerifyHarness?AgentSubmission4Spec6Driver:rd_contentC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node04C5ARocqVerifyHarness?AgentSubmission3Lib6Decode8dec_readC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4msysC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3ioAK5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg03C5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_diagK5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result01K47Corelib4Init9Datatypes3sum02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3eqbC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6rd_bufK5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result02C5ARocqVerifyHarness?AgentSubmission4Spec6Driver<u8s_of_bytesC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission4Spec6Driver5rd_st01K47Corelib4Init9Datatypes3sum01C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanI5ARocqVerifyHarness?AgentSubmission3Lib6Decode8read_ans00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface6ASTAGEK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3ALOK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW7AD_diag:adiag_argsC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ABASEC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A4RNGSC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8aat_exitC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7AMFRAMEC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ASTATK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C45stdpp9bitvector;definitions;bv_unsignedK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun_cells0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit@drv_got_of_aheapK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission5BothW7AD_diagBafprintf_diag_postC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_ifaceCstderr_wfile0_wfileC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW7AD_diagCafprintf_diag_proofC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx@implMA_of_implAMC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC47Corelib4Init5Logic3notC4ELinuxProcessSemantics5Riscv3Sem7reg_getC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<stderr_wfileC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles9ssp_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3WOKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A:after_diagC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC56Stdlib6ZArith6BinInt1Z3mulK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stdout_fileC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAstderr_wfile_fileC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx;aexit2_tailC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6s_diagC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RFMTC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<AGOT_STDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8ASTDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>AGOT_FUZZ_INITC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspI5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:AFUZZ_INITC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission5BothW7AD_diag>AFPRINTF_DEPTHC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_ranges".   
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
Definition AS_OOM : Z := 0x14794.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition AS_SHORT : Z := 0x1f80e.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition AS_OVER : Z := 0x15847.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b bsegs AS_OOM (zb s_oom) = true.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p;2p;1p;3p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p73110p1001Zp4p7210p8p1002Kp4p7210P1p8g0037j23Tg003Qj12Tg004Lj30Tg005Ej31Tg005_R1g006?R0'3g006_g007Tg008P#230=110do"). Qed.
Lemma s_short_ro : ro_bytes_b bsegs AS_SHORT (zb s_short) = true.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p;2p;1p;3g0037j23Tg003Qj12Tg004Lj30Tg005Ej31Tg005_R0g006?R1'3g006_g009Kg00:I#230=101do"). Qed.
Lemma s_over_ro : ro_bytes_b bsegs AS_OVER (zb s_over) = true.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p;2p;1p;3g0037j23Tg003Qj12Tg004Lj30Tg005Ej31Tg005_R0g006?R1'3g006_g00;Fg00<C#230=101do"). Qed.
Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "h01lh14__x1h21ah31Hh42H0h52IHh67__arithh74__ffh88__varmaph95__with:1ch;4cstrh<1sp;1p;2p;3p;4p;7p;6p;5p;<p;8g00=?j1ZTg00=lj1?Tg00>Lj26Tg00>hj10Tg00?Mj1YTg00?kR0j25Tg00@Gj2:Tg00@bj11Tg00ADR1j12Tg00Abj33Tg00BCj2ATg00Bdj1>Tg00CDj1XTg00Ckj1TTg00DIR2j2<Tg0037j27Tg00Dej4LTg00ELj1JTg00Eoj2ITg00FMj1HTg00Fkj1GTg00GVj29Tg00H9j2FTg00H\j4=Tg00IGj1ETg00Iij7DTg00JMj2KTg00Joj2CTg005Ej3BTg00K[j3NTg00L:j4OTg00Llj6PTg00MMj3QTg00Mmj5@Tg00NOj1RTg00OBj4STg00O^l<WTg00PCj7VTg00Pgj8UTg00QKR3g00QjR4f1R5f0R6CSp=4g00RHP4P2P1P0g00Rff5f4R0f3R1f2R2P5P6M<Wp=MP5g00SFR7g00SeR8P8g00TER9P6g00TeFVp=8P1P7P8P8P9P2P5P6GUp=;g00UE%Z6%?3R:P3g00UfR;/66R<g00VDR=#0#0#0#0#0#0#0#0R>#YR?,56':X:4R@%16#2X23RA/46534RBX0:1A4@%>3,4A934@eP4P@%12RC#214A5%X2%T>R>,<C%11R1/<>%21RC/5?RDP1PC174CP>P?174?EMP6CLPD%10R0#J%20,6;g00ViR0#>%?01I45%H4%G4R0P4194;g00WU1F4=R=C=,80RD%E8R>P0P4P=g00X<194?C=,80R=P>P0P7P8P8P9PDP=FDC;C;1K09P6P2g005_R0g006?R9'71C62=B09dAN4;5COb7b8b9X14155?16;2152?':[\<^14P6f6#1#2P5P2O3b6b;b4b3P6EPAQ325,4A934@eX5BX0:X23P6D@b0%R6934@eW<o"). Qed.


Lemma implMA_loop_S : forall {X R} RNG fuel (body : X -> @Monad.M APS (X + R)) x s (Q : R -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG (body x) s (fun r s' RNG' ms' => match r with
                                        | inl x' => implMA RNG' (mloop fuel body x') s' Q ms'
                                        | inr v => evtF bsegs RNG' (Q v s' RNG') ms'
                                        end) ms ->
  implMA RNG (mloop (S fuel) body x) s Q ms.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p'0h04RNG'h13ms'h22s'h31ri001rh42H'h51ah61si011sh71Hh81Qh91Rh:3RNGh;1Xh<4bodyh=4fuelh>2msh?1vi021vh@1xi031xhA2x'i042x'p;2p;6p;4p;3p;7p;;p;1p100Xcp4p710R0g001ZR1p4p710R2p8P0p100Y[p4p710R3p8P0p100ZUp4p710p8P3P2p8p100[Tp4p710R2P1p4p7210R3p8P2g00\PR0p4p7210R4p8P2p1000eR5p4p7210R6p8P2P5p4p73110p8p200R5P3p8P5g00]DR7p4p710R8p8P5g00^?R9p4p7210p8P5g00_4R:p4p710R;p8p201R<P3p8P<P4p8P<P8p8P<g00`4R8p4p710p8P<P;p8P<P9p4p73110p8P<P:p4p7210p8p100a3p4p70R;P2p8P;P6p8g00ajR6j24TP1j23TP7j60Tg00bIj42TP0j35TP8j79TP:l;8Tg00c=j17TP9j66Tg00c\R9f4R:f3R8f2R0f1R7f0R1E6p=1g00dXR;g00eQ14:8,39\8f5R2g00f0R4p-0R3[\;\9[f8R=f7R>'4R?f6R@P:P8O1P0P6f<RAf;RBP3P8PAP0f=RCPAf:RDf9REP1D1P8P@P7E0g006_RFP0P@P1P8P0O3P7C2n200110000021010410102X14X0;X29X3?P1E014E=R?P=P>P2P:O1P6PDPE139DP1PBPDP=P>P1D1A59D1n200110100021010410100X6?P8P6PCPAP3P8PCP0f>RGPCPBPDP1D1P8P>P7E0PFP0P>P1P8P0O3P7C2n200110000021010410102X14X0;X29X3?P0P7P1P6PDPEP6PGPCP3P8PGP0f?RHPGPAPBP1D1RIP8P=P7E0PFP0P=P1P8P0O3P7C2n200110000021010410102PGP0P6PHPG139HP:f@RJPHPCPAP1D1A59H1n200110100021010410100P8P=P7E0[^14^0;^29P1PGP7PHPGPAPBP8D1P0P=P1E0P1W4X14X0;X29XABP1O1PFP7P=P8P0P7O3P1C2PHP0P:P8PEP7P1F9W4X14X0;X29X?DP1O1n200110100021010310100X5?14CAP6fARAPJP3P8PAP0fBPAPHPGP1D1P8PBP7E0PFP0PBP1P8P0O3P7C2n200110000021010410102X14X0;X29W3P8P0P7P1O4PCP0P6PGPC139GP:PIA59G1n200110100021010410100P8P>P7E0[^14^0;^29^5?eM;8P=P>PEP=%7@P2P:D1P8P0P7E0eW7X>4W8X69X@:W<W=W:X9<X;5o"). Qed.
Lemma implMA_get_bind : forall {A} RNG (f : APS -> @Monad.M APS A) s Q ms,
  implMA RNG (f s) s Q ms -> implMA RNG (mbind mget f) s Q ms.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "h01Ah11Hh21Qh33RNGh41fh52msh61sp;2p;6p200R0g001ZR1p4p7210p8P0g00]DR2p4p710p8P0p1000ep4p73110p8P1j21TP2j60Tg00dXR2g00c\R1f2R3,11[f3R4g00f0R5p-0[\2\1[f5f4P4P3O1P3f1f0R3E0P3W1X55W2X61W4W3X00o"). Qed.
Lemma implMA_mret_bind : forall {A B} RNG (a : A) (f : A -> @Monad.M APS B) s Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (mbind (mret a) f) s Q ms.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "h01Ah11Bh21Hh31Qh43RNGh51ah61fh72msh81sp;2p;6p200R0p100\Pp4p7210p8P0p1000eR1p4p7210p8p201R2g001ZR3p4p7210p8P2g00]DR4p4p710p8P2P1p4p73110p8P3j21TP4j60Tg00dXR4f2R3f3R1g00c\R5/11[f4R6g00f0R7p-0[\4\5[f6f5P1P6O1P3f1f0R3E0P3W2X77W3X85W6W5W4X12X00o"). Qed.


Section B.
  
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
  
  Variable J8 : list byte.
  Notation ABASE' := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK canary).
  Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x7fb40] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x7fb94] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x7fbb8] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x7fce8] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x7fe20] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x7feb4] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  

  Notation ioS := (ioA AAllocAsan).

  
  Definition BUF (mm : amem) (s : APS) (RNG : footprint) (bufp : AsanCtrl.aptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    AHEAP AI L RNG (aps_m s) [HB bufp A cap] mm /\ aps_so s = stdout_init /\ aps_ok L s /\ A = aptr_addr_M s bufp
    /\ rw_cells bsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ ablock_range A cap
    /\ rng RNG A cap /\ rng RNG (shad A) (shlen (cap + 7)).

  
  Definition STAGE (mm : amem) (sj : list byte) : Prop := rw_cells bsegs mm ASTAGE [CB ASTAGE_LEN sj].

  
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).

  
  Definition RDINV (fd : Z) (st : rd_st) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A : Z) (DATA junk : list byte) (sj : list byte) (pc : Z),
      ms = RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ ((pc = 0x7fb74 /\ x9 = Z_to_bv 64 A) \/ (pc = 0x7fb54 /\ rd_content st = []))
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s RNG (rd_buf st) A (rd_cap st) DATA junk /\ STAGE mm sj
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  
  Definition RDBRK (fd : Z) (bufp : AsanCtrl.aptr) (content : list Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A cap : Z) (DATA junk : list byte),
      ms = RST 0x7fbe0 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  Definition POSTBODY (fd : Z) (r : rd_st + rd_result) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDINV fd st' s RNG ms
    | inr RdExit => aat_exit 2 s RNG ms
    | inr (RdDone b c) => RDBRK fd b c s RNG ms
    end.

  
  Definition rd_read_part (fd : Z) (path : list Z) (st1 : rd_st (ptr:=AsanCtrl.aptr)) : @Monad.M APS (rd_st + rd_result (ptr:=AsanCtrl.aptr)) :=
    let len := zlength (rd_content st1) in
    let want0 := rd_cap st1 - len in
    let cnt := if 65536 <? want0 then 65536 else want0 in
    a <- msys (NRead fd ASTAGE cnt) (dec_read ASTAGE cnt) ;;
    match a with
    | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition rd_grow_part (st : rd_st) : @Monad.M APS (option rd_st) :=
    if zlength (rd_content st) =? rd_cap st then
      if MAX_INPUT <=? rd_cap st then io_diag ioS DTooBig ;;; mret None
      else
        nb <- amalloc_M (rd_cap st * 2) ;;
        match nb with
        | None => io_diag ioS DOom ;;; mret None
        | Some nb' => afree_M (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
        end
    else mret (Some st).

  Lemma read_loop_body_eq : forall fd path st,
    read_loop_body ioS amalloc_M afree_M ASTAGE fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd ASTAGE cnt) (dec_read ASTAGE cnt) ;;
         match a with
         | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"; "B"] "p'0h01ai001ah13cnth22fdh31gi011gh44pathh52sth65want0i022bsi031ei043st1p;1p;2p;3p;4p;5g00=lj1TTg00g7j1STg00goj1>Tg00[Tj1:Tg00ajj2RTg001Zj25Tg00hbR0j1?Tg00iDj1=Tg00jFj26Tg00k=j27Tg00l8j29Tg00m0j28Tg00>hj11Tg00?Mj1QTg00mMj2HTg00mjj3FTg00n_j2ETg00oWj4DTg010Kj1@Tg011>j1ATg0129j3BTg0131j1CTg013mj34Tg00\Pj32Tg000ej53Tg00Ckj1<Tg014Lj1GTg014oj2;Tg015Oj2ITg015oj2JTg016fj3KTg017bj1LTg018_j3MTg019<j4NTg01:4j3OTg0037j2PTf0R1#1#1p=0g00QjR2%T2g00a3R3#SR4g01:SR5#>R6%:3R7,R4R8'5R9g00c\R:%?4R;P8%=1P0P415:8P11631f2,73,92'8P2g005_R0P2g00VD#1#0R<#1#0#0#0#0#0#0#QR=/H1P=P1n0100000020000P2P6g01;TR=P8P6P=f6g01<NR>;F11E>1CDP=P9P1P6g00SeR>P8%@5f7#A5B6%C39447R59268V>D3P0P9%<<#G/;1g01=M'If4R<,J3R9173<R05K394479268P3P9163<%L19M20CN9O479268n0100000020000n0110000021010310102X0=D3b1b6A2:85n10110100021010400X3;D3'PW5W4W2o"). Qed.

  
  Lemma afprintf_exit : forall (d : diag_msg) {R} (K : @Monad.M APS R) (Q : R -> APS -> footprint -> machine_state -> Prop) (s : APS) (LB : list ablock) RNG
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    adiag_args RNG d mm a1v a2v LO (usp + -128) ->
    ABASE' stdout_init mm -> AHEAP AI L RNG (aps_m s) LB mm -> aps_so s = stdout_init -> frm0 fc -> RNGS' RNG ->
    (forall ms', aat_exit 2 s RNG ms' -> implMA RNG K s Q ms') ->
    implMA RNG (s_diag d ;;; K) s Q
      (GST 0x7fd4c x1 t0 t1 t2 x9 (Z_to_bv 64 RSTDERR) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until mm. intros DA BA AH SO FRM RG HK.
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF).
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (_ & _ & _ & GSSP).
apply implMA_from_evtF. zstep. apply evtF_done.
eapply implMA_bind.
{ apply implMA_of_implAM.
eapply (afprintf_diag_proof HSTRN RNG RSTK d) with (lo := LO); rewrite ?unsigned_lit by lia;
first [ apply stderr_wfile0_wfile; exact SE | reflexivity | exact DA | exact ST | exact MI | exact RCS | exact ROD | exact RGimg | exact RG0 | exact RRS | exact RRF
| split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ AH) | exact FRM | idtac ].
all: first [ unfold AFPRINTF_DEPTH; lia | unfold KHIGH; lia | eapply rng_sub'; [exact RGstk| lia] ]. }
cbv beta. intros [] st' RNG' ms' [-> PO].
destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
assert (HW2 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
destruct (after_diag usp TID S0 S1 S2 S3 S4 S5 S6 S7 RSTK canary USP16 USPLO USPHI _ _ _ _ _ BA HW2 MU2 WM2) as (FR2 & AS2 & SOF2).
apply implMA_from_evtF.
zstep.
eapply evtF_mono; [| intros ms'' H; exact (HK ms'' H)].
eapply (aexit2_tail AI usp TID USP16 USPLO USPHI canary);
first [exact ST2 | exact AS2 | exact MI2 | exact HT | exact RGimg | exact RGimsh | exact RG0 | idtac].
- eapply (AI_frame AI); [exact AH| exact MU2| exact WM2|].
pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _).
constructor; [| constructor; [| constructor]]; cbn [fst snd].
+ left. left. lia.
+ left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia].
- rewrite SO. exact SOF2.
- apply stderr_wfile_file. exact SEW.
- exact (proj2 SSP2).
- eapply rng_sub'; [exact RGstk| lia].
Qed.

  
  Lemma afwrite_exit : forall {R} (K : @Monad.M APS R) (Q : R -> APS -> footprint -> machine_state -> Prop) (s : APS) (LB : list ablock) RNG
      x1 t0 t1 t2 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    ABASE' stdout_init mm -> AHEAP AI L RNG (aps_m s) LB mm -> aps_so s = stdout_init -> RNGS' RNG ->
    (forall ms', aat_exit 2 s RNG ms' -> implMA RNG K s Q ms') ->
    implMA RNG (s_diag DOom ;;; K) s Q
      (GST 0x7fd70 x1 t0 t1 t2 x9 (Z_to_bv 64 AS_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros BA AH SO RG HK.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (_ & _ & _ & GSSP).
    apply implMA_from_evtF. zstep. apply evtF_done.
    cbn [s_diag]. change (concat pieces_oom) with s_oom.
    eapply implMA_bind.
    { apply implMA_of_implAM.
      eapply (afwrite_diag_proof RNG) with (lo := LO) (s := s_oom) (A := AS_OOM); rewrite ?unsigned_lit by (unfold AS_OOM; lia);
        first [ exact SE | reflexivity | exact ST | exact MI | exact ROD | exact RGimg | exact RRF
              | split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ AH) | idtac ].
      all: first [ apply fmt_bytes_at; [exact MI| exact s_oom_ro| unfold AS_OOM; lia| unfold AS_OOM, s_oom, zlength; cbn; lia]
                 | unfold s_oom; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
                 | unfold s_oom, zlength; cbn; lia
                 | unfold AS_OOM; lia
                 | replace (zlength s_oom) with 19 by reflexivity; unfold AS_OOM; lia
                 | unfold AFWRITE_DEPTH; lia | unfold KHIGH; lia
                 | eapply rng_sub'; [exact RGstk| lia] ]. }
    cbv beta. intros [] st' RNG' ms' [-> PO].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SEW & SSP2 & ->).
    rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
    assert (HW2 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
    destruct (after_diag usp TID S0 S1 S2 S3 S4 S5 S6 S7 RSTK canary USP16 USPLO USPHI _ _ _ _ _ BA HW2 MU2 WM2) as (FR2 & AS2 & SOF2).
    apply implMA_from_evtF.
    eapply evtF_mono; [| intros ms'' H; exact (HK ms'' H)].
    eapply (aexit2_tail AI usp TID USP16 USPLO USPHI canary);
      first [exact ST2 | exact AS2 | exact MI2 | exact HT | exact RGimg | exact RGimsh | exact RG0 | idtac].
    - eapply (AI_frame AI); [exact AH| exact MU2| exact WM2|].
      pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _).
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      + left. left. lia.
      + left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia].
    - rewrite SO. exact SOF2.
    - apply stderr_wfile0_file. exact SEW.
    - exact (proj2 SSP2).
    - eapply rng_sub'; [exact RGstk| lia].
  Qed.
End B.
End CANSEC1.
