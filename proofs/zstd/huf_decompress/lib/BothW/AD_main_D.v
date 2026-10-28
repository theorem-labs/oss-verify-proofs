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
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy AF_atexit ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3 AD_main_B4 AD_main_C.
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
Ltac2 kr_t_AD_main_D () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdK5ARocqVerifyHarness?AgentSubmission4Spec5ProgA6AAlloc01C5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_D;implMA_retbI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface@astk_shadow_presC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface7rin_ivsC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit?magree_of_dpostC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface9adrv_presI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface9atrun_ivsC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit4dcliC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3ALOC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7AMFRAMEC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ASTATC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0K47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx6ASTATXc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_D;adrv_magreeC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6moduloc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_D6ABASE2C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx:stack_dcliC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit:atx_stateAC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeI47Corelib4Init9Datatypes4prod00C47Corelib4Init5Logic7and_indC46Stdlib9micromega;ZifyClasses6eq_iffK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=gdescs_magreeC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx:ci_drv_sh'C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic6or_indC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx6ci_drvK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor6gdescsC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC56Stdlib6ZArith6BinInt1Z4landI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor8AGLOBALSC5ARocqVerifyHarness?AgentSubmission5BothW5AExit6RSTDINC5ARocqVerifyHarness?AgentSubmission5BothW5AExit;stdin_cellsI47Corelib4Init9Datatypes4bool00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_rangesC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface;ASTAGE2_RETC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor?AGLOBALS_lengthC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ABASEC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stdout_fileC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun_cells0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A4RNGSC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6aps_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps7afree_MK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit8aps_restC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:dfree_postC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7rng_subC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface7dfree_MC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_hb_idsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6hb_idsI46Stdlib5Lists4List5NoDup00C5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit?lb_remove_headAc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_D:dpost_adrvC5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit?atx_state_addrAC5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit@atx_stateA_agreec5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_DAABASE2_after_adrvC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A9RNGS_monoC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kitBstdout_file_magreeC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit>aps_so_of_restC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_ifaceBstderr_wfile0_fileC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx<amain_returnC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_C6RQEXITC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase9lb_removeC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RFMTC5ARocqVerifyHarness?AgentSubmission4Spec6Driver9COUNT_MAXC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase;AFREE_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8AFREE_PCC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_C4RUN0C5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_C3HDRC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B13BUFC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A5AARGVC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps;aptr_addr_MC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim4znthC5ARocqVerifyHarness?AgentSubmission4Spec6Driver4le16C47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure<rw_cells_appC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission3Lib7SysStepArw_cells_bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit@drv_got_of_aheapC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4runAC56Stdlib6ZArith6BinInt1Z7testbitC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA<alloc_countAC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_ifaceAatarget_run_postAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgreeDzbytes_map_unsigned'C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgreeBmap_unsigned_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib5Lists4List:length_mapC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_sp0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles9ssp_cellsC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z7mod_addC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_rC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_ifaceHatarget_alloc_count_specC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_D;free_returnC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B3AimplMA_bind_assocC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_C9main_tailC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initC5ARocqVerifyHarness?AgentSubmission4Spec6Driver9MAX_INPUTC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<AGOT_STDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8ASTDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>AGOT_FUZZ_INITC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface6ASTAGEC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:AFUZZ_INITC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_ifaceAATARGET_RUN_STACKK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".   
Import ListNotations.
Set Keyed Unification.   
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
Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_D ()) ["CANSEC1"] "h01Hh11Qh23RNGh31Xh41Yh51ah61fh72msh81sp;2p;6p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p710g001]R0p4p710p8p1002Np4p710p1002kp4p710R2p8p200R3p1003Gp4p7210p8P3p1004;R4p4p7210p8p201R5P0p4p7210p8P5g0050R6p4p710p8P5P4p4p73110p8p1005kp4p70P2p8p1006bp4p7210P1p8P0j21TP6j60Tg007NR6f2R0f3R1g008GR2/11[f4R4g009CR7p-0[\6\2[f6f5P1P4O1P0f1f0R0E0P0W0X77W1X82W6W5W2X45X33o"). Qed.


Section D.
  
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
  Notation BUF' := (BUF AI L).
  Notation RUN0' := (RUN0 AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  
  Hypothesis HUL : HU L.
  Hypothesis TRUN : atarget_run_stmtA AI rng_fs.

  
  Notation GST8 pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  
  Definition ABASE2 (mm : amem) : Prop :=
    stk bsegs mm LO (usp + -128) /\ mem_inv bsegs mm /\ AMFRAME' mm /\ ASTAT TID mm /\ stderr_wfile0 mm
    /\ rw_cells bsegs mm ssp_guard [C8 canary].

  
  Lemma dpost_adrv : forall LB SP m m', aheap_pres CI LB SP m m' -> astk_shadow_pres SP m m' -> adrv_pres AI LB SP m m'.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_D ()) ["CANSEC1"; "D"] "h02HPh12HSh22Hah32Hch42LBh52SPh62_Hh71ah81mh92m'p;1p;2p;6p;4p;5p;;p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p710p1001]R0p4p710p8p1002Np4p710p1002kp4p710R2p8p100:JR3p6051002R4p1003Gp4p7210p8P4p1004;R4p4p7210p8P3p60521001R3P0p4p7210p8P3p10050p4p710p8P3P4p4p73110p8p1005kp4p70P2p8p1006bp4p7210P1p8g00;Jj1DTg00;jj10Tg00<Oj12Tg00<mj14Tg00=Pj1CTg00>2j2;Tg00>nj6:Tg00@1j49Tg00A;j25Tg00AWj11Tg00B5j28Tg00BRj26Tg00Bnj23Tg00CIj5BTg00DNj1ATg00EDj17Tg00F<j2<Tg00FVj2=Tg00GVj1>Tg00Gol;?Tg00I0j6@Tg00J2#Dg00JkR1g00KI#0R2#0#0R4#0#0#0R3#2#4%24#4#C[R4p,2rcR0p,2AIR5,;0R6f3R7f2R8f1R9f0R:E:P0P7P8P9C9g00Kn/5:%12%13'8,6:'3P0P6f7R:f6R3P9DB%A0#7/59%73,69'3'<g00LL/=8#>P0P6f9f8P:P3f5R3f4R:P7P8P9M;?W6W3W2X71P0P5P3P:P7P8E@eW1W0X94W8W5W4o"). Qed.

  Lemma adrv_magree : forall LB SP m m', adrv_pres AI LB SP m m' ->
    magree bsegs (fun a => dcli CI LB SP a /\ ~ rin_ivs atrun_ivs a) m m'.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_D ()) ["CANSEC1"; "D"] "h01ah11Hh22H0h32Hah42Hch52Hnh62LBh72SPh81mh92m'p;1p;6p;2p;5p;3p;4p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p710p1001]R0p4p710p8p1002Np4p710p1002kp4p710R2p8p100:JR3p6051002R4p1003Gp4p7210p8P4p1004;R4p4p7210p8P3p60521001R3P0p4p7210p8P3p10050p4p710p8P3P4p4p73110p8p1005kp4p70P2p8p1006bp4p7210P1p8g00;Jj1CTg00;jj10Tg00<Oj17Tg00<mj16Tg00=Pj1BTg00I0j6ATg00A;j2>Tg00AWj18Tg00B5j2=Tg00BRj2<Tg00BnR1j23Tg00>2j2;Tg00MNj52Tg00FVj24Tg00GVj11Tg00NDj1:Tg00O3j35Tg00OMj39Tg00PJj1@Tg00Plj4?Tg00J2#Cg00JkR2g00KI#0R4#0#0R3#0#0#0R0#7#6%73#6R3#BR5[R6p,2rcR7p,2AIR8f3R9f2R:f1R;f0R<EAg00Kn/><%84%80'=,<<'3P71;78R8f6R0f5R4P;D2g00LLR=/4;#1'3P1P7P8f7R1P0P:D214=:#1P4%:9R9O1P0P9O1555g00QgR>?909%@3R3555#1f4R9#:99>0=553#1['3P<P7P8f9f8P9D214=4#1P1P0P4P;P<O4W5W4P;P<O2n2001000000120000000W2W3X02P>P7P8P4P9P<D214=<#1'3X02P:P;C?eW1X96W8W7W6o"). Qed.

  Local Ltac not_ivs := unfold atrun_ivs, rin_ivs, AINIT_FLAG; cbn [fst snd]; lia.

  
  Lemma ABASE2_after_adrv : forall LB m m',
    adrv_pres AI LB (usp + -128) m m' -> stk bsegs m' LO (usp + -128) -> mem_inv bsegs m' ->
    AMFRAME' m -> ASTAT TID m -> stderr_wfile0 m -> rw_cells bsegs m ssp_guard [C8 canary] ->
    ASTATX m' ->
    ABASE2 m'.
Proof.
intros LB m m' HPR ST' MI' FR AS SE GU AXX.
pose proof (adrv_magree _ _ _ _ HPR) as AG.
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
split; [exact ST'|]. split; [exact MI'|].
split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR|]. intros a Ha. cbn in Ha.
split; [apply (stack_dcli AI usp); lia| not_ivs]. }
split. {
destruct AS as (A1 & A2 & (cdt & thr & sec & tm1 & A3) & _ & A5 & [dso A6] & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & GD & [j1 SH1] & [j2 SH2]).
Ltac tryr2 lo hi := exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
Ltac dpick k := let L := eval vm_compute in drv_img_ranges in
  let rec go L := lazymatch L with
    | cons (?lo, ?hi) ?t => first [ k lo hi | go t ]
    | nil => fail
  end in go L.
Ltac trc AG H := eapply rw_cells_magree; [exact AG| exact H| intros a Ha; cbn in Ha; unfold AExit.RSTDIN in Ha; split; [left; right; left; dpick ltac:(fun lo hi => tryr2 lo hi)| not_ivs]].
unfold ASTAT.
split; [trc AG A1|]. split; [trc AG A2|].
split; [exists cdt, thr, sec, tm1; trc AG A3|].
split; [exact AXX|].
split; [trc AG A5|]. split; [exists dso; trc AG A6|].
split; [trc AG A7|]. split; [trc AG A8|]. split; [trc AG A9|].
split; [trc AG A10|]. split; [trc AG A11|].
split; [trc AG A12|]. split; [trc AG A13|]. split; [trc AG A14|].
split. { eapply gdescs_magree; [exact AG| | exact GD]. intros a Ha. rewrite F_module_dtor.AGLOBALS_length in Ha. split; [| not_ivs].
left. right; left. dpick ltac:(fun lo hi => tryr2 lo hi). }
split. { exists j1. eapply rw_cells_magree; [exact AG| exact SH1|]. intros a Ha. cbn in Ha. split; [| rewrite ?shad_div in Ha; unfold ASHOFF in Ha; not_ivs].
dpick ltac:(fun lo hi => apply (ci_drv_sh' AI usp DRV_CI LB lo hi); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]). }
exists j2. eapply rw_cells_magree; [exact AG| exact SH2|]. intros a Ha. cbn in Ha. split; [| rewrite ?shad_div in Ha; unfold ASHOFF in Ha; not_ivs].
dpick ltac:(fun lo hi => apply (ci_drv_sh' AI usp DRV_CI LB lo hi); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]). }
split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. cbn in Ha.
split; [apply (ci_drv AI usp DRV_CI LB RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| lia] | not_ivs]. }
eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. unfold ssp_guard in Ha. cbn in Ha.
split; [dpick ltac:(fun lo hi => apply (ci_drv AI usp DRV_CI LB lo hi); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard; lia]) | not_ivs].
Qed.

  Lemma ABASE2_of_ABASE : forall so mm, ABASE' so mm -> ABASE2 mm.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_D ()) ["CANSEC1"; "D"] "h04errvh11Hh22ASh32FRh42GUh52MIh62SEh72STh82_Hh92mmh:2sop;1p;?p;2p;4p;;p;3p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p710p1001]R0p4p710p8p1002Np4p710p1002kp4p710R2p8p100:JR3p6051002R4p1003Gp4p7210p8P4p1004;R4p4p7210p8P3p60521001R3P0p4p7210p8P3p10050p4p710p8P3P4p4p73110p8p1005kp4p70P2p8p1006bp4p7210P1p8g00;jj12Tg00<Oj1OTg00<mj1FTg00=Pj1PTg01iHl?WTg00Snj1TTg00S3j1GTg00SQj2ETg00Tcj4@Tg00UUj2;Tg00VIl;8Tg00WBj25Tg00X9j17Tg00b4j1VTg00Y=j1UTg01Goj3MTg00bij2STg01F1j2RTg00\hj1HTg014Zj1QTg00]mj19Tg00BnR1j20Tg014?j4<Tg00Y]j4>Tg01j?j2:Tg016Dj2BTg01k:j2KTg01l;j1ATg01m@j1LTg01nFj1NTg00QgR2f2R4f1R3f0R0C>p=1f7R5f6R6':f5R7g01oIR8':f4R9g020FR:':f3R;/B41K30'0'0'0'0p=3P2P7g01aFR<P9C>%A;%L4%N3/00'0'0'0p=41030,04p=6%73/00p==P2P3P<P0C>p=?1B;41K30'0p=D1:481:3:/00'0p=C%N;1:43/00'0p=I%A4%L3/00'0p=Jg021Cg00KI#2R:#2#2R8#2#2#2R<#OR=#FR>%O8#F#P[p,3uspR8p,3TIDR?p,2S0R@p,2S1RAp,2S2RBp,2S3RCp,2S4RDp,2S5REp,2S6RFp,2S7RGp,2J8RHp,4RSTKRIp,6canaryRJP3P0M?WP1P2P3%T8RK%2<#G,E8R<C@1;23P8P@PAPBPCPDPEPFPGPHP3M;815?3%73P3g01VZRL%VJ%ULRJ3MRMP3P3P3P3PIP3P3P>g022>,S=,R=%H:#2#2#H#2#2#G'ER:%Q0=MLJRJ514X0>P3P4G3E43636%94P0P2P;PKP<C@1;29P8P@PAPBPCPDPEPFPGPHP9M;815?9%79P9PMP9P9P9P9PIP9P9P>A17:JX0>P9P7G3E43636P11;27P8P@PAPBPCPDPEPFPGPHP7M;815?7P7PMP7P7P7P7PIP7P7P>A16:JX0>P7P6G3E4,=736%96P01;25P8P@PAPBPCPDPEPFPGPHf8R5M;815?5P5PMP5P5P5P5PIP5P5P>f9R6?1:JX0>P5P6G3E4,=536P1P8P@PAPBPCPDPEPFPGPHP6M;815?6%76P6PMP6P6P6P6PIP6P6P>f:R5?1:JX0>P6P5G3E436%95P0P8P@PAPBPCPDPEPFPGPHf;M;8f<R5,5?%75P5PMP5P5P5P5PIP5P5P>f=R9?1:JX0>P5P9G3E436P115?9P9PMP9P9P9P9PIP9P9P>f>R5?1:JX0>P9P5G3E4,=9%95P0f?,5?f@R5P5PMP5P5P5P5PIP5P5P>fAR;?1:JX0>P5P;G3E4'=P1%7;P;PMP;P;P;P;PIP;P;P>fBR5?1:JX0>P;P5G3E4%95P0fC#7fDR5PMP5P5P5P5PIP5P5P>fER4?1:JX0>P5P4G3E4P11?4MP4P4PIP>fFR1?1:JX0>P4P1CD9C44CI9J44%91P0fG/?MfHR1P1P1PIP>fIRI?1:JX0>P1PICD9C11CI7J1P2PIPKP<C@1;2IR2P8P@PAPBPCPDPEPFPGPHPIM;8RH15?IR?%7IRG1?IMRI'0RM'0RF'0RE'0P4P2PEP;PHPFP9P?PMP6PGPIP7P3C<C<C<C<C<W8W4P3P0O2n2001000000121000000W1W6P3P0O2n2001000000121000000W1W2P3P0O2n2001000000121000000W1W3P3P0O2n2001000000121000000W1W5P3P0O2n2001000000121000000W1W7P3P0O2n2001000000121000000W1W9W:o"). Qed.

  
  Lemma free_return : forall (code : Z) (s : APS) RNG (bufp : AsanCtrl.aptr) (A cap : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    0 <= code <= COUNT_MAX ->
    AHEAP AI L RNG (aps_m s) [HB bufp A cap] mm -> ABASE2 mm -> stdout_file mm (aps_so s) -> RNGS' RNG -> aps_ok L s ->
    implMA RNG (afree_M bufp ;;; mret code) s RQEXIT
      (GST8 0x7fce0 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until mm. intros CR HP1 B2 SOF RG RK.
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH, COUNT_MAX in *.
pose proof B2 as (ST1 & MI1 & FR1 & AS1 & SE1 & GU1).
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
apply implMA_from_evtF. zstep. zstep. apply evtF_done.
eapply implMA_bind.
{
eapply (dfree_M AI DFREE L RNG) with (lo := LO) (p := bufp) (A := A) (n := cap); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
first [ exact HP1 | left; reflexivity | exact MI1 | exact ST1 | exact BOT | unfold AFREE_STACK; lia | exact UF_ff0 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | exact RK | idtac ].
all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
cbv beta. intros [] s2 RNG2 ms3 [SOE3 PO].
destruct PO as (LE2 & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
rewrite ?(unsigned_lit (usp + -128)) in ST3, HPR3, HSP3 by lia.
fix_ret. cbn [aps_m aset_m fst snd] in HEAP3.
pose proof (AI_hb_ids AI _ _ _ _ _ HP1) as ND.
rewrite (lb_remove_headA bufp A cap [] ND) in HPR3, HEAP3.
assert (BA3 : ABASE2 m3).
{ eapply (ABASE2_after_adrv []); [apply dpost_adrv; [exact HPR3| exact HSP3]| exact ST3| exact MI3| exact FR1| exact AS1| exact SE1| exact GU1|].
destruct AS1 as (_ & _ & _ & [reg AXr] & _). exists reg.
eapply atx_stateA_agree; [eapply magree_of_dpost; [exact HPR3| exact HSP3]| | exact AXr].
intros a Ha. unfold atx_state_addrA, atx_addrA in Ha.
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
dpick ltac:(fun lo hi => apply (ci_drv AI usp DRV_CI _ lo hi); [unfold drv_img_ranges; cbn; tauto| lia]). }
pose proof BA3 as (_ & _ & FR3 & AS3 & SE3 & GU3).
assert (RG2' : RNGS' RNG2) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE2| exact RG]).
pose proof RG2' as (RGstk2 & _ & RGimg2 & RGimsh2 & _ & _ & _ & _ & RG02 & _).
apply implMA_ret. unfold RQEXIT.
eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 USP16 USPLO USPHI canary);
first [exact FR3 | exact ST3 | exact AS3 | exact HEAP3 | exact MI3 | exact HT | exact RGimg2 | exact RGimsh2 | exact RG02 | exact GU3 | idtac].
- rewrite (aps_so_of_rest _ _ SOE3). eapply stdout_file_magree; [eapply magree_of_dpost; [exact HPR3| exact HSP3]| | exact SOF].
intros a [Ha|Ha].
+ apply (ci_drv AI usp DRV_CI _ RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
+ dpick ltac:(fun lo hi => apply (ci_drv AI usp DRV_CI _ lo hi); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia]).
- apply stderr_wfile0_file. exact SE3.
- eapply rng_sub'; [exact RGstk2| lia].
Qed.

  
  Lemma phaseDE : forall bufp A cap DATA cw Lc cfg sc s RNG ms,
    RUN0' bufp A cap DATA cw Lc cfg sc s RNG ms ->
    implMA RNG (main_tail bufp cw cfg (skipn (Z.to_nat (6 + Lc)) (map bv_unsigned DATA))) s RQEXIT ms.
Proof.
intros bufp A cap DATA cw Lc cfg sc s RNG ms R0.
destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & junk
& -> & HD & BU & BA & ARG & RG & FRM).
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR.
pose proof BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). unfold MAX_INPUT in CAPR.
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
destruct HD as (LEN6 & LENC & CAPM & _ & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (_ & _ & _ & GSSP).
unfold main_tail. rewrite ECFG.
apply implMA_from_evtF. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
eapply implMA_bind.
{ eapply (TRUN L RNG RSTK) with (lo := LO) (p := bufp) (cap := cap) (LB := [HB bufp A cap]) (canary := canary);
rewrite ?(unsigned_lit (usp + -128)) by lia;
first [ exact P0h | left; reflexivity | exact TR | exact HI | exact (proj1 (proj2 (proj2 AS))) | exact ST | exact BOT | exact MI | exact FRM | exact RCS | exact ROD | exact RCB
| exact HUL | exact UM_14c | exact UF_1a0 | exact UM0 | exact UF0 | exact RGtop | exact RGimg | exact RGimsh | exact RGfs
| exact RRS | exact RRF | exact RRB | reflexivity | idtac ].
all: try (unfold zlength; rewrite ?length_map; unfold ATARGET_RUN_STACK, AHARNESS_STACK; lia).
all: first [ intros b [<-|[]]; do 3 eexists; reflexivity
| rewrite zbytes_map_unsigned'; exact BLKB
| apply map_unsigned_range
| rewrite SO0; exact SOF
| split; [exact GSSP| exact GU]
| clear -G5; Z.div_mod_to_equations; lia
| unfold zlength; rewrite length_map; f_equal; lia
| eapply rng_sub'; [exact RGstk| lia]
| exact RK
| atop_facts; lia ]. }
cbv beta. intros r s1 RNG1 ms1 [LE1 PO].
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1
& -> & RR & MI1 & FRM1 & ST1 & DP & HP1 & SOF1 & SSP1 & AX1 & RK1).
rewrite ?(unsigned_lit (usp + -128)) in ST1, DP by lia.
fix_ret.
assert (BA2 : ABASE2 m1).
{ eapply (ABASE2_after_adrv [HB bufp A cap]); [exact DP| exact ST1| exact MI1| unfold AMFRAME; exact FR| exact AS| exact SE| exact GU| exists true; exact AX1]. }
assert (RG1' : RNGS' RNG1) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE1| exact RG]).
clear DP.
rewrite TB.
destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
-
replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
apply implMA_from_evtF. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
zstep. apply evtF_done.
apply implMA_bind_assoc. eapply implMA_bind; [apply atarget_alloc_count_spec|].
cbv beta. intros n s2 RNG2 ms2 (-> & -> & -> & ->). apply implMA_retb.
fix_ret.
unfold COUNT_MAX. change (if 0 <? 251 then 0 else 251) with 0.
apply implMA_from_evtF. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
apply evtF_done.
eapply free_return; [unfold COUNT_MAX; lia| exact HP1| exact BA2| exact SOF1| exact RG1'| exact RK1].
-
replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
apply implMA_retb.
apply implMA_from_evtF. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
zstep. zstep. apply evtF_done.
eapply free_return; [unfold COUNT_MAX; lia| exact HP1| exact BA2| exact SOF1| exact RG1'| exact RK1].
Qed.
End D.
End CANSEC1.
