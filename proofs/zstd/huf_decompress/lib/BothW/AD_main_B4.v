(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3.
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
Ltac2 kr_t_AD_main_B4 () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_diagC5ARocqVerifyHarness?AgentSubmission4Spec6Driver8read_allC46Stdlib5Lists4List9app_assocI5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result00C5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mloopC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B1=afprintf_exitC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6aps_okK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A5AARGVC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A4RNGSK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4ASTGI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3ioAC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3ALOC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7AMFRAMEC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun_cells0C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ASTATC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7astringC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=astring_factsC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit@drv_got_of_aheapK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01C47Corelib4Init5Logic9False_indC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgreeDzbytes_map_unsigned'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node03K5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg02K5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result01C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps9amalloc_MI5ARocqVerifyHarness?AgentSubmission4Spec6Driver5rd_st00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3mulC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree:u64ro_readK47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9open_postK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C46Stdlib5Lists4List:length_mapI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9open_specC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B2;implMA_msysC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls8open_retC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC47Corelib4Init3Nat3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3WOKC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls:open_errnoC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx;ABASE_munchC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A;AARGV_munchK5ARocqVerifyHarness?AgentSubmission3Lib6Decode4sret01C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_rC56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission5BothW7AD_diag:adiag_argsC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8aat_exitc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B45POSTBC56Stdlib6ZArith6BinInt1Z6leb_gtK5ARocqVerifyHarness?AgentSubmission3Lib6Decode4sret02C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit8aps_restC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<dmalloc_postC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7rng_subC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface9dmalloc_MC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface@astk_shadow_presK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B3>is_primary_bigC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A9RNGS_monoC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctxAABASE_after_dpostC5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_AAAARGV_after_dpostC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B15STAGEC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B3;dpost_stageC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B38POSTLOOPC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B13BUFC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit>aps_so_of_restC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;aps_ok_restC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure<rw_cells_appC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B2<rw_cells_CB0C47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission4Spec6Driver:rd_contentC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6rd_capC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6rd_bufC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B15RDINVC5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B37rd_loopC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps;aptr_addr_MK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node05C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls:close_postC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls:close_specC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9close_retC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls;close_errnoC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5BothW:AD_main_B45RDONEC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ABASEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stdout_fileK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC46Stdlib9micromega;ZifyClasses5mkappC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4msysC5ARocqVerifyHarness?AgentSubmission4Spec6Driver>read_loop_bodyK5ARocqVerifyHarness?AgentSubmission4Spec6Driver5rd_st01K5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result02K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr08K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl9aptr_addrC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RFMTI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<AGOT_STDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8ASTDERRPC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>AGOT_FUZZ_INITK47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission3Lib6Decode4sret00C5ARocqVerifyHarness?AgentSubmission3Lib6Decode8dec_openC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps7afree_MC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface6ASTAGEC5ARocqVerifyHarness?AgentSubmission3Lib6Decode9dec_closeK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>errno_addr_ATPI47Corelib4Init5Logic4True00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:ASTAGE_LENC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission4Spec6Driver9MAX_INPUTC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface;ASTAGE2_RETC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<ASTAGE_LEN_ZC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:AFUZZ_INITC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission4Spec6Driver9READ_FUELK5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg04K47Corelib7Numbers7BinNums1N01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_rangesK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats<FMT_CANTOPENI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;GLOBALS_TOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=AMALLOC_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase:AMALLOC_PCK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".   (* [comment removed for export] *)
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





(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section B4.
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
  Notation POSTLOOP' := (POSTLOOP AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation AP1' := (AP1 AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  Definition RDONE (bufp : AsanCtrl.aptr) (content : list Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A cap fd : Z) (DATA junk : list byte),
      ms = RST 0x7fbe8 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF' mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  Definition POSTB (r : rd_result) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    match r with
    | RdExit => aat_exit 2 s RNG ms
    | RdDone b c => RDONE b c s RNG ms
    end.

  (* [comment removed for export] *)
  Lemma amain_read_all : forall RNG st (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : amem),
    ABASE' stdout_init mm -> aps_so st = stdout_init -> aps_ok L st -> AHEAP AI L RNG (aps_m st) [] mm -> AARGV' mm -> RNGS' RNG ->
    bytes_at bsegs mm (usp + -8) (le8 (wz 0)) -> frm0 fc -> ASTG mm ->
    implMA RNG (read_all ioS amalloc_M afree_M ASTAGE arg1) st POSTB
      (MS (mkR (wz ASTAGE2_RET) (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) S1 (wz 2) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
               S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          bvmap_empty (wz 0x7fb1c) fc None mm (seg_rom bsegs)).
Proof.
intros until mm. intros BA SOI RK AH ARG RG U8 FRM [sj SJ].
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. atop_facts.
pose proof ASTAGE_LEN_Z as STGZ. unfold ASTAGE in SJ.
pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR. rewrite errno_addr_ATP in ERR.
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & RG1).
destruct (RG1 ltac:(lia)) as [RGa1 RRa1].
pose proof ARG as (B0 & A0 & A1f). destruct (A1f ltac:(lia)) as [B1 A1]. pose proof (astring_facts usp _ _ _ _ _ A1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
destruct A1 as (BY1 & HF1 & SL1 & LEN1 & LO1 & RC1 & IR1 & RLO1).
destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (_ & _ & _ & GSSP).
pose proof VARGV as (_ & _ & _ & NONUL & NOSL). pose proof (proj1 (Forall_forall _ _) NONUL _ (nth_In (n:=1%nat) argv [] ltac:(lia))) as A1NN. cbv beta in A1NN.
assert (A1NOSL : path_has_slash (nth 1 argv []) = false).
{ destruct argv as [|a0' [|a1' l']]; cbn in ARGC2; try lia. cbn [tl] in NOSL. inversion NOSL as [|? ? [X _]]. exact X. }
assert (STR1' : bytes_at bsegs mm P1 (nth 1 argv [] ++ [Z_to_bv 8 0])).
{ pose proof BY1 as X. unfold zb in X. change (fun z : Z => Z_to_bv 8 z) with (Z_to_bv 8) in X.
rewrite (zbytes_map_unsigned' (nth 1 argv [])) in X || idtac.
change (?p ++ Z_to_bv 8 0 :: slack1) with (p ++ ([Z_to_bv 8 0] ++ slack1)) in X. rewrite app_assoc in X. apply bytes_at_app in X. destruct X as [X _]. exact X. }
unfold read_all. apply implMA_from_evtF.
pose proof (u64ro_read bsegs mm (usp + 16) [wz P1] 0 (wz P1) (wz (usp + 16)) B1 eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep.
remember READ_FUEL as rf eqn:Erf. clear Erf.
apply evtF_done.
replace (map (Z_to_bv 8) arg1) with (nth 1 argv []) by (symmetry; apply zbytes_map_unsigned').
eapply implMA_bind.
{ eapply implMA_msys.
eapply (open_spec RNG) with (lo := LO) (errv := errv) (canary := canary);
rewrite ?(unsigned_lit (usp + -128)) by lia; rewrite ?(unsigned_lit P1) by lia; rewrite ?errno_addr_ATP; unfold ATP; rewrite ?unsigned_lit by lia;
first [ exact ST | exact STR1' | exact ERR | exact GSSP | exact GU | exact MI | reflexivity | exact A1NN | exact A1NOSL | exact RGimg | idtac ].
all: unfold got_ssp, ssp_guard, zlength in *; rewrite ?length_map in RGa1;
first [ lia | eapply rng_sub'; [exact RGstk| lia] | eapply rng_sub'; [exact RGimg| lia] | eapply rng_sub'; [exact RGa1| lia] ]. }
cbv beta. intros r s' RNG' ms' [-> [-> PO]].
destruct PO as (u0 & u1 & u2 & b1' & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
unfold ATP in MUc, ERR1. rewrite ?unsigned_lit in MUc by lia. rewrite ?(unsigned_lit (usp + -128)) in ST1 by lia. change (6214288 + -164) with 6214124 in MUc, ERR1.
transport_after_call bsegs mm m1 MUc WMc.
fix_ret.
assert (WOKW : Forall (WOK usp) [(usp + -128 - 112, usp + -128); (6214124, 6214124 + 4)]).
{ unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (AH1 : AHEAP AI L RNG (aps_m st) [] m1).
{ eapply (AI_frame AI); [exact AH| exact MUc| exact WMc|]. pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
constructor; [| constructor; [| constructor]]; cbn [fst snd].
- left. left. lia.
- left. right; left. exists (0x5ed1e8, 0x5ed1f0). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
assert (BA1 : ABASE' stdout_init m1).
{ eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| exact ST1| |].
- destruct SE as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
first [ exact Hc | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]; intros a' Ha'; cbn in Ha' |- *; lia ].
- eexists. rewrite errno_addr_ATP. exact ERR1. }
assert (ARG1m : AARGV' m1).
{ eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG]. }
clear MUc WMc WOKW.
pose proof BA1 as (ST1' & _ & FR1 & AS1 & SE1 & GU1 & TR1 & HI1 & ROD1 & RCS1 & RCB1 & RSG1 & _ & SOF1). unfold AMFRAME in FR1.
apply implMA_from_evtF.
destruct r as [e|fd]; cbn [open_ret open_errno] in *.
-
pose proof (drv_got_of_aheap AI _ _ _ _ _ AH1) as (GSE & PSE & _). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
cbn [io_diag ioA io_S].
eapply afprintf_exit with (LB := []) (d := DCannotOpen arg1);
lazymatch goal with
| |- adiag_args _ _ _ _ _ _ _ => idtac
| |- forall ms'', aat_exit _ _ _ ms'' -> _ => intros ms'' AE; apply implMA_ret; apply evtF_done; exact AE
| |- _ => eassumption
end.
destruct ARG1m as (_ & _ & A1f'). destruct (A1f' ltac:(lia)) as [_ A1']. destruct A1' as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
cbn [adiag_args]. split; [reflexivity|]. exists slack1, RA1.
rewrite ?unsigned_lit by lia. unfold GLOBALS_TOP, FmtFp.INT_MAX.
repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
-
zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. apply evtF_done.
eapply implMA_bind.
{ eapply (dmalloc_M AI DMALLOC L RNG) with (lo := LO); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
first [ exact AH1 | exact MI1 | exact ST1' | exact BOT | unfold AMALLOC_STACK; lia | unfold AREQMAX; lia | exact UM_e48 | exact UM0 | exact RGtop | exact RK | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
all: rewrite ?unsigned_lit by lia; unfold AMALLOC_PC; lia. }
cbv beta. intros r s1 RNG1 ms1 [SOE PO].
destruct PO as (LE1 & v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MI2 & ST2 & HPR & HSP & RR).
rewrite ?(unsigned_lit (usp + -128)) in ST2, HPR, HSP by lia.
fix_ret. cbn [aps_m aset_m fst snd] in RR.
destruct r as [buf|]; [| destruct RR].
destruct RR as (A & junk & -> & BR & HEAP2 & BLK & RGN & RGNS & HEXP).
specialize (HEXP (is_primary_big 65536 ltac:(lia))).
assert (RG1' : RNGS' RNG1) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE1| exact RG]).
assert (BA2 : ABASE' stdout_init m2).
{ eapply (ABASE_after_dpost AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI canary);
[exact HPR| exact HSP| exact HEAP2| exact MI2| exact ST2| exact BA1]. }
assert (ARG2 : AARGV' m2) by (eapply (AARGV_after_dpost AI usp USP16 USPLO USPHI); [exact HPR| exact HSP| exact ARG1m]).
assert (SJ2 : STAGE m2 sj).
{ eapply (dpost_stage AI usp DRV_CI); [exact HPR| exact HSP|]. unfold STAGE, ASTAGE. exact SJ. }
pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
apply implMA_from_evtF.
zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
zstep. zstep. zstep. zstep. apply evtF_done.
eapply (implMA_bind RNG1 _ _ s1 (POSTLOOP' fd)).
{ eapply rd_loop; lazymatch goal with |- RDINV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- _ => first [eassumption | lia] end.
unfold RDINV. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
do 17 eexists. exists bvmap_empty, fc, m2, A, [], junk, sj, 0x7fb54.
split; [reflexivity|]. split; [right; split; reflexivity|]. split; [reflexivity|].
split; [| split; [exact SJ2| split; [exact BA2| split; [exact ARG2| split; [exact RG1'| exact FRM]]]]].
split; [exact HEAP2|]. split; [rewrite (aps_so_of_rest _ _ SOE); exact SOI|]. split; [eapply aps_ok_rest; [exact SOE| exact RK]|]. split; [exact HEXP|]. cbn [length Z.of_nat Z.sub].
split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
- apply rw_cells_CB0. lia.
- unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia|]. split; [exact BR|]. split; [exact RGN| exact RGNS]. }
cbv beta. intros res s2 RNG2 ms2 PO.
destruct res as [|b c]; cbn [POSTLOOP] in PO.
{ apply implMA_ret. apply evtF_done. exact PO. }
clear dependent m2.
destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & x23 & Fv2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3
& -> & HC3 & BU3 & BA3 & ARG3 & RG3 & FRM3).
pose proof BA3 as (ST3 & MI3 & FR3 & AS3 & SE3 & GU3 & TR3 & HI3 & ROD3 & RCS3 & RCB3 & RSG3 & [errv3 ERR3] & SOF3). unfold AMFRAME in FR3. rewrite errno_addr_ATP in ERR3.
pose proof RG3 as (RGstk3 & RGtop3 & RGimg3 & _).
pose proof BU3 as (P3 & SO3 & RK3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3 & RGA3 & RGAS3).
pose proof BRR3 as (BQ1 & BQ2 & BQ3 & BQ4). pose proof (ablk_lin _ _ BQ1) as (BM1 & BM2 & BM3 & BM4). unfold AIMG_HI in BM1.
apply implMA_from_evtF. zstep. zstep. apply evtF_done.
eapply implMA_bind.
{ eapply implMA_msys.
eapply (close_spec RNG2) with (lo := LO) (errv := errv3); try reflexivity; rewrite ?errno_addr_ATP; unfold ATP; rewrite ?unsigned_lit by lia;
first [ exact ST3 | exact ERR3 | exact MI3 | lia | eapply rng_sub'; [exact RGstk3| lia] | eapply rng_sub'; [exact RGimg3| lia] ]. }
cbv beta. intros r3 s3 RNG3' ms3 [-> [-> PO]].
destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
unfold ATP in MUc, ERR4. rewrite ?unsigned_lit in MUc by lia. rewrite ?(unsigned_lit (usp + -128)) in ST4 by lia. change (6214288 + -164) with 6214124 in MUc, ERR4.
transport_after_call bsegs m3 m4 MUc WMc.
fix_ret.
assert (WOKW : Forall (WOK usp) [(usp + -128 - 32, usp + -128); (6214124, 6214124 + 4)]).
{ unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (P4 : AHEAP AI L RNG2 (aps_m s2) [HB b A3 cap3] m4).
{ eapply (AI_frame AI); [exact P3| exact MUc| exact WMc|]. pose proof (AI_layout AI _ _ _ _ _ P3) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
constructor; [| constructor; [| constructor]]; cbn [fst snd].
- left. left. lia.
- left. right; left. exists (0x5ed1e8, 0x5ed1f0). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
assert (BA4 : ABASE' stdout_init m4).
{ eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA3| exact WOKW| exact MUc| exact WMc| exact MI4| exact ST4| |].
- destruct SE3 as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
first [ exact Hc | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]; intros a' Ha'; cbn in Ha' |- *; lia ].
- eexists. rewrite errno_addr_ATP. exact ERR4. }
assert (ARG4 : AARGV' m4) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG3]).
assert (BLK4 : rw_cells bsegs m4 A3 [CB (length DATA3) DATA3; CB (Z.to_nat (cap3 - Z.of_nat (length DATA3))) junk3]).
{ first [ exact BLK3 | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact BLK3|]; intros a' Ha'; cbn in Ha' |- *; lia ]. }
apply implMA_ret. apply evtF_done. cbn [POSTB]. unfold RDONE.
do 17 eexists. exists Fv2, fc2, m4, A3, cap3, fd, DATA3. exists junk3.
split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exact BA4| split; [exact ARG4| split; [exact RG3| exact FRM3]]]].
split; [exact P4|]. split; [exact SO3|]. split; [exact RK3|]. split; [exact HA3|]. split; [exact BLK4|]. split; [exact CAP3|]. split; [exact LEN3|]. split; [exact BRR3|]. split; [exact RGA3| exact RGAS3].
Qed.
End B4.
End CANSEC1.
