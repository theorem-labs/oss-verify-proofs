(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats ADriver_iface AD_kit AD_ctx AD_diag.
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
Ltac2 kr_t_AD_main_A () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indI5ARocqVerifyHarness?AgentSubmission4Spec6Driver7IOStyle00C5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapK47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List7map_nthC5ARocqVerifyHarness?AgentSubmission4Spec4Prog6argv_ZC47Corelib5Lists7ListDef3nthI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K5ARocqVerifyHarness?AgentSubmission4Spec5ProgA6AAlloc01C5ARocqVerifyHarness?AgentSubmission4Spec6Driver>read_loop_bodyC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrI5ARocqVerifyHarness?AgentSubmission4Spec6Driver9rd_result00C5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_lec5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A4RNGSC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3ALOK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA9rng_fp_leK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RFMTC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC47Corelib4Init5Peano2ltI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions5bv_eqC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C46Stdlib5Lists4List:length_mapK47Corelib5Lists7ListDef6Forall01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<nth_overflowC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leI46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8map_consI47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface@astk_shadow_presc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A5AARGVC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7astringC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit?magree_of_dpostC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit4dcliC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?bytes_at_magreeC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctxCastring_after_dpostC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00c5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A4geoAC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx4WOKbC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx<WOKb_outsideC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=astring_munchK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC46Stdlib9micromega;ZifyClasses6eq_iffC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast=munch_write_nC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast;stk_write_nC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8AMAIN_PCK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A6AENTRYC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ABASEC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6aps_okC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4ASTGC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ASTATC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun_cells0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_splitC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>ABASE_of_partsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_framec5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A;AARGV_munchC47Corelib4Init3Nat3addc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A>amain_prologueC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stdout_fileC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC56Stdlib6ZArith6BinInt1Z4landI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface6ASTAGEC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:ASTAGE_LENI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface;ASTAGE2_RETC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>errno_addr_ATPC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<ASTAGE_LEN_Zc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A3AP1C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7AMFRAMEC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0c5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A=amain_to_testK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3WOKC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx:astat_addrK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx;ASTAT_agreeC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kitBstdout_file_magreeC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3ioAK5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg01C5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_diagC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission4Spec6Driver8read_allC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps7afree_MC5ARocqVerifyHarness?AgentSubmission4Spec6Driver4le16C5ARocqVerifyHarness?AgentSubmission4Spec6Driver4le32C5ARocqVerifyHarness?AgentSubmission4Spec5ProgA;alloc_initAC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim4znthC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4runAC56Stdlib6ZArith6BinInt1Z7testbitC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA<alloc_countAC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8aat_exitC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=astring_factsC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A9arg_factsC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit@drv_got_of_aheapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib5Lists4List9nth_errorK46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree:u64ro_readK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW7AD_diagBafprintf_diag_postC5ARocqVerifyHarness?AgentSubmission4Spec6Driver6s_diagC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_ifaceCstderr_wfile0_wfileC5ARocqVerifyHarness?AgentSubmission5BothW7AD_diag:adiag_argsC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW7AD_diagCafprintf_diag_proofC5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx@implMA_of_implAMc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A:nth_argv_ZC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC4ELinuxProcessSemantics5Riscv3Sem7reg_getC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<stderr_wfileC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles9ssp_cellsC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A:after_diagC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAstderr_wfile_fileC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx<amain_returnC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit:implMA_retC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit;implMA_bindC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit@implMA_from_evtFC5ARocqVerifyHarness?AgentSubmission4Spec6Driver:main_modelK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<AGOT_STDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8ASTDERRPC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>AGOT_FUZZ_INITC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps9amalloc_MC5ARocqVerifyHarness?AgentSubmission4Spec6Driver7HDR_MINK5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg06K5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg07C5ARocqVerifyHarness?AgentSubmission4Spec6Driver9COUNT_MAXc5ARocqVerifyHarness?AgentSubmission5BothW9AD_main_A:argc_factsC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:AFUZZ_INITK47Corelib7Numbers7BinNums1N01C5ARocqVerifyHarness?AgentSubmission5BothW@I_printf_formats9FMT_USAGEI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;GLOBALS_TOPC5ARocqVerifyHarness?AgentSubmission5BothW7AD_diag>AFPRINTF_DEPTHC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_ranges".   
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
Section A.
  
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

  Lemma nth_argv_Z : forall i, nth i (argv_Z argv) [] = map bv_unsigned (nth i argv []).
Proof. intros i. unfold argv_Z. change (@nil Z) with (map bv_unsigned (@nil byte)) at 1. apply map_nth. Qed.
  
  Notation ABASE' j8 := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 RSTK canary).
  Notation AMFRAME' j8 := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 j8).
  Notation LO := (ALO usp).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.

  
  Definition RNGS (RNG : footprint) : Prop :=
    rng RNG LO (usp + 24 - LO) /\ rng RNG LO (al_top L - LO) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG
    /\ rrng RNG RSTK /\ rrng RNG RFMT /\ rrng RNG RBstdout /\ rng0 RNG
    /\ rng RNG P0 (zlength arg0 + 1 + zlength slack0) /\ rrng RNG RA0
    /\ (2 <= argc -> rng RNG P1 (zlength arg1 + 1 + zlength slack1) /\ rrng RNG RA1).

  Lemma RNGS_mono : forall R R', fp_le R R' -> RNGS R -> RNGS R'.
Proof.
intros R R' LE (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold RNGS, rrng, rng0 in *.
repeat match goal with |- _ /\ _ => split end; try (eapply rng_fp_le; [exact LE|]; assumption).
- eapply rng_fs_mono; eauto.
- intros b Hb. eapply rng_fp_le; [exact LE|]. apply G8. exact Hb.
- intros H. destruct (G11 H) as [X Y]. split; (eapply rng_fp_le; [exact LE|]); assumption.
Qed.

  
  Definition AARGV (mm : amem) : Prop :=
    bytes_at bsegs mm (usp + 8) (u64s [wz P0]) /\ astring usp mm P0 arg0 slack0 RA0
    /\ (2 <= argc -> bytes_at bsegs mm (usp + 16) (u64s [wz P1]) /\ astring usp mm P1 arg1 slack1 RA1).

  Lemma geoA : ATOP <= LO /\ LO + 8388608 - 4096 = usp /\ KHIGH <= LO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
Proof. clear BOT. unfold ALO, KHIGH in *. repeat split; lia. Qed.   

  Lemma argc_facts : 1 <= argc <= 1024.
Proof. destruct VARGV as (A & _). exact A. Qed.

  Lemma arg_facts : forall i, Forall (fun c => 0 < c < 256) (map bv_unsigned (nth i argv [])) /\ zlength (map bv_unsigned (nth i argv [])) <= 131071.
Proof.
intros i. destruct VARGV as (_ & _ & LEN & NONUL & _).
destruct (Nat.lt_ge_cases i (length argv)) as [LT|GE].
- pose proof (proj1 (Forall_forall _ _) LEN _ (nth_In argv [] LT)) as L1. pose proof (proj1 (Forall_forall _ _) NONUL _ (nth_In argv [] LT)) as N1.
cbv beta in L1, N1. split.
+ apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
assert (bv_unsigned b <> 0); [| lia]. intros E. apply N1. replace (Z_to_bv 8 0) with b; [exact Hb|].
apply bv_eq. rewrite E. vm_compute. reflexivity.
+ unfold zlength in *. rewrite length_map. lia.
- rewrite nth_overflow by lia. cbn. split; [constructor| unfold zlength; cbn; lia].
Qed.

  
  Lemma AARGV_after_dpost : forall LB m m', aheap_pres CI LB (usp + -128) m m' -> astk_shadow_pres (usp + -128) m m' -> AARGV m -> AARGV m'.
Proof.
clear BOT. intros LB m m' HP HS (B0 & A0 & A1). pose proof geoA as (G1 & G2 & G3 & G4 & G5).
pose proof (magree_of_dpost _ _ _ _ _ HP HS) as AG.
split; [| split].
- eapply bytes_at_magree; [exact AG| exact B0|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. left. left. lia.
- eapply astring_after_dpost; eauto.
- intros H2. destruct (A1 H2) as [B1 A1']. split; [| eapply astring_after_dpost; eauto].
eapply bytes_at_magree; [exact AG| exact B1|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. left. left. lia.
Qed.

  Lemma AARGV_munch : forall hi W m m', ALO usp <= hi <= usp + 8 -> Forall (WOKb usp hi) W -> munch W m m' -> wmono bsegs m m' -> AARGV m -> AARGV m'.
Proof.
clear BOT. intros hi W m m' Hhi HW MU WM (B0 & A0 & A1). pose proof geoA as (G1 & G2 & G3 & G4 & G5).
pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
split; [| split].
- eapply bytes_at_magree; [exact AG| exact B0|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. cbv beta.
eapply (WOKb_outside usp USP16 USPLO USPHI); [| exact HW| left; lia]; lia.
- eapply (astring_munch usp USP16 USPLO USPHI hi); [split; lia| exact HW| exact MU| exact WM| exact A0].
- intros H2. destruct (A1 H2) as [B1 A1']. split; [| eapply (astring_munch usp USP16 USPLO USPHI hi); [split; lia| exact HW| exact MU| exact WM| exact A1']].
eapply bytes_at_magree; [exact AG| exact B1|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. cbv beta.
eapply (WOKb_outside usp USP16 USPLO USPHI); [| exact HW| left; lia]; lia.
Qed.

  

  
  Definition AENTRY (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : amem),
      ms = MS (mkR (wz ASTAGE2_RET) (wz (usp + -48)) gpv tpv t0 t1 t2 S0 S1 (wz argc) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                   S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
              bvmap_empty (wz AMAIN_PC) (Z_to_bv 32 0) None mm (seg_rom bsegs)
      /\ stk bsegs mm LO usp /\ mem_inv bsegs mm
      /\ ASTAT TID mm /\ stderr_wfile0 mm /\ rw_cells bsegs mm ssp_guard [C8 canary]
      /\ atrun_cells0 mm /\ harness_invA mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
      /\ rclean mm RSTG                                                      
      /\ (exists errv, rw_cells bsegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
      /\ stdout_file mm stdout_init /\ aps_so st = stdout_init /\ aps_ok L st
      /\ AHEAP AI L RNG (aps_m st) [] mm
      /\ AARGV mm /\ RNGS RNG
      
      /\ bytes_at bsegs mm (usp + -8) (le8 (wz 0))
      /\ ASTG mm.                                                             

  
  Lemma amain_prologue : forall RNG (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m LO (usp + -48) -> mem_inv bsegs m -> rng RNG LO (usp + 24 - LO) ->
    (forall (j8 : list byte) m', rw_cells bsegs m' (usp + -128) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bsegs m' LO (usp + -128) ->
        munch [(usp - 128, usp - 48)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        evtF bsegs RNG Q (MS (mkR ra (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz 0x7fb18) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra (wz (usp + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz AMAIN_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST MI RG K. pose proof geoA as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof (munch_refl [(usp - 128, usp - 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold AMAIN_PC. zstep.
carve_frame 80%nat ST.
do 10 zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => eapply (K _ mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
Qed.

  
  Definition AP1 (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : amem) (j8 : list byte),
      ms = MS (mkR (wz ASTAGE2_RET) (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) S1 (wz 2) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                   S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
              bvmap_empty (wz 0x7fb1c) fc None mm (seg_rom bsegs)
      /\ ABASE' j8 stdout_init mm /\ aps_so st = stdout_init /\ aps_ok L st /\ AHEAP AI L RNG (aps_m st) [] mm
      /\ AARGV mm /\ RNGS RNG /\ bytes_at bsegs mm (usp + -8) (le8 (wz 0)) /\ frm0 fc /\ ASTG mm.

  
  Lemma amain_to_test : forall RNG st (ms : machine_state) (Q : machine_state -> Prop),
    AENTRY RNG st ms ->
    (forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : amem) (j8 : list byte),
        ABASE' j8 stdout_init mm -> aps_so st = stdout_init -> aps_ok L st -> AHEAP AI L RNG (aps_m st) [] mm -> AARGV mm -> RNGS RNG ->
        bytes_at bsegs mm (usp + -8) (le8 (wz 0)) -> ASTG mm ->
        evtF bsegs RNG Q (MS (mkR (wz ASTAGE2_RET) (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) S1 (wz argc) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                               S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                          bvmap_empty (wz 0x7fb18) (Z_to_bv 32 0) None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q ms.
Proof.
intros RNG st ms Q AM K.
destruct AM as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m
& -> & ST & MI & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF & SOI & RK & AH & ARG & RG & U8 & SJ).
pose proof geoA as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. pose proof RG as (RGstk & _).
destruct (stk_split _ _ LO (usp + -48) usp ST ltac:(lia)) as [ST1 ST2].
eapply amain_prologue; [exact ST1| exact MI| exact RGstk|].
intros j8 m1 FR ST3 MU WM MI1.
assert (HW : Forall (WOKb usp (usp + -48)) [(usp - 128, usp - 48)]) by (constructor; [left; cbn; lia| constructor]).
apply (K t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 j8).
- pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
eapply (ABASE_of_parts usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 RSTK USP16 USPLO USPHI canary (usp + -48) _ m m1);
first [exact HW| exact MU| exact WM| eassumption| idtac].
all: lazymatch goal with
| |- _ /\ _ => split; lia
| |- AMFRAME _ _ _ _ _ _ _ _ _ _ _ => unfold AMFRAME; exact FR
| |- stderr_wfile0 _ =>
destruct SE as (flags & mode & e & wend & tail & Hc & HR); exists flags, mode, e, wend, tail; split; [| exact HR];
eapply rw_cells_magree; [exact AG| exact Hc|]; intros a Ha; cbn in Ha |- *; lia
| |- exists errv, _ =>
destruct ERR as [errv ERR]; exists errv; eapply rw_cells_magree; [exact AG| exact ERR|]; intros a Ha;
rewrite ?errno_addr_ATP in Ha; cbn in Ha |- *; lia
end.
- exact SOI.
- exact RK.
- eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [| constructor]. left. left. cbn [fst snd].
pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *. lia.
- eapply (AARGV_munch (usp + -48)); [split; lia| exact HW| exact MU| exact WM| exact ARG].
- exact RG.
- eapply bytes_at_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact U8|]. intros a Ha. rewrite length_le8 in Ha. cbn. lia.
- destruct SJ as [sj SJ]. exists sj. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact SJ|].
intros a Ha. pose proof ASTAGE_LEN_Z as STGZ. cbn in Ha |- *. unfold ASTAGE in Ha. lia.
Qed.

  
  Lemma amain_to_P1 : forall RNG st (ms : machine_state) (Q : machine_state -> Prop),
    argc = 2 -> AENTRY RNG st ms ->
    (forall ms', AP1 RNG st ms' -> evtF bsegs RNG Q ms') ->
    evtF bsegs RNG Q ms.
Proof.
intros RNG st ms Q E2 AM K.
eapply amain_to_test; [exact AM|]. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm j8 BA SOI RK AH ARG RG U8 SJ.
rewrite E2. pose proof BA as (ST & MI & _).
zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
apply K. unfold AP1. do 13 eexists. exists (Z_to_bv 32 0), mm, j8. split; [reflexivity|].
split; [exact BA|]. split; [exact SOI|]. split; [exact RK|]. split; [exact AH|]. split; [exact ARG|]. split; [exact RG|]. split; [exact U8|].
split; [vm_compute; reflexivity| exact SJ].
Qed.

  
  Lemma after_diag : forall j8 so m m' W,
    ABASE' j8 so m -> Forall (WOK usp) W -> munch W m m' -> wmono bsegs m m' ->
    AMFRAME' j8 m' /\ ASTAT TID m' /\ stdout_file m' so.
Proof.
intros j8 so m m' W (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM.
pose proof geoA as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR|]. intros a Ha. apply WOKo; [exact HW|]. cbn in Ha. lia. }
split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. apply WOKo; [exact HW|]. right.
unfold astat_addr, astat_app, astat_sh in Ha. rewrite ?shad_div in Ha. unfold ASHOFF in Ha. lia. }
eapply stdout_file_magree; [exact AG| | exact SOF]. intros a Ha. apply WOKo; [exact HW|]. right; left. cbn in Ha. lia.
Qed.

  
  Lemma amain_usage : forall RNG st ms, AENTRY RNG st ms -> argc <> 2 ->
    implMA RNG (main_model (ioA AAllocAsan) amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan)
                           (alloc_countA AAllocAsan) (argv_Z argv)) st
           (fun code s' RNG' ms' => aat_exit code s' RNG' ms') ms.
Proof.
intros RNG st ms AM HARGC.
unfold main_model. unfold argv_Z at 1. rewrite length_map.
replace (argc =? 2) with false by (symmetry; apply Z.eqb_neq; exact HARGC). cbn [negb].
apply implMA_from_evtF.
eapply amain_to_test; [exact AM|]. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm j8 BA SOI RK AH ARG RG U8 _.
pose proof geoA as (G1 & G2 & G3 & G4 & G5). pose proof argc_facts as AC. unfold KHIGH in *.
pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF).
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & _).
destruct ARG as (B0 & A0 & _). pose proof (astring_facts usp _ _ _ _ _ A0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
destruct (arg_facts 0) as [HF0 LEN0].
destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (GSE & PSE & _ & GSSP).
zstep. if_cases K0; zify_cond K0. 2: { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
zstep. zstep. zstep.
pose proof (u64ro_read bsegs mm (usp + 8) [wz P0] 0 (wz P0) (wz (usp + 8)) B0 eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep.
apply evtF_done.
eapply implMA_bind.
{ unfold ioA, io_S, io_diag. rewrite (nth_argv_Z 0). apply implMA_of_implAM.
eapply (afprintf_diag_proof HSTRN RNG RSTK (DUsage arg0)) with (lo := LO); rewrite ?unsigned_lit by lia;
first [ apply stderr_wfile0_wfile; exact SE | reflexivity | exact ST | exact MI | exact RCS | exact ROD | exact RGimg | exact RG0 | exact RRS | exact RRF
| split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ AH) | idtac ].
all: try (unfold AFPRINTF_DEPTH; lia).
- cbn [adiag_args]. split; [reflexivity|]. exists slack0, RA0. destruct A0 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
rewrite ?unsigned_lit by lia. unfold GLOBALS_TOP, FmtFp.INT_MAX.
repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
- unfold KHIGH. lia.
- eapply rng_sub'; [exact RGstk| lia]. }
cbv beta. intros [] st' RNG' ms' [-> PO].
destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
apply implMA_ret.
assert (HW2 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
destruct (after_diag _ _ _ _ _ BA HW2 MU2 WM2) as (FR2 & AS2 & SOF2).
zstep.
eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 USP16 USPLO USPHI canary);
first [exact FR2 | exact ST2 | exact AS2 | exact MI2 | exact HT | exact RGimg | exact RGimsh | exact RG0 | idtac].
- eapply (AI_frame AI); [exact AH| exact MU2| exact WM2|].
pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _).
constructor; [| constructor; [| constructor]]; cbn [fst snd].
+ left. left. lia.
+ left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia].
- rewrite SOI. exact SOF2.
- apply stderr_wfile_file. exact SEW.
- exact (proj2 SSP2).
- eapply rng_sub'; [exact RGstk| lia].
Qed.
End A.
End CANSEC1.
