(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Stdio Driver AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit ADriver_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
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
Ltac2 kr_t_AD_kit () := "C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface@astk_shadow_presC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c59OSSVerify5KrLib5BothW6AD_kit4dcliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<aclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5BothW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7in_fakeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib8RunConst9ATOP_al16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5BothW:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib6Common8DrvAgree?rw_cells_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef6firstnC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes3nat00I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5BothW:StdioFiles;stderr_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow<shadow_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib4LibA6ShadowBshadow_bytes_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow@unpoisoned_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit7shcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6hull64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9shad_monoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib5BothW6AD_kitAunpoisoned_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree<wr_at_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface:rodata_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm7hinv_bmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kitCshadow_bytes_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm>hinv_bm_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm7AHBM_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm7AHBM_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib5BothW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:rw_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface8AI_relroC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_image0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure?rw_cells_recastC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit8relro_C8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface<AGOT_STDERRPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface8ASTDERRPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface>AGOT_FUZZ_INITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface:AFUZZ_INITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:Znumtheory;Zmod_divideC56Stdlib6ZArith6BinInt1Z6divideK46Stdlib9micromega7EnvRing5PExpr06C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC47Corelib5Lists7ListDef5skipnI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps9keeps_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps7aset_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps5keepsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps9keeps_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio5rd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps9keeps_unrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps9keeps_sysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps9keeps_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps8keeps_ifC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps:keeps_bindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kitDa_stdio_write_loop_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9WRITE_MAXC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBstdout_stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit9a_rd_so_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit:a_upd_so_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit?a_stdio_write_kC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_writefnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kitFa_stdout_stdio_write_kC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:TIOCGWINSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5Stdio>stdout_fwritexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kitBa_stdout_writefn_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kitBa_stdout_towrite_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=STDOUT_BUFSIZC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio:out_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kitBa_stdout_fwritex_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit>a_out_pieces_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit:a_s_emit_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit6aps_mrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AD_kit7aps_mraC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps4tallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit6implMAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib5BothW6AD_kit;implF_etallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA@implF_epost_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01".   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition dcli (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  aclient_addr CI LB SP a \/ (shad ATOP <= a < shad SP).

Lemma magree_of_dpost : forall CI LB SP m m',
  aheap_pres CI LB SP m m' -> astk_shadow_pres SP m m' -> magree bsegs (dcli CI LB SP) m m'.
Proof using Type.
  intros CI LB SP m m' HP HS a Ha [Hc | Hs].
  - apply HP; assumption.
  - pose proof (HS a Hs) as E. split; [exact E|]. unfold wview, mrd. rewrite E. auto.
Qed.

Lemma dcli_weaken : forall CI LB LB' SP SP' a,
  dcli CI LB' SP' a -> SP <= SP' -> SP' <= 2^47 -> SP mod 8 = 0 -> (forall b, In b LB' -> In b LB) -> dcli CI LB SP a.
Proof using Type.
  intros CI LB LB' SP SP' a H HS HS' H8 HL. destruct H as [H | H].
  - left. revert H. unfold aclient_addr, in_block, in_fake. intros [X|[X|[(b & Hb & R)|(a' & X & E)]]].
    + left; lia. + right; left; exact X.
    + right; right; left. exists b. split; [apply HL; exact Hb| exact R].
    + right; right; right. exists a'. split; [| exact E].
      destruct X as [X|[X|(c & A & n & Hin & R)]]; [left; lia| right; left; exact X| right; right].
      exists c, A, n. split; [apply HL; exact Hin| exact R].
  -
    left. right; right; right. exists (8 * (a - ASHOFF)). split.
    + left. rewrite !shad_div in *. unfold ASHOFF in *. atop_facts. pose proof ATOP_al16. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
    + rewrite shad_div. unfold ASHOFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transport.
  Variable P : Z -> Prop.
  Variables (m m' : amem).
  Hypothesis AG : magree bsegs P m m'.

  Lemma stdout_file_magree : forall so, (forall a, (RSTDOUT <= a < RSTDOUT + 232) \/ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024) -> P a) ->
    stdout_file m so -> stdout_file m' so.
Proof using AG.
    intros so HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
    exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
    - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
    - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
  Qed.

  Lemma stderr_file_magree : (forall a, RSTDERR <= a < RSTDERR + 232 -> P a) -> stderr_file m -> stderr_file m'.
Proof using AG.
    intros HP (flags & mode & e & wend & tail & F1). exists flags, mode, e, wend, tail.
    eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. cbn in Ha. lia.
  Qed.

  Lemma shadow_bytes_magree : forall s1 s2 f, (forall a, s1 <= a < s2 -> P a) -> shadow_bytes m s1 s2 f -> shadow_bytes m' s1 s2 f.
Proof using AG.
    intros s1 s2 f HP SB. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
    intros s Hs. destruct (AG s ltac:(lia) ltac:(apply HP; lia)) as [E _]. exact E.
  Qed.

  Lemma unpoisoned_magree : forall lo hi, (forall a, shad lo <= a <= shad (hi - 1) -> P a) -> 0 <= lo -> hi <= KEND ->
    unpoisoned m lo hi -> unpoisoned m' lo hi.
Proof using AG.
    intros lo hi HP H0 H1 U. eapply unpoisoned_agree; [exact U|].
    intros s Hs. destruct (AG s ltac:(rewrite !shad_div in Hs; unfold ASHOFF, KEND in *; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])) ltac:(apply HP; lia)) as [E _]. exact E.
  Qed.

  Lemma rclean_magree : forall r, (forall a, shad (r_rlo r) <= a < shad (r_rhi r) -> P a) -> rclean m r -> rclean m' r.
Proof using AG.
    intros r HP [(U & HL & W & AB) LT]. pose proof HL as (H1 & H2 & H3 & H4 & H5 & H6). split; [| exact LT].
    split; [| split; [exact HL| split; [| exact AB]]].
    - eapply unpoisoned_magree; [| lia | unfold KEND in *; lia | exact U].
      intros a Ha. apply HP. pose proof (shad_mono (r_rlo r) (r_lo r) H1). pose proof (shad_mono (r_hi r - 1) (r_rhi r - 1) ltac:(lia)).
      assert (shad (r_rhi r - 1) < shad (r_rhi r)) by (rewrite !shad_div; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])). lia.
    - eapply wr_at_magree; [exact AG| exact W|]. intros a Ha. apply HP. lia.
  Qed.

  Lemma rodata_sh0_magree : (forall a, (shad 0x10000 <= a < shad 0x20dc0) \/ (shad AHBM_LO <= a < shad AHBM_HI) -> P a) ->
    rodata_sh0 m -> rodata_sh0 m'.
Proof using AG.
    intros HP [SB [W HB]]. split; [eapply shadow_bytes_magree; [intros a Ha; apply HP; left; exact Ha| exact SB]|].
    split; [eapply wr_at_magree; [exact AG| exact W|]; intros a Ha; apply HP; left; lia|].
    eapply hinv_bm_magree; [exact AG| intros a Ha; apply HP; right; exact Ha| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma harness_invA_magree : harness_invA m -> harness_invA m'.
Proof using AG.
    intros _. exact I.
  Qed.
End Transport.

(* [comment removed for export] *)
Lemma RSTDOUT_eq : RSTDOUT = 0xb67e8.
Proof using Type. reflexivity. Qed.
Lemma RSTDOUT_BUF_eq : RSTDOUT_BUF = 0x60d9a0.
Proof using Type. reflexivity. Qed.
Lemma RSTDERR_eq : RSTDERR = 0xb66f8.
Proof using Type. reflexivity. Qed.
Lemma shad_lit : forall a, shad a = 0x7fff8000 + a / 8.
Proof using Type. intros; apply shad_div. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Relro.
  Variable AI : AMallocIface.

  Lemma relro_C8 : forall L RNG st LB m A v,
    AHEAP AI L RNG st LB m -> ARELRO_LO <= A -> A + 8 <= ARELRO_HI ->
    rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
    rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof using Type.
    intros L RNG st LB m A v AH HLO HHI HB. pose proof (AI_relro AI L RNG st LB m AH) as R.
    eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | exact HB | unfold ARELRO_LO in *; lia | rewrite length_le8; unfold ARELRO_HI in *; lia ]
      | cbn; split; exact I | reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma drv_got_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
    rw_cells bsegs m AGOT_STDERRP [C8 (Z_to_bv 64 ASTDERRP)]
    /\ rw_cells bsegs m ASTDERRP [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs m AGOT_FUZZ_INIT [C8 (Z_to_bv 64 AFUZZ_INIT)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
Proof using Type.
    intros L RNG st LB m AH. unfold AGOT_STDERRP, ASTDERRP, AGOT_FUZZ_INIT, AFUZZ_INIT, got_ssp, ssp_guard.
    repeat match goal with |- _ /\ _ => split end;
      (eapply relro_C8; [exact AH | unfold ARELRO_LO; lia | unfold ARELRO_HI; lia | vm_compute; reflexivity]).
  Qed.
End Relro.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Lemma land3_range : forall c, 0 <= c -> 0 <= Z.land c 3 <= 3.
Proof using Type.
  intros c Hc. split; [apply Z.land_nonneg; lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound c 4 ltac:(lia)). change (2^2) with 4. lia.
Qed.

Lemma snez_norm : forall rv, -2^63 < rv < 2^63 -> Z.b2z (0 <? Z.land rv 18446744073709551615) = (if rv =? 0 then 0 else 1).
Proof using Type.
  intros rv Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eqb_spec rv 0) as [->|NE]; [reflexivity|].
  destruct (Z.ltb_spec0 0 (rv mod 2^64)) as [L|G]; [reflexivity|]. exfalso.
  pose proof (Z.mod_pos_bound rv (2^64) ltac:(lia)). assert (E : rv mod 2^64 = 0) by lia.
  apply Znumtheory.Zmod_divide in E; [| lia]. destruct E as [q E]. assert (q = 0) by lia. subst q. lia.
Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (skipn n l).
Proof using Type.
  intros A P n. induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; cbn; [constructor|].
  inversion H; subst. apply IH. assumption.
Qed.

Lemma unsigned_wz_mod32 : forall r, bv_unsigned (Z_to_bv 64 r) mod 2^32 = r mod 2^32.
Proof using Type.
  intros r. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ApsKeeps.
  Context {B : Type} (f : APS -> B).
  Hypothesis FSO : forall v s, f (aset_so v s) = f s.

  Lemma a_upd_so_k : forall g, keeps f (upd_so aps_so aset_so g).
Proof using FSO. intros g. unfold upd_so. apply keeps_upd. intros s. apply FSO. Qed.
  Lemma a_rd_so_k : keeps f (rd_so (St:=APS) aps_so).
Proof using Type. unfold rd_so. keeps_tac. Qed.
  Lemma a_stdio_write_loop_k : forall fuel fd iov, keeps f (stdio_write_loop (St:=APS) fuel fd iov).
Proof using Type. induction fuel as [|fuel IH]; intros fd iov; cbn; keeps_tac. Qed.
  Lemma a_stdio_write_k : forall fd buf s, keeps f (stdio_write (St:=APS) fd buf s).
Proof using Type. intros fd buf s. unfold stdio_write. pose proof a_stdio_write_loop_k. keeps_tac. Qed.
  Lemma a_stdout_stdio_write_k : forall s, keeps f (stdout_stdio_write aps_so aset_so s).
Proof using FSO. intros s. unfold stdout_stdio_write. pose proof a_rd_so_k. pose proof a_upd_so_k. pose proof a_stdio_write_k. keeps_tac. Qed.
  Lemma a_stdout_writefn_k : forall s, keeps f (stdout_writefn aps_so aset_so s).
Proof using FSO. intros s. unfold stdout_writefn. pose proof a_rd_so_k. pose proof a_upd_so_k. pose proof a_stdout_stdio_write_k. keeps_tac. Qed.
  Lemma a_stdout_towrite_k : keeps f (stdout_towrite aps_so aset_so).
Proof using FSO. unfold stdout_towrite. apply a_upd_so_k. Qed.
  Lemma a_stdout_fwritex_k : forall s, keeps f (stdout_fwritex aps_so aset_so s).
Proof using FSO. intros s. unfold stdout_fwritex. pose proof a_rd_so_k. pose proof a_upd_so_k. pose proof a_stdout_writefn_k. pose proof a_stdout_towrite_k. keeps_tac. Qed.
  Lemma a_out_pieces_k : forall ps, keeps f (out_pieces aps_so aset_so ps).
Proof using FSO. induction ps as [|p ps IH]; cbn; [apply keeps_ret|]. pose proof a_stdout_fwritex_k. keeps_tac. Qed.
  Lemma a_s_emit_k : forall v, keeps f (s_emit aps_so aset_so v).
Proof using FSO. intros v. unfold s_emit, stdout_vprintf. pose proof a_stdout_towrite_k. pose proof a_out_pieces_k. keeps_tac. Qed.
End ApsKeeps.

Lemma s_emit_aps_m : forall v, keeps aps_m (s_emit aps_so aset_so v).
Proof using Type. intros v. apply a_s_emit_k. intros; reflexivity. Qed.
(* [comment removed for export] *)
Definition aps_mr (s : APS) : astate * list (Z * Z) := (aps_m s, aps_resv s).
Lemma s_emit_aps_mr : forall v, keeps aps_mr (s_emit aps_so aset_so v).
Proof using Type. intros v. apply a_s_emit_k. intros; reflexivity. Qed.
(* [comment removed for export] *)
Definition aps_mra (s : APS) : astate * list (Z * Z) * Z := (aps_m s, aps_resv s, aps_atop s).
Lemma s_emit_aps_mra : forall v, keeps aps_mra (s_emit aps_so aset_so v).
Proof using Type. intros v. apply a_s_emit_k. intros; reflexivity. Qed.

Lemma implF_etall : forall {R} RNG (t : itree node (exc R)) (P : R -> Prop) (Q : R -> footprint -> machine_state -> Prop) ms,
  implS bsegs RNG t (epostF Q) ms -> tall P t ->
  implS bsegs RNG t (epostF (fun r RNG' ms' => Q r RNG' ms' /\ P r)) ms.
Proof using Type.
  intros R RNG t. revert RNG. induction t as [[|r]|n k IH]; cbn; intros RNG P Q ms H HP.
  - exact H.
  - eapply evtF_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp RNG' HF. apply IH; [apply Hk; exact HF| apply HP].
Qed.

Lemma implMA_keeps : forall {B A} (f : APS -> B) RNG (c : @Monad.M APS A) s Q ms,
  implMA RNG c s Q ms -> keeps f c -> implMA RNG c s (fun r s' RNG' ms' => Q r s' RNG' ms' /\ f s' = f s) ms.
Proof using Type.
  intros B A f RNG c s Q ms H K. unfold implMA in *.
  eapply implF_epost_mono; [eapply implF_etall; [exact H| apply K]|]. cbn. intros [a s'] RNG' ms' [HQ E]. split; [exact HQ| exact E].
Qed.
End CANSEC2.
