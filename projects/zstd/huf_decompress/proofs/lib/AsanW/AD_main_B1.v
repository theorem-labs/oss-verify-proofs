(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AHarness_bm.
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
Ltac2 kr_t_AD_main_B1 () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AD_main_B16AS_OOMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AD_main_B15s_oomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AD_main_B18AS_SHORTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AD_main_B17s_shortC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AD_main_B17AS_OVERC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AD_main_B16s_overC1?~~~~~~~~~~~~~~~C46Stdlib7Strings6StringDlist_ascii_of_stringI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib7Strings5Ascii:N_of_asciiC56Stdlib6ZArith6BinInt1Z4of_NI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib4Init9Datatypes4list01C46Stdlib7Strings5Ascii?N_ascii_boundedK47Corelib7Numbers7BinNums1N02C56Stdlib6NArith6BinNat1N2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib5Lists7ListDef6Forall02K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I46Stdlib7Strings5Ascii5ascii00I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib7Strings6String6string00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K59OSSVerify5KrLib4Spec5ProgA6AAlloc01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit6implMAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit;implMA_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit:implMA_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA3AStC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5AsanW:AD_main_B1<rd_grow_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbK59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA3ioAC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3eqbC59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum01C59OSSVerify5KrLib4Spec<AsanProgDeps:AAllocAsanC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface6ASTAGEC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5AsanW9AProg_kit@implMA_from_evtFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib5AsanW6AD_ctx3ALOC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5AsanW7AD_diag:adiag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx5ABASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AD_main_A4RNGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface8aat_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx7AMFRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx5ASTATC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface<atrun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface:rodata_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_topC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5AsanW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6MonadF4rng0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_kit@drv_got_of_aheapC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7AD_diagBafprintf_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;Stdio_ifaceCstderr_wfile0_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5AsanW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7AD_diagCafprintf_diag_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx@implMA_of_implAMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib5AsanW>F_printf_iface<stderr_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib5AsanW6AD_ctx3WOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5AsanW9AD_main_A:after_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface9AI_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4al_UC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C59OSSVerify5KrLib5AsanW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface3aciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface=aclient_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_ifaceAaclient_app_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib5AsanW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5AsanW=AMalloc_iface8AI_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>F_printf_ifaceAstderr_wfile_fileC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5AsanW6AD_ctx;aexit2_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit8RBstdoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface4RSTGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface4RFMTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface<AGOT_STDERRPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface8ASTDERRPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface>AGOT_FUZZ_INITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface:AFUZZ_INITC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5AsanW7AD_diag>AFPRINTF_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5AUMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5AsanW=ADriver_iface>drv_img_rangesC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
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
Definition AS_OOM : Z := 0x14794.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition AS_SHORT : Z := 0x1f80e.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition AS_OVER : Z := 0x15847.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b asegs AS_OOM (zb s_oom) = true.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p;2p;1p;3p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p73110p1001Zp4p7210p8p1002Kp4p7210P1p8g0037j23Tg003Qj12Tg004Lj30Tg005Ej31Tg005_R1g006?R0'3g006_g007Tg008P#230=110do"). Qed.
Lemma s_short_ro : ro_bytes_b asegs AS_SHORT (zb s_short) = true.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p;2p;1p;3g0037j23Tg003Qj12Tg004Lj30Tg005Ej31Tg005_R0g006?R1'3g006_g009Kg00:I#230=101do"). Qed.
Lemma s_over_ro : ro_bytes_b asegs AS_OVER (zb s_over) = true.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "p;2p;1p;3g0037j23Tg003Qj12Tg004Lj30Tg005Ej31Tg005_R0g006?R1'3g006_g00;Fg00<C#230=101do"). Qed.
Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"] "h01lh14__x1h21ah31Hh42H0h52IHh67__arithh74__ffh88__varmaph95__with:1ch;4cstrh<1sp;1p;2p;3p;4p;7p;6p;5p;<p;8g00=?j1ZTg00=lj1?Tg00>Lj26Tg00>hj10Tg00?Mj1YTg00?kR0j25Tg00@Gj2:Tg00@bj11Tg00ADR1j12Tg00Abj33Tg00BCj2ATg00Bdj1>Tg00CDj1XTg00Ckj1TTg00DIR2j2<Tg0037j27Tg00Dej4LTg00ELj1JTg00Eoj2ITg00FMj1HTg00Fkj1GTg00GVj29Tg00H9j2FTg00H\j4=Tg00IGj1ETg00Iij7DTg00JMj2KTg00Joj2CTg005Ej3BTg00K[j3NTg00L:j4OTg00Llj6PTg00MMj3QTg00Mmj5@Tg00NOj1RTg00OBj4STg00O^l<WTg00PCj7VTg00Pgj8UTg00QKR3g00QjR4f1R5f0R6CSp=4g00RHP4P2P1P0g00Rff5f4R0f3R1f2R2P5P6M<Wp=MP5g00SFR7g00SeR8P8g00TER9P6g00TeFVp=8P1P7P8P8P9P2P5P6GUp=;g00UE%Z6%?3R:P3g00UfR;/66R<g00VDR=#0#0#0#0#0#0#0#0R>#YR?,56':X:4R@%16#2X23RA/46534RBX0:1A4@%>3,4A934@eP4P@%12RC#214A5%X2%T>R>,<C%11R1/<>%21RC/5?RDP1PC174CP>P?174?EMP6CLPD%10R0#J%20,6;g00ViR0#>%?01I45%H4%G4R0P4194;g00WU1F4=R=C=,80RD%E8R>P0P4P=g00X<194?C=,80R=P>P0P7P8P8P9PDP=FDC;C;1K09P6P2g005_R0g006?R9'71C62=B09dAN4;5COb7b8b9X14155?16;2152?':[\<^14P6f6#1#2P5P2O3b6b;b4b3P6EPAQ325,4A934@eX5BX0:X23P6D@b0%R6934@eW<o"). Qed.

(* [comment removed for export] *)
Lemma implMA_loop_S : forall {X R} RNG fuel (body : X -> @Monad.M APS (X + R)) x s (Q : R -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG (body x) s (fun r s' RNG' ms' => match r with
                                        | inl x' => implMA RNG' (mloop fuel body x') s' Q ms'
                                        | inr v => evtF asegs RNG' (Q v s' RNG') ms'
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

(* [comment removed for export] *)
Section B.
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
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x7fb7c] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x7fbd0] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x7fbf4] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x7fd24] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x7fe5c] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x7fef0] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).

  (* [comment removed for export] *)
  Definition BUF (mm : amem) (s : APS) (RNG : footprint) (bufp : AsanCtrl.aptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    AHEAP AI L RNG (aps_m s) [HB bufp A cap] mm /\ aps_so s = stdout_init /\ aps_ok L s /\ A = aptr_addr_M s bufp
    /\ rw_cells asegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ ablock_range A cap
    /\ rng RNG A cap /\ rng RNG (shad A) (shlen (cap + 7)).

  (* [comment removed for export] *)
  Definition STAGE (mm : amem) (sj : list byte) : Prop := rw_cells asegs mm ASTAGE [CB ASTAGE_LEN sj].

  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Definition RDINV (fd : Z) (st : rd_st) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A : Z) (DATA junk : list byte) (sj : list byte) (pc : Z),
      ms = RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ ((pc = 0x7fbb0 /\ x9 = Z_to_bv 64 A) \/ (pc = 0x7fb90 /\ rd_content st = []))
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s RNG (rd_buf st) A (rd_cap st) DATA junk /\ STAGE mm sj
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDBRK (fd : Z) (bufp : AsanCtrl.aptr) (content : list Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A cap : Z) (DATA junk : list byte),
      ms = RST 0x7fc1c x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  Definition POSTBODY (fd : Z) (r : rd_st + rd_result) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDINV fd st' s RNG ms
    | inr RdExit => aat_exit 2 s RNG ms
    | inr (RdDone b c) => RDBRK fd b c s RNG ms
    end.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma afprintf_exit : forall (d : diag_msg) {R} (K : @Monad.M APS R) (Q : R -> APS -> footprint -> machine_state -> Prop) (s : APS) (LB : list ablock) RNG
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    adiag_args RNG d mm a1v a2v LO (usp + -128) ->
    ABASE' stdout_init mm -> AHEAP AI L RNG (aps_m s) LB mm -> aps_so s = stdout_init -> frm0 fc -> RNGS' RNG ->
    (forall ms', aat_exit 2 s RNG ms' -> implMA RNG K s Q ms') ->
    implMA RNG (s_diag d ;;; K) s Q
      (GST 0x7fd88 x1 t0 t1 t2 x9 (Z_to_bv 64 RSTDERR) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z)); (constr:(135872%Z), constr:(136000%Z))] (kr_t_AD_main_B1 ()) ["CANSEC1"; "B"] "p'0h01Hh11kh22m'h33fc'h42Fth52t6h62t5h74errvh82t4h92t3h:2a7h;4__x1h<2a6h=2a5h>4__x2h?2a4h@7__arithhA7__sat49hB7__sat50hC7__sat51hD2a3hE4__ffhF8__varmaphG5__withH2a2hI2a1hJ3ms'hK1zhL2a0hM1bhN2ivhO4RNG'hP4__p1hQ7__sat52hR1ahS2t2hT2HahU4__p2hV7__sat53hW4__x3hX2s'hY2t1hZ2_Hh[2FAh\2H2h]2H6h^3MU2h_3ST2h`4__p3ha3clshb2fnhc1mhd1she3st'hf2t0hg2AHhh2AShi3AS2hj2BAhk2DAhl3ERRhm1Fhn3FEQho2FRhp3FR2hq3FRMhr4FRM2hs2G1ht2G2hu2G3hv2G4hw2G5hx4GSSPhy2GUhz2H0h{2H1h|2H3h}2H4h~2H5i002H7i012H8i022HIi032HKi043HW2i051Ki062LBi072MIi083MI2i092POi0:1Qi0;1Ri0<3RCBi0=3RCSi0>2RGi0?3RG0i0@4RGfsi0A5RGimgi0B6RGimshi0C5RGstki0D5RGtopi0E3RNGi0F3RODi0G3RRBi0H3RRFi0I3RRSi0J3RSGi0K2SEi0L3SEWi0M2SOi0N3SOFi0O4SOF2i0P4SSP2i0Q2STi0R2TRi0S3WM2i0T2Y1i0U2Y2i0V2Y3i0W2Y4i0X3_H0i0Y3_H1i0Z3a1vi0[3a2vi0\2b0i0]2b1i0^2b2i0_2b3i0`2b4i0a2b5i0b2b6i0c2b7i0d1di0e2fci0f2m2i0g2mmi0h4ms''i0i2u0i0j2u1i0k2u2i0l2u3i0m2u4i0n2u5i0o2u6i0p2x1i0q3x13i0r3x14i0s3x15i0t3x16i0u3x17i0v3x18i0w3x19i0x3x20i0y3x21i0z3x22i0{3x23i0|2x9i0}1ui0~1xp%0p%1p%2p%3p&0p&1p&2p;2p;1p;7p;?p;3p;<p;4p;6p;Op;;p;8p;5p;>p;Ip;Fp;np;=p;gp;:p200S00g001ZR0p4p7210p8Q00g00]DR1p4p710p8Q00g000eR2p4p73110p8Q00g00_4R3p4p7210p8Q00g01=lR4p4p710p8P0k22oTg00=lk10vTg00>hj11Tg00Ckk10ETg014Lk10wTg01?1j15Tg002Kk22_Tg00hbk10jTg01?Vk12KTg01@Kk11HTg01@ij2<Tg01AFk71@Tg01BCm?1?Tg01C:j1pTg01D6k72lTg01E4k11mTg005Ej36Tg01F1k107Tg01Fam<1_Tg00?Mj1ATg01GZk41Zk32HTP1j67Tg01H[k12STg00>Lj28Tg00m0j2BTg01IQk21GTg01Ink21\Tg00@GR1j22Tg01JNj2FTg01K4lO4Tg00IGk11uTg01Kfk12kTg01L_j73Tg01MQl;oTg01NJj2hTg01OAk10[Tg00Bdk10ZTg01P6k20Yk12:Tg01P`k12dTg01QUk114Tg01RYk10TTg01S^k10]Tg01Tdk10_Tg01Ugj2LTg01VbS01j20Tg01W<j3UTg01Wok12@Tg01Xfk41NTg00OBk41FTg00l8k20xTg014ok21VTg01YBk125Tg00c=k10nTg01Ybj2MTg01Z[k10MTg01[Qk81{Tg01\Sk11xTg01]@j2?Tg01]bj4iTg0037j2TTg01^Ok12nTg01_Vk12mTg01`^k20KTg01aQk30JTg01b4k21wTg01b`k51tTg01cIk31sTg01d0k31rTg01e;k21qTg01f7k21pTg01f_k21oTg01gWk31=Tg01h<k21nTg0000j6]Tg01i>k22iTg01j9k31lTg01jdk31kTg01k_k21jTg01ldk21hTg01mfk11gTg01nfk21fTg01oFk40;Tg01ofk11eTg020Wm>1dTg021Pk11cTg00BCk20tTg022FmI0smF2gTg023Kk22fTg024Uk12eTg025Sk21bTg00?kj2dTg026;k31aTg026_k21`Tg027Pk20pTg0289k319Tg028bk22cTg00MMj3wTg029Nk12bTg00Eok217Tg029lk40qTg00FMk12aTg00Fkk12`Tg00H9k20oTg00H\k40WTg02:Jk31]Tg00GVk21[Tg00JMk22^Tg00Jok22]Tg00K[k32\Tg00L:k42[Tg02:mk210Tg02;ik413Tg02<Dk12ZTg02==k12YTg02>6k71YTg02>nmn2XTg02@4k72WTg02A6k12RTg02Alk12QTg02BEk20iTg02Bok10XTg02D5k20?Tg02E4k30GTg02Ehk61<Tg02FDk32NTg02G?k42MTg02G[k22LTg02HPk31MTg02IEj2JTg02I_k303Tg02J9k30NTg00Llk60gTg00Abk30OTg02JSmI2ITg02KRk82GTg02LTk12ETg02MKk10}Tg02NIk12DTg02OFk12CTg02P;k12BTg02P[k22ATg02Q5k12?Tg02Qmk22>Tg02Rik606Tg02Sok50fTg02U9k30@Tg02UPk12=Tg02VHk12<Tg02W@k20cTg02W]k12;Tg02XVk32FTg02YOk50FTg02Ylk428Tg02ZFm=27Tg02[Gk20VTg02\Hk226Tg02]Sk32TTg02]nmg2UTg02^kk72VTg02_dm:1WTP4k71XTP3m;24Tg02`ak523Tg02aZk21ETP2k51DTg02bQk41:Tg02cCj4{Tg02d9k21^Tg02dmk322Tg02f4k221Tg00PCk718Tg02g<k620Tg00Iik71~Tg02g`k31vTg02hCk31}Tg00Pgk82hTg02hfk30uTg02iZk31|Tg02j7k32jTf0R2#1#1#1#1p=K%12#1p>04%12#Ap>0Pg00QjR3f1R4;62p=_%12#1#1#1#1#1#1#Ap=m%12#5#5#1p=D%12#5#5#5p=V%52#1#1#5p>0>%52#5#5#5p=Q%12#1#1#Ap=E%52#5p>0y%52#1#5#5p>01%12#1#1#5p=Rf7R0f6R5g00c\R6g00SeR7f5R8f4R9-1E6f3R:I1Df2R;P4P2E7p=>g006_R<P;P4P2H1:p=yg02jTR=?w42p>0B%52#1#1p=kP<P;P4P2C{p=@&0_01L58g02kIR>,L9g02lFR?,L:10;4g02mCS02-0V2'2'2'2'2'2p=g&148P<P9g02n>S03P:C{&0T;&0]4/22'2'2'2p=z1242,2;p=C21^<4/22p=s21^<2p>0Q1h;4/22p>0mQ02-0V2p=Y1L:?10;4/22'2p=x1L:;1L4>/22'2p>0C&0];&0_4/22'2p>0kP<P:Q03P;C{&0T4/22'2p>1UP<P4Q03P2C{p>0h10;4/22p>2P1L;>1L4?/22'2p>2O&0T8&0]9&0_:1L;4/22'2'2'2p>1R1L9>1L:?10;4Q02-0V2'2'2'2p>1;1L2>p>1K1L2?p>1J10;4Q02-0V2'2p>1I%12#5#5p>0S%52#1#5#1p=O%52#5#5#5#5#5#5#5p>08%12#5#1#1p=NAU9:;1M42'2p=G&0M5AU89:1M;4/22'2'2p=f1M9:g02o=R?,M;1M4>/22'2'2,28p=uAU:;4/22p=^1M;4/22p>0I1M5?1M8>&0M9AU:;4/22'2'2'2p>0b1M2?p>1CAU89:1M;4/22'2p>0a1M;>&0M4/22'2p>1B1M2>p>1AP<P4g030:P2C{p>0zP<P4g031?S04P2C{p>0LP<P4g032@P2C{p>02P<P4g033GP2C{p=l21E62p>1zP6P7P;P4P2I1Dp>1yP5P8P9P:P;CiP4P2Cip=HP9P:1?;4P2Cip=W%52#5#5#1p>0`%52#5#1#1p=[%12#1#5#5p>0=%52#1#1#1p=S%52#1#1#1#1#1#5#1p=~g00f0R>@2242-21;p=v%52#1p>1i%12#1#1#1#1#1#1#1p>0A18;4/22p>0rg00UfS05/82p=Z21[32p=aP;g00SFR?P7P7g00TES06P3P4g00WUR@P2H0Wg00TeRAK18p=eP4P?P7P7Q06P2J20p>16P;P?P7P7Q06P4P2K1~p=XB1v342p=|B1}342p=rP4P?P7P7Q06P2PAK18p>0UP:P?P7P7Q06P3B1v3;4P@P2H0WPAK18p=tP3P4g00X<P2H0Wp>15P:P?P7P7Q06P;P4P2L2hp=`1<;4/82p>0:P3P9P:P;P4P2E]p>0D1842,2;p>12P6P2P4P;P:P9P8P5P0f8R?f9R@f:RBf;S07f<RCf=S08f>S09f?S0:f@S0;fAS0<fBS0=fCS0>fDS0?PAfES0@fFS0ANI0sp>0lP3P3P4P2H0;p>0R20i4296:;p==A6642,2;,2:,29,28p=;B0u<9:1242,2;'2p=9A6>89B0G:;4/22'2p=:20i:;20i42569p=IP5P8P9P:P;P4P2F396>0p>1T&0X920?:;A6642'2'2p>0\P<P:P;P4H1:/22p>11B0G89:B0u<;4/22'2p>1SA6642p=bP<P5P8P9H1:&0X:20?;4/22'2'2,20p=n&074/22p>0<B0u<;4/22p>1QB0u<42p>1P20?:;A6642'2p>1OB1|332p>1>B2j332p>0~18:;1842'2p>00%12#5#1#5p=P%52#5#1#5p=qA63;4/22p=j1J42,J;p>2J%12#5p>0|%12#1#5#1p>051242,2;,2:,29p>0{&0}4=632p>0e%p2$0}p>0d1032p>0HP3P3P4%A2H0;p>1LP3P3%14#1#AP2H0;p>09P3P3%14#1#1#1#1#1#AP2H0;p=}P3P3%14#1#A%12#1#1#AH0;p>0^A6:;4/J2p>29A6589A6:;4/J2'Jp=cAw;429w9:p=\g034DQ0022o62g00dXS0Bp-0RA\>[\6\4g035?S0C$0vQ0Bg00VDRD#1S0D#1S0E#1S0F#1RE#1S0G#1S0H$0ERF$0wRGQ0D#5S0I$0ES0J02_GRHQ0G$0ES0K$0wRIQ0F$0ERJ$0wRK$0j\GRLfIRMfOS0LP2Q0>Q0=p,3uspRN$2KROQ0H#1RP$1HS0M,<NRQK1@PNp,3TIDRRp,2S0S0Np,2S1S0Op,2S2S0Pp,2S3S0Qp,2S4S0Rp,2S5S0Sp,2S6S0Tp,2S7S0Up,2J8S0Vp,4RSTKRSp,6canaryRTQ02P4N?1?p,2rcS0Wp,2AIS0Xp,1LRUfKS0YfMRV#pfLRWP;K2lg0368S0ZfNS0[$1mQ0236&078S0\p,6rng_fsRXPNPSPUp,4argvRYp,2P0RZp,2P1R[p,6slack0R\p,6slack1R]p,3RA0R^p,3RA1R_Q0[N<1_Q0D#AS0]fRR`fPRaP2H1ZfVRbfQRcfURdfSS0^fTReP4E7[^J>p,5geoA'S0_Q0W$2SS0`/8OS0a%1P#KRP#1S0b#1$04Rf$04#KS0c$0PS0d,<O%APS0e'B/_NS0fg0373/8OS0g%5DS0h#1S0i#1$0PS0j,<NRPQ0]Q0I#5S0k#5S0l#5S0m#AS0n+1GS0o'8S0p%AES0q-1\NS0rQ05563S0s'2S0t'2S0u'2S0v'2P1Q0aQ0vfWS0wP`Q0wfXS0xQ0wV7PePdPc1FFQRg%5E#K#m,FFREg037i,FFRhPaQ0LQ0[Q0],FFRiPV%DD#V$0>#Q#ERj,FFRkPWQ0YfJS0yPMfHS0zfGS0{Q0AQ0@Q0?Q0>Q0=Q0<Q0;p,2S8Rlp,2S9Rmp,3S10Rnp,3S11RoQ0:Q09Q08PCMO4Q07%5D$0y#Q$01#R#ES0|,FFRpPB&1uGRqP@&2k<RrF3G>P2Q0aQ0vP1Q0fQ0uf[S0}PbQ0}f\RsQ0}V7Q0xfYRtPdPgPEPhPeQ0^P`PiPcPkPaQ0LQ0[PVPWQ0YQ0yPMQ0zQ0{Q0AQ0@Q0?PlPmPnPoQ0>Q0=Q0<Q0;MO4Q0:PpQ09PqQ08PrF3G>P2Q0fQ0uP1Q0gQ0tf_S0~fZRuQ0~f`S10Q0~V7Psf]RvPtPgPEPhQ0xQ0wPbPiPdPkPeQ0^P`PcPaQ0LQ0[PVPWQ0YQ0yPMQ0zPlPmPnPoQ0{Q0AQ0@Q0?MO4Q0>PpQ0=PqQ0<PrF3G>P2Q0gQ0tP1Q0pQ0sfcS11f^RwQ11fdS12Q11V7Q10faRxPvPgPEPhPsQ0}PuPiPtPkQ0xQ0wPbPdPeQ0^P`PcPaQ0LQ0[PVPWPlPmPnPoQ0YQ0yPMQ0zMO4Q0{PpQ0APqQ0@PrF3G>P2Q0pQ0sQ0APNPRQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPSPTQ02Q0zN?1?P1AyMOQPNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPMM;o1hRMPMPM&0[T&0Z=S13+0BS14PMPMPMPMPSPMPMPGQ0y20YFhQ0I#1S15#1S16#k$1H'<R=&2d2Q13+0BRy3@X7GPMGgEz3C,sMfhS17Q11Q17fiS18Q17V7feS19ffRzfbR{PgPEPhPxQ10Q0~PiPwPkPvPsQ0}PuPtQ0xQ0wPbPdPeQ0^P`PcPlPmPnPoPaQ0LQ0[PVMO4PWPpQ0YPqQ0yPrF3G>P2Q0Y?yOQPNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPWM;o1hRWPWPWQ14PWPWPWPWPSPWPWPGA@V=yX7GPWGgEz3C,sWP1&0QVPNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPVM;o1hRVPVPVQ14PVPVPVPVPSPVPVPGQ0[?@=yX7GPVGgEz3CflS1:fgS1;Q1:fmS1<Q1:V7Q18fjR|PzPgPEPhQ19Q12Q11PiP{PkPxQ10Q0~PwPvPsQ0}PuPtQ0xQ0wPbPdPlPmPnPoPeQ0^P`PcMO4PaPpQ0LPqQ0[PrF3G>P2Q0L$0QPNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPaM;o1hRaPaPaQ14PaPaPaPaPSPaPaPGA@c=yX7GPaGgEz3CP1PNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPcM;oPcPcQ14PcPcPcPcPSPcPcPGA@`=yX7GPcGgEz:0mRcfpS1=fkS1>Q1=fqS1?Q1=V7Q1<fnS1@P|PgPEPhQ18Q17Q1;PiPzPkQ19Q12Q11P{PxQ10Q0~PwPvPsQ0}PuPtPlPmPnPoQ0xQ0wPbPdMO4PePpQ0^PqP`PrF3G>P2PNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0^M;oPePeQ14PePePePePSPePePGA@d=yX7GPeGgEz:0mReP11hRdPdPdQ14PdPdPdPdPSPdPdPGA@b=yX7GPdGgEzftS1AfoS1BQ1AfuS1CQ1AV7Q1?frS1DQ1@PgPEPhQ1<Q1:Q1>PiP|PkQ18Q17Q1;PzQ19Q12Q11P{PxQ10Q0~PwPvPlPmPnPoPsQ0}PuPtMO4Q0xPpQ0wPqPbPrF3G>P2Q0w,hRQ0xQ0xQ14Q0xQ0xQ0xQ0xPSQ0xQ0xPGA@t=yX7GQ0xGgEzP1&14tPtQ14PtPtPSPtPtPGA@u=yX7G%YtS1ECxH0C:0kttH1UfxS1FfsS1GQ1FfyS1HQ1FV7Q1CfvS1IQ1DPgPEPhQ1?Q1=Q1BPiQ1@PkQ1<Q1:Q1>P|Q18Q17Q1;PzQ19Q12Q11P{PxPlPmPnPoQ10Q0~PwPvMO4PsPpQ0}PqPuPrF3G>P2Q0}$14PsQ14PsPsPSPsPsPGA@v=yX7G%YsCxH0C:0kssH1UP1Q14-0hvPvPvPvPvPSA@w=yX7G%YvS1J62PG:2OvvJ1Rf|S1KfwS1LQ1Kf}S1MQ1KV7Q1HfzS1NQ1IPgPEPhQ1CQ1AQ1GPiQ1DPkQ1?Q1=Q1BQ1@Q1<Q1:Q1>P|Q18Q17Q1;PzQ19PlPmPnPoQ12Q11P{PxMO4Q10PpQ0~PqPwPrF3G>P2Q0~Q14+0hQ10Q10Q10Q10PSQ10Q10PGA@x=yX7GQ10I1;J1RP1&0TxPxPSPxPxPGA@{=yX7G%YxS1OCxH0C:0kxxp+01AS1Pf{S1QQ1Pp+01BS1RQ1PV7Q1Mf~S1SQ1NPgPEPhQ1HQ1FQ1LPiQ1IPkQ1CQ1AQ1GQ1DQ1?Q1=Q1BQ1@Q1<Q1:Q1>P|Q18PlPmPnPoQ17Q1;PzQ19MO4Q12PpQ11PqP{PrF3G>P2Q11$0TQ12Q12Q12PSQ12Q12PGQ19?@=yX7GQ12#YCxH0C40kP1Q19$0]Q19Q19PSQ19Q19PGA@z=yX7GQ19Ggp+01ES1Tp+01@S1UQ1Tp+01FS1VQ1TV7Q1Rp+01CS1WQ1SPgPEPhQ1MQ1KQ1QPiQ1NPkQ1HQ1FQ1LQ1IQ1CQ1AQ1GQ1DQ1?Q1=Q1BQ1@Q1<PlPmPnPoQ1:Q1>P|Q18MO4Q17PpQ1;PqPzPrF3G>P2Q1;$0]Q17Q17PSQ17Q17PGQ18?@=yX7GQ17GgP1Q18$0_Q18PSQ18Q18PGA@|=yX7GQ18#YCxH0Cp+01IS1Xp+01DS1YQ1Xp+01JS1ZQ1XV7Q1Vp+01GS1[Q1WPgPEPhQ1RQ1PQ1UPiQ1SPkQ1MQ1KQ1QQ1NQ1HQ1FQ1LQ1IQ1CQ1AQ1GQ1DQ1?PlPmPnPoQ1=Q1BQ1@Q1<MO4Q1:PpQ1>PqP|PrF3G>P2Q1>$0_Q1:PSQ1:Q1:PGQ1<?@=yX7GQ1:#YCxH0CP1Q1</LSQ1<Q1<PGQ1@?@=yX7GQ1<I1;p+01MS1\p+01HS1]Q1\p+01NS1^Q1\V7Q1Zp+01KS1_Q1[PgPEPhQ1VQ1TQ1YPiQ1WPkQ1RQ1PQ1UQ1SQ1MQ1KQ1QQ1NQ1HQ1FQ1LQ1IQ1CPlPmPnPoQ1AQ1GQ1DQ1?MO4Q1=PpQ1BPqQ1@PrF3G>P2Q1B/LSQ1=Q1=PGQ1??@=yX7GQ1=I1;P1Q1?$1KQ1?PGQ1D?@=yX7GQ1?#YCxp+01QS1`p+01LS1aQ1`p+01RS1bQ1`V7Q1^p+01OS1cQ1_PgPEPhQ1ZQ1XQ1]PiQ1[PkQ1VQ1TQ1YQ1WQ1RQ1PQ1UQ1SQ1MQ1KQ1QQ1NQ1HPlPmPnPoQ1FQ1LQ1IQ1CMO4Q1APpQ1GPqQ1DPrF3G>P2Q1G$1KQ1APGQ1C?@=yX7GQ1A#YCxP1Q1C$1JQ1I?@=yX7GQ1C61IGp+01US1dp+01PS1eQ1dp+01VS1fQ1dV7Q1bp+01SS1gQ1cPgPEPhQ1^Q1\Q1aPiQ1_PkQ1ZQ1XQ1]Q1[Q1VQ1TQ1YQ1WQ1RQ1PQ1UQ1SQ1MPlPmPnPoQ1KQ1QQ1NQ1HMO4Q1FPpQ1LPqQ1IPrF3G>P2Q1L$1JQ1H?@=yX7GQ1F61IGP1Q1N?@=yX7G,0GQ1H#Yp+01YS1hp+01TS1iQ1hp+01ZS1jQ1hV7Q1fp+01WS1kQ1gPgPEPhQ1bQ1`Q1ePiQ1cPkQ1^Q1\Q1aQ1_Q1ZQ1XQ1]Q1[Q1VQ1TQ1YQ1WQ1RPlPmPnPoQ1PQ1UQ1SQ1MMO4Q1KPpQ1QPqQ1NPrF3G>P2Q1K?@=yX7G,0GQ1K#YQ1LPXPNPSPUPYPZP[P\P]P^P_Q1kN<1_P1p+01XS1l1BPOS1m7UOQ1lPO&2@US1n/BORPQ1l%AfS1o&0SD#Q#O#K#mRfQ1lQ0h#5S1p#5S1q#5$0y$08S1r#5S1s#N#K#mRy%VD#Q#N#mR=PXPUQ1lO2Q1lPSQ1lQ1lQ1lQ1lPZPKP3&2:JS1t&0vKRJg01=MS1uPY&0ZKR}H1NH1F-0x3%ADS1v'<20xK\'<R\Q1lP^Q0]21VJY$25'8R~Q1hP[PKP3Q1tPJQ1u$0nS1tPYP}H1NH1F-0x3Q1v'<20xK]'<R]Q1hP_DG[FfEuC^C^C^p+01^S1wQ1hQ1wp+01_S1xQ1wV7p+01[S1yp+01\S1zQ1lPgPEPhQ1kQ1fQ1dPiQ1iPkQ1gQ1bQ1`Q1eQ1cQ1^Q1\Q1aQ1_Q1ZQ1XQ1]Q1[PlPmPnPoQ1VQ1TQ1YQ1WMO4Q1RPpQ1PPqQ1UPrF3G>P2Q1jQ1m7UOQ1yPOPPQ1yQ1oPfQ1yPyP=PXPUQ1yO2Q1yPSQ1yQ1yQ1yQ1yPZP\Q1yP^Q1zP[P]Q1zP_DG\~FfEuC^C^C^P1Q1z?UOPQ1zQ1oPfQ1zPyP=PXPUQ1zO2Q1zPSQ1zQ1zQ1zQ1zPZP\Q1zP^p+01]S1{P[P]Q1{P_DG\~FfEuC^C^p+01bS1|Q1{Q1|p+01cRKQ1|V7Q1xp+01`S1}Q1zPgPEPhQ1yQ1jQ1hPiQ1lPkQ1kQ1fQ1dQ1iQ1gQ1bQ1`Q1eQ1cQ1^Q1\Q1aQ1_PlPmPnPoQ1ZQ1XQ1]Q1[MO4Q1VPpQ1TPqQ1YPrF3G>P2Q1w?UOPQ1xQ1oPfQ1xPyP=PXPUQ1xO2Q1xPSQ1xQ1xQ1xQ1xPZP\Q1xP^Q1}P[P]Q1}P_DG\~FfEuC^C^P1Q1}Q1o;UfQ1}PyP=PXPUQ1}O2Q1}PSQ1}Q1}Q1}Q1}PZP\Q1}P^p+01aS1~P[P]Q1~P_DG\~FfEuC^p+01fS20Q1~Q20p+01gS21Q20V7PKp+01dRPQ1}PgPEPhQ1xQ1wQ1{PiQ1zPkQ1yQ1jQ1hQ1lQ1kQ1fQ1dQ1iQ1gQ1bQ1`Q1eQ1cPlPmPnPoQ1^Q1\Q1aQ1_MO4Q1ZPpQ1XPqQ1]PrF3G>P2Q1|Q1o;UfPKPyP=PXPUPKO2PKPSPKPKPKPKPZP\PKP^PPP[P]PPP_DG\~FfEuC^P1AUPy=PXPUPPO2PPPSPPPPPPPPPZP\PPP^p+01eS22P[P]Q22P_DG\~FfEup+01jS23Q22Q23p+01kRfQ23V7Q21p+01hS24PPPgPEPhPKQ1|Q1~PiQ1}PkQ1xQ1wQ1{Q1zQ1yQ1jQ1hQ1lQ1kQ1fQ1dQ1iQ1gPlPmPnPoQ1bQ1`Q1eQ1cMO4Q1^PpQ1\PqQ1aPrF3G>P2Q20?Uy=PXPUQ21O2Q21PSQ21Q21Q21Q21PZP\Q21P^Q24P[P]Q24P_DG\~FfEuP1PXPUQ24O2Q24Q24Q24Q24Q24PZP\Q24p+01iS25P[P]Q25P_DG\~80I^K0b80ISp+01nS26Q25Q26p+01oS27Q26V7Pfp+01lR=Q24PgPEPhQ21Q20Q22PiPPPkPKQ1|Q1~Q1}Q1xQ1wQ1{Q1zQ1yQ1jQ1hQ1lQ1kPlPmPnPoQ1fQ1dQ1iQ1gMO4Q1bPpQ1`PqQ1ePrF3G>P2PXPUQ23O2PfPfPfPfPZP\P=P[P]P=P_DG\~:0If^K0b:0IfSP11M=SP=P=P=P=PZP\p+01mS28P[P]Q28P_DG\~:0I=^K0bp+022RXQ28PXp+023RyPXV7Q27p+020R}P=PgPEPhPfQ23Q25PiQ24PkQ21Q20Q22PPPKQ1|Q1~Q1}Q1xQ1wQ1{Q1zQ1yPlPmPnPoQ1jQ1hQ1lQ1kMO4Q1fPpQ1dPqQ1iPrF3G>P2Q26/MSQ27Q27Q27Q27PZP\Q27P}P[P]P}P_DG\~80I^K0bP1&1C}P}PZP\P}P^p+021RYP[P]PYP_DG\~J0a:1B}}p+026S29PYQ29p+027S2:Q29V7Pyp+024RJP}PgPEPhQ27Q26Q28PiP=PkPfQ23Q25Q24Q21Q20Q22PPPKQ1|Q1~Q1}Q1xPlPmPnPoQ1wQ1{Q1zQ1yMO4Q1jPpQ1hPqQ1lPrF3G>P2&1CXPyPZP\PyP^PJP[P]PJP_DG\~J0a:1ByyP1&1AJPJPJPZP\PJP^p+025S2;P[P]Q2;P_DG\~Ffp+02:S2<Q2;Q2<p+02;S2=Q2<V7Q2:p+028S2>PJPgPEPhPyPXPYPiP}PkQ27Q26Q28P=PfQ23Q25Q24Q21Q20Q22PPPKPlPmPnPoQ1|Q1~Q1}Q1xMO4Q1wPpQ1{PqQ1zPrF3G>P2Q29$1AQ2:Q2:PZP\Q2:P^Q2>P[P]Q2>P_DG\~FfP1Q2>$0MQ2>PZP\Q2>P^p+029S2?P[P]Q2?P_DG\~J0ap+02>S2@Q2?Q2@p+02?S2AQ2@V7Q2=p+02<S2BQ2>PgPEPhQ2:Q29Q2;PiPJPkPyPXPYP}Q27Q26Q28P=PfQ23Q25Q24Q21PlPmPnPoQ20Q22PPPKMO4Q1|PpQ1~PqQ1}PrF3G>P2Q2<$0MQ2=PZP\Q2=P^Q2BP[P]Q2BP_DG\~J0aQ0WQ0XPUQ2BQ2@#pp+02=R~PKQ1}L1{Q04,FF$0[Q13+0BR_-0zK&0[kQ13+0BR]-0LKg038],FF$0[Q13+0BR[-02KQ03,FF$0[Q13+0BS13,lK'23CP120zP_20LP]202P[Q13,lP3Cp+02CS03Q2@Q03p+02DS04Q03V7p+02@S1|p+02AS2CP~PgPEPhQ2BQ2=Q2<PiQ2?PkQ2>Q2:Q29Q2;PJPyPXPYP}Q27Q26Q28P=PlPmPnPoPfQ23Q25Q24MO4Q21PpQ20PqQ22PrF3G>P2Q2000z_Q2100L]Q21002[Q21Q13'l3CP1Q2400L]Q24002[Q24Q13'l'2p+02GS20p+02BS22Q20p+02HS2DQ20V7Q04p+02ES2EQ2CPgPEPhQ1|Q2AQ2@PiP~PkQ2BQ2=Q2<Q2?Q2>Q2:Q29Q2;PJPyPXPYP}PlPmPnPoQ27Q26Q28P=MO4PfPpQ23PqQ25PrF3G>P2Q2300L]202f[Q13,lf'2P1202=[Q13,l=p+02KR=p+02FS23P=p+02LS25P=V7Q2Dp+02IR]Q2EPgPEPhQ04Q03Q22PiQ2CPkQ1|Q2AQ2@P~Q2BQ2=Q2<Q2?Q2>Q2:Q29Q2;PJPlPmPnPoPyPXPYP}MO4Q27PpQ26PqQ28PrF3G>P2Q26002[Q27Q13'lp+02NS26P]Q26p+02OR[$1zS2FQ26V7S2G41yP=Q25Q2DPgPEPhQ20Q23Q2EPiQ04PkQ03Q22Q2CQ1|Q2AQ2@P~Q2BQ2=Q2<Q2?Q2>Q2:PlPmPnPoQ29Q2;PJPyMO4S2HPXPpPYPqP}PrF3S2IP<P]P[p+02JS2JP[p+02PS2KP[V7Q25p+02MS2LP2G>XJ>S2MQ2IPGPGPGPGPGPG&1xGR_1?GyP_Q2A,?GS2NP_FHQ2E,?GS2OPGP_PGQ2:P_DWS2P1?GES2QPGPGP_PGQ2=P_DWS2RQ03,?GS2SPGP_PGPoP_DWS2TCiFH%5D#Q$0`#[#D$0PS2U,FFR^,?GS2VPGPGPGP_PGP~P_DWS2WQ04,?GS2XPGP_PGPmP_DWS2YQ20,?GS2ZPGPGP_Q2?,?GP_Q2C,?GPGP_PGQ2;P_DWFHS2[FHPqPGPGPGPGP_PGQ2@P_DWS2\1?GiS2]PGP_PGPlP_DWS2^Ci1?GhS2_PGPGP_Q2<,?GP_Q22,?GPGP_PGQ29P_DWFHS2`1?GgS2aPGPGPGP_PGQ2BP_DWS2b1?GkS2cPGP_PGPnP_DWS2dQ23,?GS2ePGPGP_PGQ2>P_DWS2fQ1|,?GS2gPGP_PGPJP_DWR\CiFHFHFHPX%1D$04$0=#D#S#E,FFS2hPYPqP}PrF3S2ig039`S2j$0ZS2k&0jG/TqS2l&2n>S2m$2mS2nQ0E#AS2o,FFS2pQ0JQ1vQ0JQ0i$0y#V$0=#~#RS0i#A+0K40JQ15#5$0ES1vQ1p#1S1p$04$0=$01#V#ERZQ1v00KZ40JRZ+1wS2qQ2HPXPpPYPqI1t41s>1r<}-1qrS2rQ2nQ2nQ2mPGPGPGPGPGP\Q2gP_CiQ2eQ2fQ2QPGQ2bQ2XQ2TCiFHS2TQ2VPGPGQ2\Q2OQ2YQ2D,?GQ2`FHS2`PqPGPGPGPGP_Q2NP_Q2]Q2^FHQ2_PGQ2RQ2SQ2PCiQ2aPGPGQ2WQ2cQ2dQ2ZQ2[FHFHS2[FHPyQ2hPXPqPYPrF3Q2k3vR_762WcPGQ1v01pZR\-1opS2hQ2nQ2mPGPGQ2TQ2p:1=FpS2Z,?GQ2`PqQ2[FHPyP2PXPqPYPrF3Q2k3v;6_XMGPGQ0|Q2o'<,FFS2dQ2nQ2mPGPGQ2T1?G2Q2`PqQ2[FHPyQ2hPXPqPYPrF3Q2k3v;6_XMGPGQ0|/<\,FFQ2nQ2mPGPGQ2TQ2d,?GQ2`PqQ2[FHPyP2PXPqPYPrF3Q2k3v;6_XMGQ2nQ2mQ2iQ2k3vR_'T20YFp/<\,FFQ0|01n\E]Q2ZQ0|Q2o+2iE]Q1v@1lFZ:1=FpQ1v>1kpZE]Q2nQ2r;6_eQ2I-1j<P<Q2HPXPpPYPqP}PrQ0KQ0i#5$1i#Q#AR_Q0K00K_40JR_Q2qQ2o&0jIS0i1?I_RZ'TQ0i21h<p;6Zdg005_S2Hg03:eS2I'TS2rQ2H&1g_Q2I36dg03;ES0|01f3S2Z$0jS2[Q2ZQ0|P3Q2qQ2oH0;'?RZ'TQ2[&1e_;6ZdN>1dE]Q2j&1c]+0tP<P]Q2MQ2iP7Q26P]Q2FQ2GP=Q0BQ0BQ2L764S2GP6P^PgPEPhPiQ2DQ1|Q2AQ2@P~Q2BQ2=PlPmPnPoQ29POPTPJP[P:P;P2NI0s'2XJ>WOXX6XR7Q25Q2iP7P]Q2FP=P6P^PgPEPhPiQ04Q2BQ2=Q2<Q2?Q2>Q2:PlPmPnPoPXPOPTP}P=NF2gQ2iP6p,5HSTRNP]PSP[P^PgPEPhQ20Q23Q2EPiQ04PkQ03Q22Q2CQ1|Q2AQ2@P~Q2BQ2=Q2<Q2?Q2>Q2:PlPmPnPoQ29Q2;PJPyPXPYP}P=POPTQ1Y-2f}1TGkPQQ2JQ2KPYQ04Q03POP2K1@XK3Q2720YFgRXQ0W$2eS27Q1r#1$08$0A$0A#mRyQ0`Q0`Q1s$08$0A$0A#m'8S1s40rS1rQ0]Q0n+1bS23Q05Q0]'dS20Q0n#ZQ05Q0o'd[[S2iQ0]#ZRZg03<1R_Q0]Q0n<1a4UWTS0nQ0o#Z\_^TZS2FQ0q-1`NS2M%ZNQ0q#ZQ0r#Z[[S0rQ0]Q0H#AR\+1bS0HQ20%Z\Q05Q0]01G\S0q'd[[S20Q0]@1a\4V_XTZS2qQ0q#Z\_^TZS2`g00ViRZQ1t$0nR_$0nR\$0n-0p320p3\20p3_Q1u-0p3619361936193g03<M+2c&0ZZS1u3w&0vZS1tP3&2b3S2dP4P32173:S2TP;Q2dH0qH0q&2a3S2h&2`3RZ%ayQ0I-0o3R_5eZ216Z8R\5XZ&1u7S0IPZP3Q0h-0o3S0hQ0d#aS2c'|Q0e#aS2W'rg03=9S2a20o3DS2PH0W-0UZQ0IPZPZP_Q2WQ0hCtQ0IPZPZQ2PQ0j#aS2SQ0]#aS2RQ0m$0E61]3S0mCtS2_Q0IQ05-1[3S2^Q2PQ0M#aS2]'|R_5eZQ2R>1]3FS2R-15_-0UZ5XZC`C`C`C`Q06-2^ZS06P2P;Q2Hg006?S2N'TQ2H22]2;Q2N36dQ05>2\34H2[S2NbEbFbGX;3X>3XW3XPAS2YB0ry;:Q0d,<;Q0e'B/_4Q0e>0:9:Q0jQ0o60::S2OQ0M,<9S2\#ZQ2\Q0q'd'2[[[[^;3^>3^W3^PAS2VP2Q1sQ0`POPNP5Q24p,3BOTS2Xp,5USPHIS2bO8b@bAbBbCbQbVb0-10QRyI0DPQAyYO2XK3Q1iPXPyI0DPQg03=`S2Q,B2,8OXK3Q27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tP32173;S2fP4Q2dH0qS2eQ2hPZ216Z9S2gP3Q2PQ2c'|Q2W'rQ2aQ0D-0o3S0DH0W-0UZ=XZ\5XZQ0IQ2PQ0DQ2]'|S2aQ0k#1S0k$04S2c#k#ERY#a'r5eZC`Q06Q2NbEbFbGX;3X>3XPAXUAQ0d,<2Q0e'B/_4=C;:Q0M,<;/BY,84[^;3^>3^PA^UAP2Q0b$08$08$0A#mRY/8OS0bQ0t'2S2sQ0aPNPOQ0_O5b@bAbBbCb0Q2Q,BQ,8OePXPyI0DQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1t21734S2QQ2hPZ216Z:Q2g%aYQ2P5eZS2t=XZ\5XZ5XZQ0IQ2tC`Q06Q2NbEbFbGX;3XPAXUAX`AB0rY2:9C4;18Y4[^;3^PA^UA^`AP2Q0tQ0fQ0aPOQ0_O5b@bAbBbCb0Q0gePQQ0o,d2XK3Q27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tQ2QQ2hPZQ2_Q0IQ0m-15_-0UZC`Q06Q2NbEbFbGX;3Q0jQ0o60:2Q0M,<4S2_Q0o'd[^;3P2PNQ2bO2b@bAbBbCb0Q0o,dQePXPyI0DQ13,l}Q14-0h}P2Q1UH13Q1ePfp,6ASHENVPUP]%p=Q2JP}Q28O6Q1BQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tQ2eQ2hPZQ2PQ0D5eZR}Q0IP}C`Q06Q2NbEbFbGX;3X>31824184;[^;3^>3P2PO&2ZSR}p,7RSTK_loO3b@bAbBbCb018}OePQ&2YSR},82XK3Q27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tQ2eQ2hPZQ0D9eZ_R_Q0IP_C`Q06Q2NbEbFbGX;3X>3Q0M>0:24Q2_/8;[^;3^>3P2P}PNp,7RSTK_hiO3b@bAbBbCb018Q}ePXPyI0DQ1GPQQ2J1B2O7UOXK3P]POQ1mPO1BQOS2JPwQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tQ2eQ2hQ2PQ2P5eZS0MPZQ2PQ2aQ2P'rQ2PQ0DQ2S'|Q2P'r'|S28Ct5XZQ06Q2NbEbFbGX;3X>31822S2QQ2_/B2,<2Q0j,<4/B2,<2S0j412^;3^>3P2PNPOO2S2tb@bAbBbCb0K1YPXPyI0DPbQ09Q0yQ0ANn2XK2WP7Q0BQ0BQ26764P6P^PgPEPhPiP]Q2CQ1|Q2AQ2@P~Q2BPlPmPnPoQ2:POPTQ2;Q2KP:P;P2NI0s'2p+02TS2gP;p+02SS2uP:p+02RS2vP4E7[^J>]O^X6P2Q0BQ2GP^PgPEPhPiQ2DQ1|Q2AQ2@P~Q2BQ2=PlPmPnPoQ29POPTPJP[P;P2NG0l'2P1Q0BQ2676;P^PgPEPhPiP]Q2CQ1|Q2AQ2@P~Q2BPlPmPnPoQ2:POPTQ2;Q2KP:P4NG0lQ2gP:Q2uP9Q2vP;E7P2Q0BQ2K769Q0Bp+02QS2;Q0BP^PgPEPhPiQ2LQ2EQ04Q03Q22Q2CQ1|PlPmPnPoQ2=POPTQ2?Q2gP0P8NG0lp+02XS2?P4p+02WS2=P?p+02VS2EP5E7[WOP^PgPEPhPiQ25Q04Q03Q22Q2CQ1|Q2APlPmPnPoQ2<POPTQ2>Q2uP5P9NG0lQ01PGQ0{P^PgPEPhQ0<Q0;Q0:Pip+02_S2:Q09Q08PCQ07PBP@P?P0Q2=Q2Ep+02US2BQ2gQ2uQ2vPlPmPnPoP5P8P9P:MO4P;&2R^R~P4PqP2PrF321f33R]20ROXQ1p#5#ES1p,<jS2@-0RjRJ&0Z]S2G5w]S293wRyP=P2P=P2&0Q2R=&074R}Q0J$0wR_Q0J00Y2Q15#A'_$2QRfPG20i94RAP[P4C=[]1Ay2OXR[&0X2RY20?2TR\PMp+02fS15E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLG,0GXSG,0GXYG,0GXfGQ2?Q2uQ2=P?Q2EP5E7P2PMP^PgPEPhQ0<Q0;Q0:Pip+02aS2DQ09Q08PCQ07PBP@P?P0p+02YS2wQ2?Q2=Q2EQ2BQ2gPlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2LP2Q2LP2P=P}PGPAQ2;P4C=\f^1_P[PYP\Q0Yp+02hS2LE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLG,0GXSG,0GXYG,0GQ01PGQ0yP^PgPEPhQ0=Q0;Q0:Pip+02bS2xQ09Q08PCQ07PBP@P?P0p+02ZS2yQ2wQ2?Q2=Q2EQ2BPlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ26P2Q26P2P=P}PGPAQ2vP4C=\f^1_P[PYP\PWp+02iS26E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLG,0GXSG,0GXYGp+02\S2zQ2=p+02[S2{PCQ2yPBE7P2PWP^PgPEPhQ0?Q0;Q0:Pip+02dS2|Q09Q08PCQ07PBP@P?P0Q2zQ2{Q2yQ2wQ2?Q2=PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2KP2Q2KP2P=P}PGPAQ2gP4C=\f^1_P[PYP\Q0[p+02kS2KE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLG,0GXSG,0GQ01PGPVP^PgPEPhQ0@Q0<Q0:Pip+02eS2}Q09Q08PCQ07PBP@P?P0p+02]S2~Q2zQ2{Q2yQ2wQ2?PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2;P2Q2;P2P=P}PGPAQ2BP4C=\f^1_P[PYP\Q0Lp+02lS30E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLG,0GXSGp+02`S31Q2{Q2:Q0;p+02^S32Q09E7P2Q0LP^PgPEPhQ0{Q0>Q0:Pip+02gS33Q09Q08PCQ07PBP@P?P0Q2:Q32Q2~Q2zQ2{Q2yPlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2uP2Q2uP2P=P}PGPAQ2=P4C=\f^1_P[PYP\Pcp+02nS34E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLG,0GQ01PGPaP^PgPEPhQ0zQ0?Q0;PiQ2LQ09Q08PCQ07PBP@P?P0Q31Q2:Q32Q2~Q2zQ2{PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2gP2Q2gP2P=P}PGPAQ2?P4C=\f^1_P[PYP\P`p+02oS2?E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GXLGQ2|Q2:p+02cS2gQ0?Q2xQ0=E7P2P`P^PgPEPhQ0yQ0AQ0=Pip+02jS35Q09Q08PCQ07PBP@P?P0Q2xQ2DQ31Q2:Q32Q2~PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2EP2Q2EP2P=P}PGPAQ2yP4C=\f^1_P[PYP\Pep+031S2EE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIG,0GQ01PGQ0^P^PgPEPhQ0YQ0{Q0>PiQ2KQ0:Q08PCQ07PBP@P?P0Q2gQ2xQ2DQ31Q2:Q32PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2=P2Q2=P2P=P}PGPAQ2{P4C=\f^1_P[PYP\Pdp+032S2{E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GXIGQ2LQ2gQ33Q0zQ15Q0AE7P2PdP^PgPEPhPVPMQ0@Pip+02mS2=Q0<Q08PCQ07PBP@P?P0Q2}Q2|Q2gQ2xQ2DQ31PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2wP2Q2wP2P=P}PGPAQ2~P4C=\f^1_P[PYP\Q0wp+034S36E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHG,0GQ01PGPbP^PgPEPhQ0[Q0yQ0APiQ34Q0=Q09PCQ07PBP@P?P0Q15Q2}Q2|Q2gQ2xQ2DPlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2yP2Q2yP2P=P}PGPAQ32P4C=\f^1_P[PYP\Q0xp+035S32E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GXHGQ30Q33Q2KPWQ35Q0yE7P2Q0xP^PgPEPhPaPWQ0zPip+030S2yQ0?Q0;PCQ07PBP@P?P0Q2LQ33Q15Q2}Q2|Q2gPlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2zP2Q2zP2P=P}PGPAQ31P4C=\f^1_P[PYP\Pup+037S2zE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDG,0GQ01PGPtP^PgPEPhPcPVPMPiQ2EQ0@Q0<Q08Q07PBP@P?P0Q26Q2LQ33Q15Q2}Q2|PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2~P2Q2~P2P=P}PGPAQ2DP4C=\f^1_P[PYP\Q0}p+038S2~E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GXDGQ2yQ2KQ2?PaQ34Q0[E7P2Q0}P^PgPEPhQ0^Q0LQ0YPip+033S37Q0{Q0>Q0:Q07PBP@P?P0Q2KQ35Q26Q2LQ33Q15PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2:P2Q2:P2P=P}PGPAQ2gP4C=\f^1_P[PYP\Pvp+03:S2:E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?G,0GQ01PGPsP^PgPEPhPePaPWPiQ36Q0zQ0?Q0;PCPBP@P?P0Q30Q2KQ35Q26Q2LQ33PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ31P2Q31P2P=P}PGPAQ2|P4C=\f^1_P[PYP\Pwp+03;S2|E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GX?GQ36Q2?Q37PeQ2{P`E7P2PwP^PgPEPhPbP`Q0[Pip+036S31Q0yQ0AQ0=Q09PBP@P?P0Q34Q2=Q30Q2KQ35Q26PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2xP2Q2xP2P=P}PGPAQ15P4C=\f^1_P[PYP\Q10p+03=S2xE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=G,0GQ01PGQ0~P^PgPEPhQ0wQ0^Q0LPiQ2zQ0YQ0{Q0>Q0:Q07P@P?P0Q2?Q34Q2=Q30Q2KQ35PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2gP2Q2gP2P=P}PGPAQ33P4C=\f^1_P[PYP\Pxp+03>S33E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GX=GQ2~Q37Q2zQ0xQ31PbE7P2PxP^PgPEPhPtPdPcPip+039S2gPVPMQ0@Q0<Q08P@P?P0Q2EQ2yQ2?Q34Q2=Q30PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2}P2Q2}P2P=P}PGPAQ26P4C=\f^1_P[PYP\Q11p+03@S2}E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<G,0GQ01PGP{P^PgPEPhPuPbP`PiQ2:Q0[Q0yQ0AQ0=Q09PBP?P0Q2{Q2EQ2yQ2?Q34Q2=PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ15P2Q15P2P=P}PGPAQ35P4C=\f^1_P[PYP\Q12p+03AS35E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GX<Gp+03<S15Q2zQ2|PsQ2:PuE7P2Q12P^PgPEPhPsQ0xPePiQ15PaPWQ0zQ0?Q0;PCP?P0Q36Q37Q2{Q2EQ2yQ2?PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2LP2Q2LP2P=P}PGPAQ30P4C=\f^1_P[PYP\Pzp+03CS2LE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:G,0GQ01PGQ19P^PgPEPhPvPtPdPiQ2xPcPVPMQ0@Q0<Q08P@P0Q32Q36Q37Q2{Q2EQ2yPlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ26P2Q26P2P=P}PGPAQ2=P4C=\f^1_P[PYP\Q1;p+03DS2=E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GX:GQ2}Q2|p+03?S26Q10Q33PwE7P2Q1;P^PgPEPhQ0~Q0}Q0wPiQ26Q0^Q0LQ0YQ0{Q0>Q0:Q07P0Q2zQ31Q32Q36Q37Q2{PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ2KP2Q2KP2P=P}PGPAQ2?P4C=\f^1_P[PYP\Q18p+03FS2KE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9G,0GQ01PGQ17P^PgPEPhQ10PsQ0xPiQ2}PePaPWQ0zQ0?Q0;PCP?Q2~Q2zQ31Q32Q36Q37PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ30P2Q30P2P=P}PGPAQ2yP4C=\f^1_P[PYP\P|p+03GS2yE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GX9GQ2=Q26Q2LQ12p+03BS30P{E7P2P|P^PgPEPhP{PwPuPiQ30PbP`Q0[Q0yQ0AQ0=Q09PBQ2:Q2gQ2~Q2zQ31Q32PlPmPnPoP5P8P9P:MO4P;P~P4PqP2PrF3PyQ34P2Q34P2P=P}PGPAQ2{P4C=\f^1_P[PYP\Q1:p+03IS34E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8G,0GQ01PGQ1>P^PgPEPhQ11Q0~Q0}PiQ2LQ0wQ0^Q0LQ0YQ0{Q0>Q0:Q07Q2|Q2:Q2gQ2~Q2zQ31PlPmPnPoP0P8P9P:MO4P;P~P4PqP2PrF3PyQ2?P2Q2?P2P=P}PGPAQ37P4C=\f^1_P[PYP\Q1<p+03JS37E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GX8Gp+03HS2?Q2LQ2yQ17Q2KPzE7P2Q1<P^PgPEPhQ19PxPvPip+03ES38PtPdPcPVPMQ0@Q0<Q08Q2xQ15Q2|Q2:Q2gQ2~PlPmPnPoP@P8P9P:MO4P;P~P4PqP2PrF3PyQ2EP2Q2EP2P=P}PGPAQ32P4C=\f^1_P[PYP\Q1Bp+03LS2EE;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6G,0GQ01PGQ1@P^PgPEPhPzP{PwPiQ2KPuPbP`Q0[Q0yQ0AQ0=Q09Q33Q2xQ15Q2|Q2:Q2gPlPmPnPoPBP5P9P:MO4P;P~P4PqP2PrF3PyQ2{P2Q2{P2P=P}PGPAQ31P4C=\f^1_P[PYP\Q1=p+03MS31E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GX6GQ2EQ2yp+03KS2{Q1:Q37P|E7P2Q1=P^PgPEPhQ17Q12Q10PiQ2?PsQ0xPePaPWQ0zQ0?Q0;Q2}Q26Q33Q2xQ15Q2|PlPmPnPoPCP?P9P:MO4P;P~P4PqP2PrF3PyQ36P2Q36P2P=P}PGPAQ2~P4C=\f^1_P[PYP\Q1Dp+03OS36E;D9E:X2L,0LX3I,0IX4H,0HX5G,0GQ01PGQ1?P^PgPEPhQ18Q19PxPiQ34PvPtPdPcPVPMQ0@Q0<Q35Q2}Q26Q33Q2xQ15PlPmPnPoQ08P@P8P:MO4P;P~P4PqP2PrF3PyQ32P2Q32P2P=P}PGPAQ2gP4C=\f^1_P[PYP\Q1Gp+03PS2gE;D9E:X2L,0LX3I,0IX4H,0HX5GQ2gQ2{Q36Q1=p+03NS32Q1@E7P2Q1GP^PgPEPhQ1>Q1;Q11PiQ2{Q0~Q0}Q0wQ0^Q0LQ0YQ0{Q0>Q2LQ30Q35Q2}Q26Q33PlPmPnPoQ0:Q07P0P:MO4P;P~P4PqP2PrF3PyQ2zP2Q2zP2P=P}PGPAQ2|P4C=\f^1_P[PYP\Q1Cp+03RS2zE;D9E:X2L,0LX3I,0IX4H,0HQ01PHQ1AP^PgPEPhQ1:Q17Q12PiQ2EQ10PsQ0xPePaPWQ0zQ0?Q2=Q2LQ30Q35Q2}Q26PlPmPnPoQ0;PCP?P9MO4P;P~P4PqP2PrF3PyQ2~P2Q2~P2P=P}PGPAQ15P4C=\f^1_P[PYP\Q1Ip+03SS15E;D9E:X2L,0LX3I,0IX4Hp+03TS2~Q36Q15Q1AQ2zQ1DE7P2Q1IP^PgPEPhQ1@P|PzPiQ32P{PwPuPbP`Q0[Q0yQ0AQ2KQ38Q2=Q2LQ30Q35PlPmPnPoQ0=Q09PBP5MO4P;P~P4PqP2PrF3PyQ2:P2Q2:P2P=P}PGPAQ33P4C=\f^1_P[PYP\Q1Fp+03US2:E;D9E:X2L,0LX3I,0IQ01PIQ1LP^PgPEPhQ1BQ1>Q1;PiQ36Q11Q0~Q0}Q0wQ0^Q0LQ0YQ0{Q2yQ2KQ38Q2=Q2LQ30PlPmPnPoQ0>Q0:Q07P0MO4P:P~P4PqP2PrF3PyQ2|P2Q2|P2P=P}PGP8P4Q26P4DI\f^1_P[PYP\Q1Hp+03VS26E;D9E:X2L,0LX3Ip+03XRAQ15p+03WS2|Q1FQ26Q1IE7P2Q1HP^PgPEPhQ1?Q1<Q18Pip+03QS2LQ19PxPvPtPdPcPVPMQ34Q2?Q2yQ2KQ38Q2=PlPmPnPoQ0@Q0<Q08P@MO4P8P~P4PqP2PrF3PyQ2xP2Q2xP2P=P}PGP0P4Q35P4DI\f^1_P[PYP\Q1QPAE;D9E:X2L,0LQ01PLQ1NP^PgPEPhQ1DQ1@P|PiQ2zPzP{PwPuPbP`Q0[Q0yQ37Q34Q2?Q2yQ2KQ38PlPmPnPoQ0AQ0=Q09PBMO4P5P~P;PqP2PrF3PyQ33P2Q33P2P=&07;PGP?P4Q30P4DI\f^1_P[PYP\Q1Kp+03YS30E;D9E:X2Lp+03\S33Q2|p+03[R}Q1Kp+03ZS2KQ1NE7P2Q1KP^PgPEPhQ1AQ1=Q1:PiQ2~Q17Q12Q10PsQ0xPePaPWQ2EQ2{Q37Q34Q2?Q2yPlPmPnPoQ0zQ0?Q0;PCMO4P?P~P9PqP2PrF3PyQ2}P2Q2}P2P=&079PGPBP4Q2=P4DI\f^1_P[PYP\Q1SP}E;D9E:P1Q1MP^PgPEPhQ1CQ1?Q1<PiQ2:Q18Q19PxPvPtPdPcPVQ31Q2EQ2{Q37Q34Q2?PlPmPnPoPMQ0@Q0<Q08MO4P@P~P8PqP4PrL1TPyQ35P4Q35P4Q0\PGQ07P4Q38P4DI\f^1_P4POPXP4P4PTQ1UQ33I0\H113C,s4J1Sp+03`S0\P}p+03_R\Q1Pp+03^S35Q1SE7P2Q1UP^PgPEPhQ1LQ1GQ1BPiQ2|Q1>Q1;Q11Q0~Q0}Q0wQ0^Q0LQ36Q32Q31Q2EQ2{Q37PlPmPnPoQ0YQ0{Q0>Q0:MO4Q07P~P0PqP:PrL1TP>P^PgPEPhQ1FQ1AQ1=PiPAQ1:Q17Q12Q10PsQ0xPePaQ2gQ36Q32Q31Q2EQ2{PlPmPnPoPWQ0zQ0?Q0;MO4PCP~P?PqP9PrF3Q38>0Gy8S17Q38PGQ0:P4Q34P4DI\f^1_P8POPXP8P8PTQ1YQ0\'bGn-0<@,s881Q8S38'2p+03dRYP\p+03cR[Q1Tp+03bR=P4E7[XJ>PyQ2=P9Q2=P9PGQ09P4Q2?P4DI\f^1_P9POPXP9P9PTQ1W/b\Gn-0<?,s9J1SP1Q17Q38PYP\P[Q1TP=P^PgPEPhQ1NQ1IQ1DPiQ2KQ1@P|PzP{PwPuPbP`Q2zQ2LQ2gQ36Q32Q31PlPmPnPoQ0[Q0yQ0AQ0=MO4Q09P~PBPqP5PrF3E7P2Q2y>0Gy0Q2?PGQ0=P4Q2EP4DI\f^1_P?POPXP?P?PTQ1[/b[Gn-0<C,s?81Q?P1Q3401P@Q08PGQ0>P4Q31P4DI\f^1_P@POPXP@P@PTQ1]/bYGn+0<,s@p+03hS31P[p+03gR@Q1Xp+03fR?P^PgPEPhQ1SQ1NQ1IPiQ35Q1DQ1@P|PzP{PwPuPbQ26Q2:Q2~Q15Q2zQ2LPlPmPnPoP`Q0[Q0yQ0AMO4Q0=P~Q09PqPBPrF3E7P2Q2{Q07+1PQ0;PGQ0AP4Q2gP4DI\f^1_PCPOPXPCPCPTQ1_/b@Gn+0<,sCP1Q08$0QQ0<PGQ0{P4Q2LP4DI\f^1_Q08POPXQ08Q08PTQ1aQ31'bGn+0<p+03lS08P@p+03kRyQ1\p+03jS1\P^PgPEPhQ1WQ1SQ1NPiP=Q1IQ1DQ1@P|PzP{PwPuQ2KQ30PAQ2|Q26Q2:PlPmPnPoPbP`Q0[Q0yMO4Q0AP~Q0=PqQ09PrF3E7P2Q0:$0QQ0?PGQ0yP4Q2~P4DI\f^1_Q0;POPXQ0;Q0;PTQ1c/byGn+0<P1Q0@$07PGQ0YP4Q2:P4DI\f^1_Q0<POPXQ0<Q0<PTQ1eQ08'bGnp+040S0<Pyp+03oR0Q1`p+03nS1`P^PgPEPhQ1[Q1WQ1SPiP?Q1NQ1IQ1DQ1@P|PzP{PwQ35p+03]S2:Q33P}Q2KQ30PlPmPnPoPuPbP`Q0[MO4Q0yP~Q0APqQ0=PrF3E7P2Q0{$07PGQ0[P4PAP4DI\f^1_Q0?POPXQ0?Q0?PTQ1g/b0GnP1PGQ0LP4Q30P4DI\f^1_Q0@POPXQ0@Q0@PTQ1iQ0<I0\H11p+044S0@P0p+043RAQ1dp+042R9P^PgPEPhQ1_Q1[Q1WPiQ1\Q1SQ1NQ1IQ1DQ1@P|PzP{P=p+03aS1dQ0\P\Q35Q2:PlPmPnPoPwPuPbP`MO4Q0[P~Q0yPqQ0APrF3E7P2PGPcP4P}P4DI\f^1_Q0zPOPXQ0zQ0zPTQ1kPAI0\H11P1AyMOXPMPMPTQ1lQ0@I0\p+048S0APAp+047R_Q1hp+046S1hP^PgPEPhQ1cQ1_Q1[PiQ1`Q1WQ1SQ1NQ1IQ1DQ1@P|PzP?p+03eRfPYP[P=Q1dPlPmPnPoP{PwPuPbMO4P`P~Q0[PqQ0yPrF3E7P2Q0Y?yOXPWPWPTQ1yP_I0\P1&0XVPVPTQ1zQ0AH1Op+04<R=P_p+04;R[Q1{p+04:RYP^PgPEPhQ1gQ1cQ1_PiP9Q1[Q1WQ1SQ1NQ1IQ1DQ1@P|Q1\p+03iS1{Q31P@P?PfPlPmPnPoPzP{PwPuMO4PbP~P`PqQ0[PrF3E7P2Q0L$0XPaPTQ1xP[H1OP120?cTQ1}/b=p+04@R}P[p+04?R\Q1~p+04>S1~P^PgPEPhQ1kQ1gQ1cPiQ1hQ1_Q1[Q1WQ1SQ1NQ1IQ1DQ1@Q1`p+03mS31Q08PyQ1\Q1{PlPmPnPoP|PzP{PwMO4PuP~PbPqP`PrF3E7P2Q0^00?T1bK\P6P}p+04DS1\P\p+04CS08P2p+04BR}P^PgPEPhQ1yQ1kQ1gPiPYQ1cQ1_Q1[Q1WQ1SQ1NQ1IQ1DP9p+041S1dQ0<P0Q1`Q31PlPmPnPoQ1@P|PzP{MO4PwP~PuPqPbPrF3E7Xe6P3PX20RO2Q295w]@0G?bXK3PVPQQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ0HQ20Q2qQ2`Q2YQ2VP2Q1sQ0`POPNP5Q2:Q2XQ2bO8b@bAbBbCbQbVb0-10QJ1<20ROQR?Q295w]Ry@0GfdP3PXQ0w?yO2XK3PBPQQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ0HQ20Q2qQ2`Q2YQ2VP2Q1sQ0`POPNP5Q35Q2XQ2bO8b@bAbBbCbQbVb0-10QJ1<AybOQPGP~P^Q2UQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ0HQ20Q2qQ2`Q1uQ1tQ2dQ2hQ2^Q2U#aR55eZQ2R-155-0UZ5XZQ06Q2NbEbFbGQ2U#ZQ2UQ0q'd'2P2b@bAbBbCbQbVb0Q05,T342NH2MA6G^~PGP^p+04GS0qP}p+04FS2RQ1\p+04EP^PgPEPhQ1wQ1jQ1fPip+04=S1fQ1bQ1^Q1ZQ1VQ1RQ1MQ1HQ1Cp+045S1CQ0@PAP9Q1dQ0<PlPmPnPoQ1?Q1<Q18Q19MO4PxP2PvPqPtPrF3E7XMGP]Q0W02LNR}P?Q29PO&1>?R5&0~?RBPQH00RX%1D#Q#P#N$0=#D$0PS19&0SD#q#P#K$0`#ES18,_B5j5Q2@,_B9j5jQ0W@1M5Bg01<NS1<P5PBQ1<Q1o'<S1?H00'J42JQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tQ2eQ2hQ0MQ2aQ2a5eZ5XZQ06Q2NbEbFbGX;3X>3Q2QQ2_Q2_412^;3^>3Q2tb@bAbBbCb0PXe403P]P}PJQ2GPO&1>JRX&0~JRfPQH00Q19Q18,_f5jXS19Q2@,_f9jXjRQQ0W@1MXfQ1<PXPfQ1?H00'JS1?'JS1<'JQ19Q1<Q1?1_jjQ2@Q2@'_1T3jQ2@,T3H13PQe603Q40N40N20t]}J0gJ0gB0O]}yQ0WPNPRQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UPSPTp,5USP16S1<p,5USPLOS19Q2bQ0VQ02Q1{PtPyP@P2P:PVNI2IPNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPtM;o1hRtQ1E3CP1PNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPuM;o%Yu:0mRup+04IQ1\p+04HR@Q2RQ0qP^PgPEPhQ1}Q1zQ1lPiP\Q1iQ1eQ1aQ1]Q1YQ1UQ1QQ1LP_Q1hQ1CQ0@PAP9PlPmPnPoQ1GQ1BQ1>Q1;MO4Q11P^Q0~PqQ0}PrF3E7P2PNQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPsM;oQ1J:0mRvP11hRw%Ywp+04MRAP@p+04LR@p+04Jp+04KRSP^PgPEPhPPQ1}Q1zPiQ08Q1lQ1iQ1eQ1aQ1]Q1YQ1UQ1QP[PYp+049S08Q0AP_Q1hPlPmPnPoQ1LQ1GQ1BQ1>MO4Q1;P^Q11PqQ0~PrF3E7P2Q10,hRQ1Op+04PR_PSp+04OS1hPAp+04NR}P^PgPEPhQ21PKQ1xPiQ2RQ1yQ1kQ1gQ1cQ1_Q1[Q1WQ1SQ1~Q1fP=P[PYQ08PlPmPnPoQ1NQ1IQ1DQ1@MO4S0AP|P^PzPqP{PrF3RQP<PSp+04QS1JP@P_P}Q1hP2E7XJ>S0VPQQ0AP|%5D$0y#Q$01#D#E,FFS0UPzPqP{PrF3S0TQ2kQ2lQ2nQ2pQ0JQ05Q0JQ0E#kR_#1#K$0AS0E#A+0K40JQ1v%A_R_Q1v00K_40JR_+1wS0JQ0AP|P^PzPqI1t41s>1r<{-1qrS2pQ2nQ2nQ2mP^PgPEPhQ24PPQ1}PiQ0qQ1zQ1lQ1iQ1eQ1aQ1]Q1YQ1UP\Q1~Q1fP=P[PYPlPmPnPoQ1QQ1LQ1GQ1BMO4S1BQ1>Q0UQ1;PqQ11PrF3Q2k3vS0U762WcPGQ1v01p_R\-1o^Q2nQ2mQ1BQ1>P2Q1;PqQ11PrF3Q2k3vQ0U36XMGS0UPGQ2U/<\,FFQ0UQ2nQ2mQ0TQ2k3vS2m'T20YF^/<\,FFQ2U01n\E]Q1v@1lF_:1=F^Q1v>1k^_E]Q2nQ2pQ2m36e21j<QP<Q0AP|P^PzPqP{PrQ0KQ0E#5$1i#Q#ARQQ0K00KQ40JRQQ0JQ2oQ0i1?IQR_'TQ0i21h<^;6_dQ2rQ2H&1gQQ2I36dQ2[Q2ZQ0|P3Q0JQ2oH0;'?R_'TQ2[&1eQ;6_dN>1dE]Q2j&1cS+0tP<PSQ0]@2HASQ0VQ0TQ0WQ0XPNPRQ1<Q19Q2bPTPAPUP@PSP^Q21PKQ1xPiQ2RQ1yQ1kQ1gQ1cQ1_Q1[Q1WQ1SQ1~Q1fP=P[PYQ08PlPmPnPoQ1NQ1IQ1DQ1@P|PzP{Q07P4Q0WQ0XPUPS%pAR|P@P9P{PyP0PCPbQ0WQ0XPUPSP|P@P9P0L2G&2EUR0Q0d'<Q1n'_R9Q1nQ0e+1\S0dQ05563RCQ1nQ0o'8RYQ0`Q16#E'B/80R[Q0`Q1q#1#[#E'<,80R0'2R=&0}|&2DUR|&0v3&2CU+1Vg03>a$2B+2Ag03?W&2?URU'8Q2c$0|$05#K#mQ0`60:U3CRU3jI0{P1P9PCPYP=%p}00e|PUI0{Q0WQ0WQ0X+2>RKQ1hQ0`Q0e'<R<&1>2R_&0~2RQ/B_RFJ06XN]>0O]yP2PCPYP=Q1J#p00e|PUI0{P1PCp+04R$0d?j|U9CY=Q0WPKp+04SP<P_PFJ06XN]>0O]yP2p+04U$0d?j|U9CY=P1PYp+04V#p00e|=C=UQ0WPKp+04WP<P_PFJ06XN]>0O]yP2p+04Y#p00e|=C=UP1P=p+04Z$0d?j|UQ0WPKp+04[P<P_PFJ06XN]>0O]yP2p+04]Ry$0d?j|UP]Q0WPKp+04^RUP<P_PFJ06XN]RFP?Q29PKPyP<POQ2JI0fQ0CQ0CQ0C@0@2US29&2=2RU/8OQ2J,<OR?&2<2,<US1J'83CWM'0PKPyQ0`Q0F#AR|g03@OS0F,BO+0cQ2J-0c|I0f'JP<POP?Q0oH00B0@]2KS2J18_O18?Q3CXN],0]Q0C&2;;@2F42p+04`40@R1184O1<42R\,8?3CXb3$0HX[3$0HXa3$0H'JQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1nQ0e+1`S1hQ1n#ZQ0e#ZQ0d#Z[[S0dQ1uQ1tP3Q2fP4Q2TH0qQ2hPZPZQ2PQ2WQ0DCtR?Q0IPZPZQ0hQ2SQ0mCtQ0IPZQ0DQ0hQ2]'|Q0D'rQ0mCt9XZ?C`C`Q06Q2NbEbFbGX;3X>3XW3Q0e>0:24Q2OQ0e,<;Q2\/B:Q0o60::80r:[[^;3^>3^W3P2PNPOQ0`Q2XQ2bO5b@bAbBbCbQb0403403Q0WPKPyP<P51BB5J06eP]PFPJQ2GPKPyP<PjQ2@/BjRBI0fQ0CQ0CQ2918Uj1<jBRUQ1J'83CWM'0PKPyQ0`Q0F,Bj-0c|20c|BI0f'JP<PjPUQ0oH00Q2J18_j18UQ3CXN]RQ,0]S2J184j18U\5C1Xb3$0HX[3$0HXa3$0HS0o'JQ2JQ0oP]PQPJB0@]JKPXPjPUPfH00S0Fp,6DRV_CIPJQ05/dRRQQ0c#A,dRRRQ1oQ0G#5#qR1#1$04#K+1LS1o=6]JR\%VD#O#V#Q#N&0SD#q#N#K#mR_+09S0G=6]JRBA6]JJR|P]%DD#V$01#q#ER5Q1p,<5+0RS0cPJP]%1D#[#Q#V#S0095S05PJP]%1D#[#Q$01#N%DD#V#q$01#ER5+09S0`PJP]%1D#[$08%DD#V#Q$0>#E'}S0CPJP]%~D#[#K%kD#R#D#S#S#E'}S29PJP]%VD#O#O#R#OQ18+09S18PJP]%~D#O#P#N%kD#R#P$05$01+0^S1JPJP]%~D#O#P#S%kD#R#P$0=$05+0^S2bPJP]%~D#O#O%kD#R#P#P$05#E'}S2XPJP]%~D#O$0`%kD#R#P#V#R#E'}S2OPJP]%~D#O$0`#S%kD#R#P#V#D+0^S2\PJP]%1D#[$08#[%DD#S#P#D+0^S0ePJP]%1D#q#K$01%DD#S#P$0>#E'}S0mPJP]%1D#q#K#[#N&0SD#N$0=#R#R#A+09S2]PJP]%1D#[#P#R%DD$05#S$0>#E'}S0hPJP]&0|D$05#D#K#S%ND$0>#~#R#A+09S0IPJP]%1D#q#N#D#N&0|D#O#S#[#O$0P+09S2SPJP]Q0k#5#N$0>#[%DD#O#N#V+0^S0kPJP]%51&04D$05#P#S#E'}S2WPJP]&0SD$0=#Q#D#S-1L5S2TPJP]Q0l#D#S#K/}_S0lPJg03AIH29FcFcFcFcFcFcFcFcFcFcR_'JR5'JRD'JR1Q0aQ0fQ2s'2R?P1Q0aP[P0P1Q0fQ2sP1Q0fQ2sQ0bQ0tP1Q0bQ0tQ0pQ0sP1Q0pQ0s1T]J:03|_:0NB5:0N\DY01W]P2I0FY00W\P2I0FW]W~P;I0FX}0X|[P8I0FX\?W{Q0_I0FXzRX0Qp,2HTRQI0FP]Q1oP]Q0GP]PJP]Q0cP]Q05P]Q0`P]Q0CP]Q29P]Q18P]Q1JP]Q2bP]Q2XP]Q2OP]Q2\P]Q0eP]Q0mP]Q2]P]Q0hP]Q0IP]Q2SP]Q0kP]Q2WP]Q2TP]Q0lQ2GD\D\D\D\D\D\D\D\D\D\D\D\:0@]Jeg03Af:0@]JeO2Q27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1hQ0dQ1uQ1tQ2dQ2h%ajRJ=eZJPZPJQ1p#a,|JRR/rJPRCt5XZQ06Q2NbEbFbGPjPjPUQ2@H00P2b@bAbBbCbQb0Q0FeH13H2840340N403Q0WPKPyP<PX1BfXJ06e20t]FJ0gJ0gWZZ0W=P4P2O2n2001000000121000000W0Z0VYP4P2O2n2001000000121000000W0Z0UCP4P2O2n2001000000121000000W0Z0T9P4P2O2n2001000000121000000b0N=27Q0ZQ02Q0ZQ1100V2WdP2&1mAQ1`E]Q0=-26{Q13,l{Q14-0h{Q0942TP`PQPSPOQ1mPO1BNOQ2DQ27Q1rQ23Q2iQ0nQ2FQ2MQ0rQ1uQ1tQ2eQ2hQ0MPZQ2PQ0DQ2P'rQ28Ct5XZQ06Q2NbEbFbGX;3X>3Q2Q1B42,<2Q0j412^;3^>3Q2tb@bAbBbCb0K1YQ2wQ2BQ2CNg2UQ0]P}P@P2H1ZQ31P4P2O2W0Z0h>K2VN:1WK1XY0OWiP4P2O2n2001000010121000000W0WpP4P2O2n2001000010121000000bRc04P~P2J1<b0b_b^PPP2E]W0Y0PP4P2O2n2001000010121000000W0Y0LP4P2O2n2001000010121000000W0W_P4P2O2n2001000010121000000W0WnP4P2O2n2001000010121000000W0WrP4P2O2n2001000010121000000W0Y08P4P2O2n2001000010121000000W0Y0SP4P2O2n2001000010121000000W0W^P4P2O2n2001000010121000000W0Q1PP2E]W0P4P2O2n2111000000121000000W0Z0fLP4P2O2n201100000012110~000W0X3IP4P2O2n201100000012110~000W0X4HP4P2O2n201100000012110~000W0Z0oGP4P2O2n201100000012110~000W0Z0nGP4P2O2n201100000012110~000W0Z0mGP4P2O2n201100000012110~000W0Z0lGP4P2O2n201100000012110~000W0Z0cGP4P2O2n201100000012110~000W0Z0bGP4P2O2n201100000012110~000W0Z0aGP4P2O2n201100000012110~000W0Z0`GP4P2O2n201100000012110~000W0Z0_GP4P2O2n201100000012110~000W0Z0^GP4P2O2n201100000012110~000W0Z0]GP4P2O2n201100000012110~000W0Z0\GP4P2O2n201100000012110~000W0Z0kGP4P2O2n201100000012110~000W0Z0jGP4P2O2n201100000012110~000W0Z0iGP4P2O2n201100000012110~000Y09P8P2E]W0P4P2O2n2001000000121000000W0XJ>WOXe6n0110}000101XR7Q0BQ0BQ0BQ2;764P6P^PgPEPhPiQ25Q04Q03Q22Q2CQ1|Q2APlPmPnPoQ2<POPTQ2>Q2uP:P;P2NI0s'2XJ>WOXX6XR7P:P;P4P2O4Q2uP;Q2vP:Q2;P4E7[^J>]O^X6^R7eN;24I23N:1WK1XWxY0YP4P2O2n2001000010121000000W0Y0XP4P2O2n2001000010121000000W0WZP4P2O2n2001000010121000000bRWZY0?P4P2O2n2001000010121000000W0Y0GP4P2O2n2001000010121000000W0Y0HP4P2O2n2001000010121000000W0Y0IP4P2O2n2001000010121000000W0Y0@P4P2O2n2001000010121000000W0Y0BP4P2O2n2001000010121000000W0Y0AP4P2O2n2011000010121000000W0Y0DP4P2O2n2011000010121000000W0Y0CP4P2O2n2011000010121000000b0Y0NWlP4P2O2n2001000010121000000W0Y0JP4P2O2n2001000010121000000W0Y0<P4P2O2n2001000010121000000W0Y0=P4P2O2n2001000010121000000W0Y0FP4P2O2n2001000010121000000W0Y02P4P2O2n2001000010121000000W0Y0RP4P2O2n2001000010121000000W0WyP4P2O2n2001000010121000000W0Y0KP4P2O2n2001000010121000000W0WhP4P2O2n2001000010121000000W0WoP4P2O2n2001000010121000000W0Y07P4P2O2n2001000010121000000W0Y0QP4P2O2n2001000010121000000b0PzPxPzQ1;PzV7Q11Q12Q10PgPEPhQ0~PwPvPiPsPkQ0}PuPtQ0xQ0wPbPdPeQ0^P`PcPaQ0LPlPmPnPoQ0[PVPWQ0YMO4Q0yPpPMPqQ0zPrF3G>eWwWvP4P2O2n2001000010121000000W0WuP4P2O2n2001000010121000000W0WtP4P2O2n2001000010121000000W0WsP4P2O2n2001000010121000000b0Y03Y0>WqY0MWgWjWkY0gY0eWmX5GX6GX8GX9GZ0{GZ0zGZ0yGZ0xGZ0wGZ0vGZ0uGZ0tGZ0sGZ0rGZ0qGZ0[GZ0ZGZ0|GXSGXYGXfGY0pY0EY06Xd6Y0:Y05Y0;Y0do"). Qed.

  (* [comment removed for export] *)
  Lemma afwrite_exit : forall {R} (K : @Monad.M APS R) (Q : R -> APS -> footprint -> machine_state -> Prop) (s : APS) (LB : list ablock) RNG
      x1 t0 t1 t2 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    ABASE' stdout_init mm -> AHEAP AI L RNG (aps_m s) LB mm -> aps_so s = stdout_init -> RNGS' RNG ->
    (forall ms', aat_exit 2 s RNG ms' -> implMA RNG K s Q ms') ->
    implMA RNG (s_diag DOom ;;; K) s Q
      (GST 0x7fdac x1 t0 t1 t2 x9 (Z_to_bv 64 AS_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
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
