(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs name the unit's interp_eff_accesses and stepF shims, proved equal to the model's; diagC_exit, phaseC take zstd_frame_info's proofs of the same statements (their recorded proofs used the old stack window, geoA')). *)
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
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3 AD_main_B4.
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
Ltac2 kr_t_AD_main_C () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List:firstn_mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5AsanW9AD_main_C:byte_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions9bv_signedc59OSSVerify5KrLib5AsanW9AD_main_C3sx8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2ex00I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01C47Corelib4Init3Nat3addC46Stdlib5Lists4List<length_skipnC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z8land_0_lC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z4lxorc59OSSVerify5KrLib5AsanW9AD_main_CAland_shiftl_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorc59OSSVerify5KrLib5AsanW9AD_main_C>lor_shiftl_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z;testbit_eqbK46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z9mul_assocC56Stdlib6ZArith6BinInt1ZAmul_lt_mono_pos_rK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7mod_addc59OSSVerify5KrLib5AsanW9AD_main_C;lor_mul_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C:land15_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2I47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z;add_simpl_rC56Stdlib6ZArith6BinInt1Z8lor_commC59OSSVerify5KrLib4Spec5ProgA3AStC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver8read_allC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec5ProgA3ioAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthK59OSSVerify5KrLib4Spec6Driver8diag_msg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps7afree_MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib4Spec6Driver4le32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA;alloc_initAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA4runAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA<alloc_countAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C9main_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AD_main_A:nth_argv_ZC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6Driver:main_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps9amalloc_MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface6ASTAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps:AAllocAsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7HDR_MINC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9COUNT_MAXC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec5Stdio=stderr_fwriteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5AsanW:AD_main_B13BUFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AD_main_A4RNGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx3ALOC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit6aps_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps;aptr_addr_MC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx7AMFRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx5ASTATC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface<atrun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface:rodata_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6MonadF4rng0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_kit@drv_got_of_aheapC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC59OSSVerify5KrLib3Lib6MStateKinterp_eff_accesses_nv_shimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_gnvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib5AsanW7AD_diagAafwrite_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib5AsanW:Stdio_kit2<fmt_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7AD_diagBafwrite_diag_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx@implMA_of_implAMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib5AsanW6AD_ctx3WOKC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5AsanW=AMalloc_iface9AI_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4al_UC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface3aciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface=aclient_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_ifaceAaclient_app_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib5AsanW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib5AsanW=AMalloc_iface8AI_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree?magree_of_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib6Common8DrvAgree?rw_cells_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx;ABASE_munchC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit8aps_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface:dfree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface7dfree_MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>AHarness_iface@astk_shadow_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface9AI_hb_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6hb_idsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5AsanW9AProg_kit?lb_remove_headAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctxAABASE_after_dpostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AD_main_A9RNGS_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit>aps_so_of_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;Stdio_ifaceBstderr_wfile0_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx<amain_returnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C6RQEXITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit:implMA_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit@implMA_from_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx5ABASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit6implMAC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib5AsanW5ABase9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AProg_kit;implMA_bindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface4RSTGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit8RBstdoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface4RFMTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface<AGOT_STDERRPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface8ASTDERRPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface>AGOT_FUZZ_INITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface:AFUZZ_INITC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC59OSSVerify5KrLib5AsanW7AD_diag=AFWRITE_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5AUMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface>drv_img_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AD_ctx>errno_addr_ATPC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop01C59OSSVerify5KrLib5AsanW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib5AsanW:AD_main_B45RDONEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C4RUN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AD_main_A5AARGVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib7SysStepArw_cells_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appK46Stdlib7Strings5Ascii5ascii01C59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AD_main_B19str_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C:diagC_exitC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib5AsanW9AD_main_C5list6C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3sxbC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C59OSSVerify5KrLib3Lib3MemAsext_extract_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib3MemAzext_extract_byteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapc59OSSVerify5KrLib5AsanW9AD_main_C;signed_byteC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C6skipn4C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0<C59OSSVerify5KrLib3Lib8PropExec7v_slliwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_slliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_ifaceGatarget_alloc_init_specC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib5AsanW9AD_main_C3HDRC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib5AsanW9AD_main_C9testbit15C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C:znth2_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C9le16_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib3Lib7ZBridge5zr_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C9le32_consC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_mapc59OSSVerify5KrLib5AsanW9AD_main_C7cfg15_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AD_main_C9main_tailC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string02C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z7inj_minK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06C59OSSVerify5KrLib5AsanW:AD_main_B17s_shortC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AD_main_B18AS_SHORTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AD_main_B1:s_short_roC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00K46Stdlib7Strings6String6string01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C59OSSVerify5KrLib5AsanW:AD_main_B16s_overC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AD_main_B17AS_OVERC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AD_main_B19s_over_roC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr5aluop02I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".   (* [comment removed for export] *)
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
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
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h04__x1h11Rh27__arithh34__ffh48__varmaph55__with61bp;1p;2p;4p;3p;8p;7p-1R0p10000p4p710R1p9P0p1000Np4p710p8p1000ep4p710p1001Bp4p710p8p1001^p4p7210P1p8g002=j10Tg002bj1OTg003@j1ATg003cj2=Tg004Vj29Tg005@j24Tg005\j1FTg006Ej23Tg006aj27Tg007<j1>Tg007\j1<Tg008<j2;Tg008Zj1:Tg0098j1NTg009cj21Tg00:Fj2MTg00:ij46Tg00;Tj12Tg00<2j3ETg00<Uj1BTg00=7j8@Tg00=[j2CTg00>=j2DTg00>Wj2?Tg00?Cj3GTg00?]j3HTg00@<j4ITg00@nj2JTg00AKj7KTg00Aoj7LTf1R1g00BSR0g00C2R2P2g00CRR3f0R4g00D2FKp=5f2R5P0P2P2P3P1P4FLp=8g00DRR6#0R7#0#0R8#OR9#A1=94g00E7R:1994R;'4%F9,3;'7g00EUR;g00F3R<#>%<<1;;1%:;%N;R<P0P2P2P3P;11;:g00F_1M;6R6C6,5<R0P;P6g00GFR=%27R7,1;=E;9C6,5<58<%B2P;P6P=%08#0#0#0#0#2R=,1;C6,5<98<0G@1C<3P4P5g00GmR<g00HMR3'D1?45=G<3dAH;:1CIb3b4b5W014:4%28,J7,34'714:1131='7[^0;P41995P1O2b2b1W6o"). Qed.

(* [comment removed for export] *)
Definition sx8 (c : Z) : Z := if c <? 128 then c else c - 256.
Lemma signed_byte : forall b : byte, bv_signed b = sx8 (bv_unsigned b).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh71Hh82H0h91Rh:1bi001bh;2b0h<2b1p;1p;2p;3p;4p;6p;7p;8g002=j17Tg002bj1fTg003@j1QTg00Hmj1JTg004Vj26Tg005@j24Tg00;Tj1>Tg006Ej23Tg006aj28Tg00Ilj2NTg00JNj2ETg00JkR0j3HTg00KOj25Tg00Klj29Tg00LLj20Tg007<j1YTg007\j1WTg008<j2VTg008Zj1UTg0098j1TTg00:Fj2STg009cj2=Tg00Lij3GTg00MLj3<Tg00=[j2PTg00>=j2MTg00>Wj2KTg00?Cj3FTg00?]j3ITg00@<j4LTg00<Uj1OTg00Moj6RTg00NSj3DTg0000j6CTg00O6j3eTg00OYj2dTg00P6j3cTg001Bj6bTg00P[j1^Tg00@nj2ZTg00Q9j2[Tg00QVj2\Tg00R=j2XTg00Rej1]Tg00:ij4BTg00AKj7_Tg00Aoj7`Tg00=7j8aTg00EUR1f1R2f0R33Fp=1P1P2g00S]P3CBp=AP2g00BSR4g00C2R5P5g00CRR6P3g00D2F_p=2P1P2g00GFP3CBp=;P1P2g00F_P3CBp=@f2R7P4P5P5P6P2P3F`p=?f3R8P4P5P5P6P7P2P3Gap=:g00DRR9#7R:#7#7R;#fR<#Q%J3g00E7R=16<3R>'4%7;#7#7#7R;#7#>R?,3>'816<2R>%>;R;'N13>;14;>1E>;R@3H16<7/E;g00GmRAP016<8R0/3;14;0f5R0,6<RB/5;RC/9?RD/0;PAP1P2PB10B?n0100000020000'1P2f4,6<RE/3;P1PC103;RFf6RG,6<RH'1X61g00F3RI#YRJ%WIRI1V12RK%U1RL%T1RM1S19RN1=1;RO5G1RP=<1O/AN'21PM6RQP3P7g00HMRR,MA1K37=FARdAI1=2CLRRb2b3b4X01153;RS/0;/13^01P3PHO1RTb1PDp-0RDPJPIPKPLPM1;NO,2M%O5RUPM1=1=RV/@N,2MPMP4P5P5P6P8ERR85?MPU1@VP,2M1=1?R6,;P,2M5?MC:C:PQPRb2b3b4X01W5133;14=2/87157;R5,4=135?'8[[^01^5DP313H?PHP2P0O4b19DC?ECW7P3O114;EPJPIPKPLA<1NORE%>9R9,=1=e165G1/AP,2MPQPRb2b3b4X011d9?RP,5F/1S^01PTb110B;/5P/1CP110H;RC/5PRP193?/0;f7,6<RB/0?RT'1X61P119C?RS11FTX61RTP1PCPTPJPIPKPLA<1EOA<1N6'A,2MPQPRb2b3b4X0110F;103?'1^01P3PBO1b1PSPJPIPKPLPM1@ON,2MPUPM1;N6,2M9?M8PU1@VE,2M1;E6,2M5?MC:C:PQPRb2b3b4X01X5D14;3132?,87107;RR,4=13R?'8[[^01^5DP314=BPBP7PGO4b19DC?EC19P?AcC9?EC15H;P3Ebb8W7P3O1n200210000000021100011000b<b;%>:R:%^<'ZR3/[:R:,5>/93/0:PAP1P@P>10>?n0100000020000R?'1e1\<>/1?e1X<2%]>'1eb9W:o"). Qed.

Lemma list6 : forall (l : list byte), (6 <= length l)%nat -> exists d0 d1 d2 d3 d4 d5 r, l = d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: r.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "p'0h01rh12d5h22d4h32d3h42d2h52d1h61Hh72d0h84__p1h92H0h:7__arithh;4__ffh<8__varmaph=5__with>1li001li011bp;1p;3p;2p;4p;6p;<p;7p;8g002=j1DTg002bj1YTg003@j1QTg007\R0j1FTg00TDj1>Tg00Tcj31Tg00?Cj34Tg00UCj20Tg007<j1GTg00U]R1j27Tg00V7j1ETg00;Tj1<Tg005@R2j2ATg00>=j2CTg00V\j4=Tg00WCj1UTg008Zj1STg0098j1RTg009cj2HTg00<Uj1PTg00Moj6OTg00=[j2NTg00>Wj2MTg00?]j3LTg00@<j4KTg00Waj48Tg00X;j2JTg00X[l<ITg00:ij4TTg00AKj7XTg00=7j8WTf2R3f1R4f0R5'J'7p=3g00EUR6/C5p=?g00Y@R7P6P1g00Y_R8P2g00Z?R9f3R:P3P4g00ZaR;g00E7R<P5M<Ip=V1H65p=@P6P4g00F_P5CTp=;P4g00BSR=g00C2R>P>g00CRR?P5g00D2FXp=9P:P=P>P>P?P3P4P5GWp=:P7P6P1P8P2P9f5R9f4R2P:P3P4P5M<Ip=BA1:34=425p=6f6R8A1345912:719p=5A1345912:p=2g00DRR1#DR7#DR@#D#Y#QRA#FRB%>;RC#>RD#>RE#>RF#>RG#>RH?3A5RIP0PAf8RJA1A45RK91A3RL91A:RM91A2RN91A9RO91A8RP54BX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0A^6IP4%GARI93HA17H;%E1R;#D#<RQ/A<RRPHPQ%?QRS1C6<CVP5C=PRp-0RTg00F3RU#GRV%FURU%U6RW%S6RX%R6RY%@QRZ1H6<';,9Y%P>R[PYP=P>P>P?P3EOR>C:1NY?R?P5P3g00GmR=g00HMR\'C1M53=4=\dAL6<4CKR<b;b<b=W8P4\R^8TP5A4BIPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0AP4O2b:b9W6P0PAA1A35RR93HAf:R6=1AJR\=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0A]6P5A1A4IR=93HA17HC%<1R1,AQR]PHPQPSPCP1%?1EBP5C=P]PVPUPWPXPY%@1,;Z,9YP[P>C:P?P<b;b<b=X8TP4\]^8TP5f;R]=1AIRI=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0AP4O2b:b9W6P0PAA1A8RRR93HAf>R1=1A\R\=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0A]6P5A1A9=R=93HA17HD%<7RC,AQR^PHPQPSPDPC%?CEBP5C=P^PVPUPWPXPY%@C,;Z,9YP[P>C:P?P<b;b<b=X8TP4\^^8TP5f?R^=1AIRI=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0AP4O2b:b9W6P0PAA1A6RRR93HAfBRC=1A\R\=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0A]6P5f9RD=1A=R=93HA17HE%<;R;,AQR_PHPQPSPEP;%?;EBP5C=P_PVPUPWPXPY%@;,;Z,9YP[P>C:P?P<b;b<b=X8TP4\_^8TP5fCR_=1AIRI=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0AP4O2b:b9W6P0PAA1A1RRR93HAfFR;=1A\R\=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0A]6P5f=RE=1A=R=93HA17HF%<@R@,AQR`PHPQPSPFP@%?@EBP5C=P`PVPUPWPXPY%@@,;Z,9YP[P>C:P?P<b;b<b=X8TP4\`^8TP5fGR`=1AIRI=4BPX0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0AP4O2b:b9W6P0PAA1ACR93HAPBPAfJRRP\PPD6X0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0A]6P5fAR\=1A=93HA17HG%E7#<R7,AQR=PHPQPSPGP7%?7EBP5C=P=PVPUPWPXPY%@7,;Z,9YP[P>C:P?P<b;b<b=X8TP4\=^8TP5PBPAfKRTPIPPD6X0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7A,0AP4O2b:b9W6PAfERIPAP\PAPEPAPDPAP9PKF5D293HAPAPBPAfMPAfIRHPAPIPAP\PAPEPAPDPJF5D2PPD6X0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5A,0AX7AP;PAPBPAfLRPPAfHR=PAfDR<PAf@R?PAf<R>PAPJf7R[F5D2A1APOD6X0B,0BX1A,0AX2A,0AX3A,0AX4A,0AX5APCPAPBPAPTPAP`PAP_PAP^PAP]PAP[P8F5D2PAPTPAP`PND2D6X0B,0BX1A,0AX2A,0AX3A,0AX4AP1PAPBPAPRPAP;PAPCPAP1PAP6PAP8P9F5D2PAPRPAP;PAPCPMF5D6X0B,0BX1A,0AX2A,0AX3AP6PAPBPAPHPAPIPAP\PAPEPAPDPAP9P2F5D2PAPHPAPIPAP\PAPEPLD2D2D6X0B,0BX1A,0AX2AP8PAPBPAP=PAP<PAP?PAP>PAPJPAP2P:F5D2PAP=PAP<PAP?PAP>PAPJPKF5D2D6X0B,0BX1AP3PBPBPAP`PAP_PAP^PAP]PAP[PAP:P3F5D2PAP`PAP_PAP^PAP]PAP[PAP:P5D2D2D2D6X0BP4PAP;PAPCPAP1PAP6PAP8PAP3P4D2D2D2,CBC8C8C8C8C8C8C8W6X0BX1AP4P5O2n10110001020121101100X>BX2AP4P5O2n10110001020121101100X>BX3AP4P5O2n10110001020121101100X>BX4AP4P5O2n10110001020121101100X>BX5AP4P5O2n10110001020121101100X>BX7AP4P5O2n10110001020121101100P5O1W6W>o"). Qed.
Lemma skipn4 : forall (l : list byte) n, (n + 4 <= length l)%nat -> exists q0 q1 q2 q3 r, skipn n l = q0 :: q1 :: q2 :: q3 :: r.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "p'0h01rh12q3h22q2h32q1h41Lh52q0h64__p1h74__p2h84__p3h94__x1h:4__x2h;4__x3h<2H0h=2L0h>7__arithh?4__ffh@8__varmaphA5__withB4cstrhC5cstr0hD2l0hE2H1hF1nhG2z1hH1HhI2H2hJ2H3hK1li001lhL1mhM1xhN1yhO2z2hP2z3i011bp&0p;1p;2p;3p;<p;4p;Bp;6p;7p;8g002=j1]Tg002bk101Tg003@j1oTg007\R0j1_Tg00TDj1UTg00[@j2KTg00X;j22Tg00U]R1j2ITg00[Wj3jTg00\8j3`Tg00\Vj2<Tg00Tcj33Tg00?Cj34j1bTg00UCj20Tg007<j1eTg00Y_R2j11Tg00LLj27Tg00\mj2nTg00]Pj3lTg00>=j2RTg00X[l<VTg00V\j4ATg00;Tj1OTg00KOR3j2GTg005@R4j2CTg00]mj1BTg00^Rj2LTg006aj29Tg00_4j2ETg00_Nk100Tg00_lj2~Tg00`Mj2^Tg00a6j3gTg00a_j3fTg00bHj2}Tg008<j2dTg00c4j4|Tg008Zj1{Tg0098j1zTg00:Fj2ZTg00V7j1vTg00MLj3uTg009cj2HTg00:ij4WTg00<Uj1tTg00Lij3sTg00=[j2rTg00>Wj2mTg00?]j3pTg00@<j4qTg00Waj4JTg00cRj2kTg00colBcTg006Ej2wTg00Moj6iTg00AKj7xTg00Aoj7yTg00dUj7hTg00=7j8\Tg00Y@R5f2R6f1R7'2f0R834p=:g00E7R9/k8p=;g00EUR:?478p=8A4578p=P1R:8p=5P5P5P5P:P:P:g00e9P2P2P2f6R;g00eYf5R<f4R=f3R>P6P7P8MBcp=TP5P5P5P:P:P:g00f@P2P2P2P3g00f`P<P=P>P6P7P8MBcp=NP5P:P1P2P4g00Z?P<P=P>P6P7P8M<Vp=M1C98p=@1w98p==1C89p=?A4:89p=FP7g00BSR4g00C2R1P1g00CRR3P8Eip=[P:P7g00S]P8CWp=DP7P4P1P1P3P8g00D2Fxp=>P6P4P1P1P3P7P8Fyp=YP6P4P1P1P3P7P8Fhp=aP>P4P1P1P3P6P7P8G\p=QP;P4P1P1P3P<P=P>P4P1P1P3P6P7P8G\G\p=SP5P:P8P2P7P6P>P=P<P;f7R4f8R?M<Vp=XA367893=>p=6g00DRR@#]RA#]RB#]$01#oRC#_RDg00ZaRE#URF#URG#URH#URI,K812C7'IAjC76A`C7612C6/<75:CA`C6>PDP0PC12C<RJ/<=RK9:C8A3C78RL93C6RM93C>RN93C=RO94D;X0D,0DX1C,0CX2C,0CX3C,0CX5C,0C]4P8%eCRP12C=/<>5:CA45EK%1JRQ%1=RR'7#;94:9RSP5P:%b5RTP2%b:R2%17%18'81P781n783lXN5XM5RUPEP91R:9PK1778#;XL:XF:RKPQPRO2PKPJPQ%5QP=PR%5RFTM<VP8CAPS1K<IRS12C;RR'I%1<RQ%OBRB'GRJ%1RRV'CRWPSPJP<PQ%5QPIPB%5BRQENPRPV%5VEMP=CAPW12C4RW#B%1W#@%B4%14#@f9RW,2CRV#1RR%1?RJ'7RS,L9%=S%;SRX/8S'9%?S%FX'9'Ef:RS,2CRY#1RZ%1WR['7#;P:p-0R\g00F3R]&00@,~:R^1^:G5g:1^:F1^:E9g:^5f:5f:g00gC'}%e]33R^%_]R]P:1d:6P71d:>C|RE%{:R_%z:R`1[`<1Z:@Ra%v@Rb,Z:Rc1Z:ARd5u:Re'D,>`5Y`RfP:Peg00F_Re1H:9RgCW,>`1[`;Rh5Y`5a`%t1R1P`P:1H:B9s:dPePcCW,>`RcP1P`1Dga,>`P11[`4ReCQFS1r`3R3P8P6g00GmRdg00HMRi'R1m86=4didAp:97CqRib?b@bAX9:X::X;:X6\X7\W81767Rd,88,9>Rj%?d/9='E1G6B/C>RdA4:96P?[[[^9:^::^;:^6\^7\^8\P8A4DPOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0C%F7f<Rk,2CRl#1Rmf;Rn#1Ro'7#=PmPoP7P6P<P;O9b>bGbEbCbBb<b=W4P0PCA3C68Rm1<V?Rp5:CA3C?;Rq=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0C]4P8A3C7PRr12C?/<45:C1PFp%O@R@/8XRXPTP2PUPFP@%5@PpPKPRPJO2PKPVPR%5RP?PJ%5JFTM9XP8CAPX1KWIRX/IY1G[BRJ/CZRRPXPJPWP[%5[PIPBPQENPYPZ%5ZEMP?CAPR12CnRR#B%1R#@%Bn%@of=Ro,2CRR#1RZ%1kRY'7R[,L9%=[%;[RJ/8['9%?[%FJ'9'Ef>R[,2CRX#1RV%1oRp'7#;P:P^P]PEP_P`1Dag,>`9Y`h9a`fRfP1P`PcP1P`1H:@/Da,>`P1PeCQFSP3Pib?b@bAX9:X::X;:X6\X7\X8\%F8,9=,EjRj18@6P?[\d[^9:^::^;:^6\^7\^8\P8A3C[PRP=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0Cf@R@,2CRh#1Rgf?RF#1Rs'7Rt#?%=tPgPsP7P6P<P;O9b>bGbEbCbBb<b=W4P0PCA3C;mRm1<RkRg5:CA3CkqRq=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0C]4P8A3C<rRr1<ln5:C1PGg%OARA/8JRJPTP2PUPGPA%5APgPKPZPYO2PKPRPZ%5ZPkPY%5YFTM9XP8CAPJ1KoIRJ/IX1GpBRY/CVRZPJPYPoPp%5pPIPBPQENPXPV%5VEMPkCAPZ12CFRZ#B%1Z#@%BF%@sfARs,2CRZ#1RV%1@RX'7Rp,L9%=p%;pRY/8p'9%?p%FY'9'EfBRp,2CRJ#1RR%1sRg'7#;P:P^P]PEP_P`PfP1P`PcP1P`1H:A/Da,>`P1PeCQFSP3Pib?b@bAX9:X::X;:X6\X7\X8\18A6P?[\d\j^9:^::^;:^6\^7\^8\P8A3CpPRP=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0CfDRA,2CRG#1RlfCRt#1Ru'7Rv#?%=vPlPuP7P6P<P;O9b>bObIbCbBb<b=W4P0PCA3CSm1<Z@Rm5:CA3C@q=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0C]4P8A3CWr1<hF5:C1PHm%ObRb/8YRYPTP2PUPHPb%5bPmPKPVPXO2PKPZPV%5VP@PX%5XFTM9XP8CAPY1KsIRY/IJ1GgBRX/CRRVPYPXPsPg%5gPIPBPQENPJPR%5REMP@CAPV12CtRV#B%1V#@%Bt%@ufERu,2C#1%1A'7RA,L9%=A%;AR9/8A'9%?A%F9'9'EfFR9,2C#1%1u'7#;P:P^P]PEP_P`PfP1P`PcP1P`1H:b/Da,>`P1PeCQFSP3Pib?b@bAX9:X::X;:X6\X7\X8\18b6P?[\d\j^9:^::^;:^6\^7\^8\P8A3C9P=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5C,0CfH,2C#1R9fG#1RP'7R\#?%=\P9PPP7P6P<P;O9b>bPbJbCbBb<b=W4PCPoPCPWA3C<LD61<Gt5:CPCPCPtPCPFPCPnPCP4P;D6D6=4DOX0D,0DX1C,0CX2C,0CX3C,0CX5CP[PCPCPpPCP[PCPSPCP;P<D6D6A3CpN54DX0D,0DX1C,0CX2C,0CX3CPSPCPCPsPCPoPCPWPCP<P=D6D6PCPsPCPoPMD654DX0D,0DX1C,0CX2CP;PCPCP@PCPkPCP?PCP=P>D6D6PCP@PCPkA3C?LD654DX0D,0DX1CP6PDPCPFPCPnPCP4PCP>P6D6D6PCPFPCPnPCP4PCP>P8D6D654DX0DP7PCP[PCPSPCP;PCP6P7D6D6,RDCJCJCJCJCJW4X0DX1CP7P8O2n10110001020121101100XDDX2CP7P8O2n10110000020121101100XDDX3CP7P8O2n10110000020121101100XDDX5CP7P8O2n10110000020121101100P7O1bDb4WHXF5WKo"). Qed.
Lemma land15_mod : forall x, Z.land x 32767 = x mod 32768.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6g002=j12Tg00;Tj11Tg00V7j13Tg00@nj2;Tg00Klj24Tg00?Cj35Tg00>=j26Tg00goj1=Tg00hMj2<Tg007<j1:Tg007\j18Tg00WCj19Tg008Zj1HTg0098j1GTg009cj27Tg00:ij4FTg00AKj7ETg00=[j2CTg00>Wj2@Tg00?]j3ATg00@<j4BTg005@j2?Tg00hkj3>Tg0000j6DTf0R0#2#2p=0g00EUR1P1g00DRR2#2R3#1%32#3#3#1R2';,40f1R4%03#0#0#0#0#0#0#1R3'49510X511403,61%=2,<0g00F3R3#:%83%91%H1%G1R3g00BSg00C2R5P5g00CRR5P1g00E7R6,71g00F_1712CFg00D2FE1C35P0f2R5g00GmR3g00HMR7'61@05=537dAA164CBb1b2b31?62P0b09>02EDW4o"). Qed.
Lemma land_shiftl_small : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.land (Z.shiftl b k) a = 0.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h01zh14__x1h27__arithh34__ffh48__varmaph55__with64__x2h71ah81Hh92Hah:2Hkh;1bh<1kp;2p;1p;3p;4p;7p;6p;8g005@j26Tg002=j1ZTg00;Tj1JTg00@nj24Tg006Ej28Tg006aj27Tg00OYj25Tg00hMj20Tg00Klj2?Tg00?Cj32Tg007<j1CTg007\j1ATg008<j2@Tg00WCj1VTg00c4j4UTg008Zj1OTg0098j1NTg009cj2MTg00:Fj2=Tg00:ij49Tg00Aoj7ITg00<Uj1HTg00=[j2ETg00>=j2FTg00>Wj2GTg00?]j3DTg00@<j4KTg00NSj3LTg00goj1:Tg00hkj3>Tg0000j61Tg00iNj1BTg00j0j2PTg00jPj3QTg00k4j2RTg001Bj6STg00kWj2TTg00l7j3YTg00AKj7XTg00=7j8WTg00EUR0f0R1g00E7R232p=3f1R3g00BSR4g00C2R5P5g00CRR6P1g00D2FXp=;f3R7P4P5P5P6f2R8P3P1GWp=<1621R91627g00DRR:#ZR;#JR</43,87'7P014<8R=,57f5R>,01#3X00P0f4R?/?=A201>X00g00F3R@#CRA%A@R@P01@08P3%V0CU%O0RB%N0RCPCP4P5P5P6P01M02g00F_1=0:R:C9,;CR4P0P:g00GF1=0;C9,;CFIR;%H5R5P;C<1EC6R6P1P8g00GmR;g00HMR:'F1G18=2;:dAD023CKR:b3b4b5X10X601813,791623R;1838'7[^10^60P114<7RDP>P3O3b29L?=%:8,0?R=PAP@1@03PBPCP4P5P4C<P6P:b3b4b5X10R:P;\9^10R9P1P7P8O2b2R;9>?8E1A20=?P0%:7R=,0>R614<?,5>/01#3R<X70P010=>R4P<X00P015?DR</0=R5/0>%31X00P01?<DRCf6,01#3X00RBP0P2PB%B>PC1P?DE1P5P:P9P1P?P7O2b29><7E110<4AQ<=>E1P61R>=E1P>P1ESb81T78AY78;E1W9W:X<0X;0X70o"). Qed.
Lemma lor_shiftl_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (Z.shiftl b k) a = a + b * 2^k.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64__x3h71zh82Hah92Hkh:1ah;1bh<1kp;2p;1p;3p;4p;6p;7p;5p;8g005@j2:Tg002=j1YTg00;Tj1JTg00@nj22Tg006Ej29Tg006aj28Tg00kWj2MTg00l`j2ITg00OYj25Tg00KOj20Tg00?Cj31Tg007<j1@Tg007\j1?Tg008<j27Tg00c4j4>Tg008Zj1VTg0098j1UTg00:Fj24Tg00O6j3TTg00V7j1LTg00Lij3<Tg00:ij46Tg00=[j2HTg00>=j2ETg00>Wj2DTg00?]j3FTg00@<j4GTg009cj2CTg00<Uj1KTg00l7j3BTg0000j6ATg00WCj1NTg00Aoj7OTg00m>j5PTg00nDj3QTg001Bj6=Tg00nnj2RTg00oKj3STg00AKj7XTg00=7j8WTf1R0g00BSR1g00C2R2P2g00CRR3f0R4g00D2FXp=3f3R5P1P2P2P3f2R6P0P4GWp=;g00EUR7g00E7R8/:4R91:85g00DRR:#YR;#JR</20,95'8P71M56R=f4R>'IR?f5R@12<5RA,5>'0RB9174X77RCP710=>PCP712<6,55104@=17BX77g00F3RB#@R<%?BRBP71776RCP01775C>%V7RD%U7REP7147:RF147;R;5T7RG%L:,47R:5<7g00S]A<7:GC6'31HE3R:P4P6g00GmRGg00HMRH'E1D46=1GHdAF780CGRHb3b4b5X07X17X671540RG/06106G517^07^17^67P4P@PAP>O3b2P=P<PB1770PDPEP71C78g00F_PFC6,3ERG%K2RIPGC;P:PHb3b4b5X071:80R8\9^07P4P5P6O2b2RJ9B56EAP?P>P5P6PJP<PBP7PCP0%N7C>PDPEPEP1P2P2P3PGP7PFg00GFP;C6,3EFOREPIPEC;P:PHb3b4b5X07X171940,891906,88[^07^17P4PAP@P0O3b2DPR09Q=>E=1R=>AS=>0E=W8W9X<7X;7W:o"). Qed.
Lemma lor_mul_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (b * 2^k) a = a + b * 2^k.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with64__x2h72Hah82Hkh91ah:1bh;1kp;2p;1p;3p;4p;6p;7p;5p;8g005@j23Tg002=j1STg00;Tj1JTg00@nj22Tg006Ej25Tg006aj24Tg00kWj28Tg00nnj27Tg00KOj20Tg00?Cj31Tg00OYj2:Tg00>=j2>Tg007<j1@Tg007\j1RTg008<j2?Tg008Zj1QTg0098j1OTg009cj2NTg00:Fj2<Tg00:ij4;Tg00<Uj1LTg00=[j2ITg00>Wj2HTg00?]j3ETg00@<j4FTg00l7j3GTg0000j6=Tg00WCj1DTg00c4j4KTg00Aoj7CTg00omj5BTg001Bj6MTg00AKj7ATg00=7j8PTf1R0g00BSR1g00C2R2P2g00CRR3f0R4g00D2FAp=6f3R5P1P2P2P3f2R6P0P4GPp=9g00EUR7g00E7R8/34R91385g00DRR:#SR;#JR</20,55'4P71856R=f5R>,7410>4R?517X17P7f4R@12<6,:5RA'0RB18@5,0>9174X17P7PA12<5R<,:@,0>=17?X171>7BP=g00F3RB#@R?%RBRB1?70%Q7RC%O7RDP71N78g00F_1<7:R:C;,6DRE%L2RFPEC91ID3RGP4P6g00GmRHg00HMRI'>1H46=1HIdAE780CFRIb3b4b5X071380R8\9^07P4P5P6O2b2RH9G56RJE=17=@P@P5P6PHP?PBP71?76P0%D7CKPCPDPDP1P2P2P3PEP7P:g00GF1<7;C;,6DFCRDPFPDC9PGPIb3b4b5X07X671540,491506,48[^07^67P4P<P>P0O3b2DBE=PAPJEMW7W8X;7X:7W9o"). Qed.
Lemma le16_cons : forall d0 d1 (r : list byte), le16 (map bv_unsigned (d0 :: d1 :: r)) = bv_unsigned d0 + bv_unsigned d1 * 256.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h02d0h12d1h21rp;1p;2g002=j10Tg002bj18Tg003@j13Tg007\j12Tg004Vj21Tg00;Tj17Tg00OYj26Tg00KOj24Tg00>=j25Tg00DR#0#0#0R0#8R1#3R2%22g00EUf2,11f1,11%00#0#0#0#0#7'6'4'5W2X12W0o"). Qed.
Lemma le32_cons : forall q0 q1 q2 q3 (r : list byte),
  le32 (map bv_unsigned (q0 :: q1 :: q2 :: q3 :: r)) = bv_unsigned q0 + bv_unsigned q1 * 256 + bv_unsigned q2 * 65536 + bv_unsigned q3 * 16777216.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h02q0h12q1h22q2h32q3h41rp;1p;2g002=j11Tg002bj18Tg003@j16Tg007\j19Tg004Vj22Tg00;Tj15Tg00OYj24Tg00KOj23Tg00>=j27Tf0#1#1p=0g00DR#1#0R0#8R1#6R2%92g00EUf4,21f3,21%10#0#0R0#5'4'3f2,21%00#0#0#0R0#5'4'3f1,21%00#0#0#0#5'4'3'7W4X32X22X12W0o"). Qed.
Lemma znth2_cons : forall d0 d1 d2 (r : list byte), znth (map bv_unsigned (d0 :: d1 :: d2 :: r)) 2 = bv_unsigned d2.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "h02d0h12d1h22d2h31rp;1p;2g002=j10Tg002bj15Tg003@j12Tg007\j11Tg004Vj24Tg00>=j23Tg00DR#0#0#0#5R0#2R1%11g00EUf1,40'3W3X21X11W0o"). Qed.
(* [comment removed for export] *)
Lemma testbit15 : forall c0 c1, 0 <= c0 < 256 -> 0 <= c1 < 256 -> Z.testbit (c0 + c1 * 256) 15 = (128 <=? c1).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "p'0h04__x1h14__x2h24__x3h32H2h41Hh57__arithh64__ffh74__p1h88__varmaph95__with:2H3h;2H4h<2H5h=2H6h>1qh?1rh@1zhA4__x4hB4__x5hC4__x6hD1bi001bhE2H0hF2H1hG3H10hH2H7hI2H8hJ2H9hK2b0hL2c0hM2c1hN2q0hO2r0p;1p;2p;3p;4p;6p;7p;8g002=j1:Tg00;Tj1CTg00V7j1RTg00@nj2qTg00Q9j21Tg00Klj20Tg0110j2UTg011Mj2aTg00?Cj36Tg011jj2`Tg012Kj1hTg00OYj2ATg00KOj2>Tg012dj2[Tg006Ej24Tg013Kj2ZTg005@j2BTg006aj2GTg0142j2WTg014Xj2\Tg00TDj18Tg015>j2VTg015gj3LTg00_Nj1dTg00_lj2cTg00a6j3TTg00`Mj2bTg016Pj2jTg007<j1iTg007\j1~Tg008<j2PTg00c4j4OTg00WCj1}Tg008Zj1|Tg0098j1{Tg009cj2JTg00<Uj1zTg00:Fj2ITg00O6j3]Tg00Lij3STg00=[j2yTg00>=j2fTg00>Wj2xTg00?]j3wTg00@<j4vTg017<j2uTg00JkR0j3tTg00Moj6rTg001Bj6_Tg017^j2pTg018?j3oTg0000j6nTg00a_j3YTg00bHj2sTg00Tcj3mTg00:ij4XTg00AKj7eTg00Aoj7lTg00=7j8^Tg018dj6kTg00E7R1f0R2'Bp=5%:2#:p=Mf2R3f1R4/42'Gp==1A42,>3p=7g00EUR5?621p=NA6542p=21b52p=<AY542p=QAY5429Y53p=9g00gC,s2p=Kg00F3R6?m42p=FP5P4g00GFP2CXp=@P4g00BSR7g00C2R8P8g00CRR9P2g00D2R:Fep=3P5P4g00F_P2CXp=DP3P7P8P8P9P4P2Flp=Hf3R;P7P8P8P9P3P4P2G^p=?P3P7P8P8P9P5P4g00S]P2CXP:Fep=;P4P7P8P8P9P2Ekp=gf6R:P7P8P8P9f5R<f4R=P;P7P8P8P9P3P4P2G^G^p=E%54g00DRR>#:R?#:R@#:#M#MRA#:RB#CRC7=4RDg00GmREA7;3CRF%C?RG%R>RH#R#R#CRI'q'1/0G%C>RJ'U%CARA/a;RK96E2XDE1`3A%NARL#hRM11;ARN,AA10;A'>,2;[1[;A141ARO10=ARP#5?=PA[1Z=A14A1RP10<ARQ,4A1BQ1'G[1W<A11:A#N\L1\:Af7RQ/0A/2Q\L11QARRP5f8RS/0ARTP5f:RUf9RV;7C%:B#M#M#M#CRW'`%NWRX#hf;RY?7UCRZ11ZW,AW10ZW'>'2[1[ZW141WRZf<R[?7YCR\/0WR]#5?=]W[1Z\W14W1f=R\?7[CR]/0WR^,4W1B^1'G[1W]Wf>R]?7\CR^/1W#N\X1\^Wf?R^?7]CR_/0W/2_\X11_WP5f@R_?7^C/0WP5g00ZaR`#8Ra#8Rb#8Rc#8Rd#8Re#8Rf#8Rg#<%<fRf1V5CRh%<eRe5L5%dB,c5%<cRc5T5%<bRb1V5W1b5`R`5L5'Q3939#K%8g#<%d>,c5Rg=T5fAL5hc%<aRa'Q391V5ARh=L5a99`e#K'j%i6Rf'F'F%~6R6P5P51P5=P31P5:COP4P51P5<P;%}5RBCOCO%|5Ri%{5RjPj1J51Rk1J5WRl'@,3j%z8Rm%:H,I5Rn,Dk,3j1@nl,3j5HjC?PmPjPjA;jlk,gjPm1I5HRH1I5@R@1J5CRo5]55S51I5?Rp9]5l=S5n5;jC?PmPjPj1J5ARn,@k,3jRlPm%R?,I5R?,Dk,3j1@?n,3j5HjC?PmPjPjA;jnk,gjRqPm1I5>R>9]5nRr=S5?9;j@C?PmPj1DkH,3jR?1@Ho,3jRo5HjPmA;j>pC?FEFE1yj9RpP2P3g00HMRs,fERt1x23=6EsdAw514CvRub6b8b9X05X15X25XA5XB5XC5%5:Rv?=:W\Zg019HRZ\XA7=<C1AW;/>Q'2[%5Q?=QA\OPZ\LRZ1AA=/>S,2Q[A=v:C12<:[[[[[^05^15^25^A5^B5^C5P2P4PSfAfBP3PVP:PQP\P]P_O;b5bObNbGbJbIbHb=b?b>b<b;b:b3b4113A11FW'2P5PN102G/UJRN1aA=R_56EX@51uA;1BA;R]14;ARv;tKP_PEP01BA<14<A10RG/UJ=6E4P41BA:1`QARG11SAR0,AA/>T,2S\MRM1[SART10VAR_#5?=_A\OR_1ZVARV10UARK,4A1BK1'G\PRP1WUARU11YA#N\LRK1\YARY10[A/2[\LRL11[AR[P510\ARXP5p-0RwAT5gcRgAL5h`Rh,QaRa59e#K%<dRd1QbhRh79c#K/Ff'FP6P5P51P5;P;PBCOP41P53CORbPiPjPjPlPm1Dk@,3j1@@n,3j5HjC?RlPmPjPjPqPmAS5r@9;jHC?RrPmPj1DnH,3jPmPjPjP7P8P8P9P<ErR<=HjoPm1J5J=;j>FEFEPpPub6b8b9X05X15X25W7%5;/Gv\ORO1AA3/>=,2;\ZRZA=:=C12J=[\][[^05^15^25^7wP2%5^P4P^P3P:PQPSP\O8b5b?b>b=b<b;b:b312JRP5PJA6ENsX@5PtP0P2E_b3W4P2O114:APGPMPTP_PVPPPUPKPYPLP[P5PXP5A9egh#KA9dca#K/Ff'FP6PbPiPjPlPmPjPrPmPj1@Hn,3jPmPjAHj?<PmA;jk>FEFEPpPub6b8b9X05X15X25X7w%5=/G:A651=[\v\Z\O^05^15^25^7wP214^CP4P^P3P:PQPSP\O8b5b?b>b=b<b;b:b3A651RP5P1g019eR196ENX@51fE1P0P2E_b3W4P2O1n200210000000021100011000bKbDA7=;C/1WP2E_b41pFIPfP6PBPi1J5I,Dk,3jPpPub6b8b9%5IP2b59oFIEnXFDWEXM5XL5o"). Qed.

(* [comment removed for export] *)
Lemma cfg15_Z : forall u0 u1, 0 <= u0 < 256 -> 0 <= u1 < 256 ->
  Z.lor (Z.shiftr (Z.land (Z.shiftl ((sx8 u1) mod 2^64) 57) 18446744073709551615) 49) u0 = Z.land (u0 + u1 * 256) 32767.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with51zh64__p1h72Hah82H2h94__x2h:4__x3h;1Hh<2H3h=2H4h>2H5h?2H6h@1qhA1rhB4__p2hC4__p3hD5__x10hE5__x11hF5__x12hG5__x13hH4__x4hI4__x5hJ4__x6hK4__x7hL4__x8hM4__x9hN1mhO1nhP1phQ1EhR2H0hS2H1hT3H10hU3H11hV3H12hW3H13hX3H14hY3H15hZ3H16h[3H17h\3H18h]3H19h^3H20h_3H21h`3H22ha3H23hb3H24hc3H25hd2H7he2H8hf2H9hg7__sat26hh7__sat27hi7__sat28hj7__sat29hk7__sat30hl7__sat31hm7__sat32hn7__sat33ho6__sat7hp6__sat8hq1bi001bhr2b0hs2q0ht2q1hu2q2hv2q3hw2r0hx2r1hy2r2hz2r3h{2u0h|2u1p%0p&0p;1p;2p;3p;4p;6p;5p;7p;8g002=j15Tg00;Tj1ATg006Ej24Tg006aR0j2;Tg00@nj2gTg00V7j1ITg00kWk20QTg00Klj20Tg01:Ej2{Tg00nnj2bTg00hMj2}Tg00OYj21Tg00Q9j23Tg00Ilk20WTg005@j2STg00JNk203Tg00JkR1k30RTg00LLj28Tg007<k10PTg007\k10NTg008Zk10JTg0098k10ITg00:Fk200Tg002bj1cTg00<2j3dTg00=[k20@Tg00>=k20>Tg00>Wk20`Tg00?Cj3wTg00?]k30\Tg00@<k40[Tg00WCk10ZTg009ck20;Tg01:ek30:Tg01;Fk209Tg01;hj3|Tg001Bj6uTg00`Mk208Tg00TDj19Tg00<Uk10YTg01<Kk40VTg01=6k40STg00NSj3sTg011jj2WTg012Kj1pTg012dj2[Tg013Kj2ZTg0142j2]Tg014Xj2YTg01=Qj2oTg01>9j3rTg00_Nj1nTg00_lj2tTg015>j2lTg00MLj3mTg00KOj2DTg01>]k40GTg00Rej1<Tg016Pj2xTg01?>k50ETg01@>k10KTg01A=k30DTg00l7k30LTg00gok10MTg00hkk30CTg008<k20BTg00O6k30OTg00:ij4jTg00AKj7qTg018dk60ATg0000k60UTg00a_j3hTg00bHk205Tg00Tck30?Tg00Mok60aTg00Aok70=Tg00=7j8`Tg00a6k30<Tg015gk30_Tg00c4k40^Tg00Lik30]Tg00E7R2f0R3'Sp=:%53#5p=ff1R4#</03p>04f2R51143'Dp=J%I3#Ip=ag00EUR6?w43p=2%53#5#5#5p>07f3R7#</05/14/03p=N1154/03p=z1054/13p=U20B63p=V20;63p=MB0O643p==P5g00BSR8g00C2R9P9g00CRR:P6P4g00S]P3Cjg00D2R;Fqp=7P4P8P9P9P:P3J0Ap=vAw632p=FP6f4R<P7P5P4P3J0Up=620863p=?Ah643g00gCR=+05p=\g00F3R>1x54<0?3p=TP5P8P9P9P:P6P4g00F_R?P3CjP;Fqp=KP4P8P9P9P:P3J0ap=iP5P8P9P9P:P4P3K0=p=BP6P4P?P3Cjp>0XP<P8P9P9P:P7P5P4P8P9P9P:P3P;FqG`p>061423p=RP5P8P9P9P:P6P4g00GFR?P3CjP;Fqp=>P6P4P?P3Cjp>0Tf6R?P8P9P9P:f5R;P<P7P8P9P9P:P5P4P3G`G`p=kP;P8P9P9P:P<P7P5P8P9P9P:P4P3K0=G`p>021443,;5p=^1154/D39w67p=C1S251443';p=L1S32p=XB0<643p=QAh643p=_%53#5#5#5#5#5#5#5p=eB0_643p=OAh6439h65p=H2053=,x4p>01P6P5P4P3H0^p=P20063p=EB0]643p=GP?P8P9P9P:P;P8P9P9P:P<P7P5G`P4P3G`p=@1154/D3p=yB0?>43p>0HB0<654=h63p=~1S24/;3p>0F%:4R8g00DRR=#5R@#5S00#5RA#5#fRB#5RC#5S01#ARD,44S02';S03Q03%A@RE%ABRF'gRG-045S04%I=S05#IRH#f#IRI#ARJ+0QRK/0GQ05#5S06#5S07#5#IRL#ARM,{3/b<AJ<7D%aH#a#a#a#a#a#AS08'}RN'2X56Q041gEJRO'1RP103GRQ/{M/b</2NX5610PGS091gEMRP'3S0:1b3</2NX56AJ75DS0;Q01#5#f$07RN#ARR'0P7PGPOPGCN/3PS0</b</23X56%ACRC-0W5145CRS1SC5RT2035C40R2037Cg00GmRUP114<C1SC<PUP6P4P?18?DR1n0100000020000/0G?zOG/3P10?CRV%AARW,gERX'1'2P414;CP?Az3OG/3PRYf7RZ?UCX'2X56P?AzZOG/3P113XR['2X5611?OR\133PR]11ZXR^'2X56R_11?PR`/1XP_11P?Ra13[P/2^X56P611?XRb,1PRcP_11bPRdP_Pb123^X56&0P>R^&0N>R>%V4R_&0J6Re&0I6Rf2006=Rg%MERh%cA5d6S0='=Ri;7i20@f:R:P3P5g00HMRi-0>U20`35=wUidB0\624H0[Rib2b3b4X0612[[^06P3PZO1b113dPP^P>&0Z6RdPe%cL9d6hS0>20;62RL57f,vfS0?P:Pib2b3b4%FPRUg019HS0@[S0AP3b1S0B:0:bPD6Pc209PbD611aXA|P?XEuP`209?PD611PX,1?A|?PXD610\G%:\14\Gp-0R`g00ZaRa-086Rb%9aRa#9Rc#?Rj,\b;T^P>P_PePfAKfLgRk1if7S0C5BfRl&0Y9R9Pf%cI9d6hRI,=g-0XLI06P:Pib2b3b4X06W6%:3Rm/;4114O#:[^06^6`P314ZDRnPZP;O3b1%R5RoP01454117<115<'4[R011571147'41475Rp[11<;117;'4\pP7P5P4P3H0VP4n2001000000120000000UXN6XO6XP6P0\o^N6^O6^P6P3POPZ%AH,gERoP^P>PdPeA>fLIP:Pib2b3b4%ROS0DP3b1P^P>P_PePf%MCR09>fgRpP9Pf%cH9d6h-0TgI06P:Pib2b3b4X06143CRq144o[^06P3f8RoP5O2b1O5b8H0S9s\GD6PVP^P>P_PePfPpP9PfPlP9ABfkpFkP:Pib2b3b4X06X6`1;85%:5Rp/;SS0E[\q^06^6`P3PnPZP4P;O4b19s?CD610?GP^P>P_PePf%MDRn9>fgRq9BfkS0FP9PfPk%cB9d6hRh9>fgJ02P:Pib2b3b4X06A^m3DS0GA^84G[^06P3PZP;O2b19s?GD6W;P3O11SC;1W1G%FGRm#pS0H18ZDRBPG13BG10BGS0ICC[1[BG%RGRB18oDRS/0GRl?LlG[1ZSG14G2S0Jf9RS/8DRl/0GR\,4G%X\';[1]lGf:Rl/8DR\/3G#F\m1Y\Gf;R\/8DRr/0G/2r\m13rGP6f<Rr/8D/0GP61oEFS0K%RERs%:FS0LPB[[S0M%:ERtg01AfRuArEF4UW7S0N%:G\u^7tS0O%n=,t6Rv%9cRc#?Rw'QRx/_bS0P%fN#e#e#e#eS0Q#eS0R#5#f$07#A,l6/ObS0S%9cRc#9S0T#?S0U%?cRc;HwRN'\Q0U%?aRa7Hx1_ca1_ab+01;T^3TP>%V7?P5d?P4dS0VPePfPfA>fLhS0WP9%E@Rx9KfLS0XA>fxh5BfP9PfPfA7fhL,vfS0YP9Am6gnQ00#ERy,=h/Gx57fP9PfAKf0gS0ZP9Pf1if;=BfqS0[P9Am6hn/GgRz=7fxFkF@F@P:Pib2b3b4X06X96X:6X6`A^p5G\BQ0@\mRp185DPGP<P7CC[A^?7DS0\18GDR{/D</2;[\T[[^06^96^:6^6`P3f@R|#:S0]P<P7P|PoPSPlf>R}O8b1bobpbAb@b?b>b=b<b81D{?101G'2P61D{ZR110oCR~/1X,2YX56P^P>P_PeAm6g0S0^/=IRY%A=R=#M9m6I/=h'G1=zI57fP:Pib2b3b4X06183C18O=S0_/1GR=7yO1D{3/1O'2^06P3PoO1b118ZC?yO=111O'2P618oCS0`/1OR1/D=S0a13QP10SCS0b/1XRQ'2X56101GS0c12]QX56RQP1PQ1WoC%FCRQ#pS0dPSPC13SCQ0bCC[1[SC%RCR=10lCRz?LzC[1ZlC14C2S0e10\CRz,4C%Xz';[1]\C13rC#F\Q1YrCf=Rz/0C/2z\Q13zCP610}CP6Q0P1l6C/ObS0f/\N1_wbQ0fQ0T#9S0T#?RN1Qvc;Hj'\;T^3TP>Q0VPePfPfA>fL0S0VP9Q0XA>fx05BfP9PfPfA7f0L,vfS0PP91=0y/Gx97fgP9PfQ0ZP9PfQ0[P9Q0^=7fxFkF@F@P:Pib2b3b4X06X96X:6X6`Q0E\=Q0@\QS0EP5PCP<P7CC[Q0\18<C/2;[\T[[^06^96^:6^6`P3Q0]P5P4P|P?PZPlP}O8b1bAb@b?b>b=b<b8Q0`/2~P618SCRT18lCS0`/1O/3P/2[X5611TXR[/1PS0\Q0`/1XS0`,2]X56P[Q0`,23X5620>6[Q0\/3PQ0B:0:[PD611XP,1TA|TXPD6Q0bP3Eub8Q0c1\bwQ0R#A,l6RT/OaRa/\b00H^5TbP>P_PePfQ0ZP9PfQ0C=BfqP9AKfLYA>fYh5BfFkP:Pib2b3b4X06X6`1SC3Q02,;5185C/1ORY?LYG[[^06^6`P3%:SS02PSP7PZO4b19s1GD6Q0a/0GP1Q0_PGP^P>PdPeQ0YP:Pib2b3b4PpP3b1H0GD61D{o/1OP3Eub8Q0IP3Eub8W;P3O1n200210000000021100011000brbqQ0:AU5CX'2R{eP{107CS0:/1XR{1b3;AJ;<D/0RR1'2X561D<{1231X561W7CQ0dP<PC13<C10<CCC[1[<C10;CR1?L1C\=1Z;CQ0e14CV%XV';[1]?C13ZC#F\Q1YZC12~o\Q13oCP6Q0bP611lDS0b,D\/WR%FRRQ#pAJr\DR~PR13~R10~RCC[1[~R%RRR~AJzrDRV/0RR1?L1R[1ZVR14R2AJ}zDRV/0RR1,4R%X1';[1]VRf?RV?J}DR1/3R#F\Q1Y1RAJ|VDR1/0R/21\Q131RP6fAR1?J|D/0RP6P1PGPOPGCN/WP%pUfBRYPGPOPGCNRqPP13qP10qPCC[1[qP%RPRqfCPGPOPGCNR[/0PR]?L]P[1Z[P14P2fDPGPOPGCNR2/0PR[,4P%X[';[1]2PfES0ePGPOPGCNR2/3P#F\U1Y2PfFS0dPGPOPGCNR2/0P/22\U132PP6fGR2PGPOPGCN/0PP6fHS0I#<?UGO/WGQ0HfI#<?UGORUPG13UG10UGCC[1[UGfJ#<?UGORU/0GR[?L[G\B1ZUGQ0JfK#<?UGORU/0GR[,4G%X[';[1]UGfLS0_#<?UGORU/3G#F\m1YUGfMS0a#<?UGORU/0G/2U\m13UGP6fNS0CPGPOPGCNP6fOS0Z#</WGQ0HfP#<RUPG13UG10UGCC[1[UGfQ#<RU/0GR[?L[G\B1ZUGQ0JfR#<RU/0GR[,4G%X[';[1]UGfSS0J#<RU/3G#F\m1YUGfTS0H#<RU/0G/2U\m13UGP6fURU004GP61oEM%:MS0cPq[\sArEM4VuX7t%:P\u^7t1oEJ%:JS0BQ0D[\sArEJ4VuX7t%:O\u^7t1oEW%:WS0D%RX[\sArEW4VuX7t%:X\u^7tQ0KQ0MQ0NQ0OQ0T#9Rt#9Ru#9RE#9#9Rs#9Rm#9R[#?R],OT%?mRm%?s3H%?E%?tRt,Qv;Hj%?uRuQ01#n,t6RE/QN;Hj1OTjQ0SQ0R#n,t6%9[R[#9#9#?'Q%?[1Qvm1OTtQ0Q#n,t6/QN'_5H]5~v3H7Ha+01'x1l6DRa/Oc/_b9~vN1l6R/Ob1OaNQ0U,QE;Hw9Hut'\;T^3TP>%Vo%Vr7P<%Vl?P?d7P5%VS%Vz7P;%V\?PZd7P77P4PePfPfQ0YP9Q07#EQ06#I#E,=h%I@R@#5#ER5'G57fP9PfPfQ0WP91ifV%EARA=>fh5BfP9PfPfQ0YP91=5I%I@#E,=h/GA57fP9PfPfQ0>9>fLP9Q00#I#ERh9KfL1if|5BfP9PfPfQ0?P9Q0>%E@R@'=/Gh97fAP9PfPf%MRRA9>fLP9Q05#ERh9KfLA>fhA5BfP9PfPfA7fAL,vfP91=yn,Gg%EH,=A/Gh57fP9PfPfQ0VP9Q0X1if15BfP9PfPfQ0PP9Q06#E,=0/Gx97fyP9PfQ0=,=xRx97f@P9PfQ0FP91Ggx=7fhFkF@F@F@F@F@F@F@F@F@P:Pib2b3b4X06X96X:6XH6XI6XJ6XK6XL6XM6XD6XE6XF6XG6X6`XB`XC`AyGzlRh,2r\pA^VSG\B11rO/2h\p20FrY\qQ0APrPPPSPzCC[ALooR\~Q0@\QQ0b,DZPRPzPSCC[Q02/;2\=Q0EPrPCP}PlCC[11lX,2zALllDAJ\rX/2z[[[[[[[[[[[^06^96^:6^H6^I6^J6^K6^L6^M6^D6^E6^F6^G6^6`^B`^C`P314UC142PQ0]Plf_Rl#<P1PSP2P|Q0ZfVQ0IPlQ0CPUf`PVQ0eQ0dQ0_Q0aQ0JQ0HfZf[f\f^OKb1bgbhbibjbkblbmbnbzbvbcbbbab`b_bybub^b]b\b[bZbxbtbYbXbWbVbUbwbsbTbfbebdb?bAb@b>b=b<b8b;1b{<P<Q0:PWP^P>PdPe%MW9KfLP:Pib2b3b4Q0DP3b1P^P>P_PePfQ0FP9PfPkQ0=9>fgJ02P:Pib2b3b4X06Q0GA^84X[^06P3P;P7O2b1I0ED6Q0<P3D6bQQ0;Q08'}Q0;$0KD6Q09/{MQ09P^P>PdPe%MM9KfLP:Pib2b3b4Q0cP3b180DMD6PKQ04P^P>PdPe%MJ9KfLP:Pib2b3b4Q0BP3b180LJD6&0MF,}KP^P>PdPe%MF9KfLP:Pib2b3b4Q0LP3b1:0CKFD6WSWRX|6X{6o"). Qed.

(* [comment removed for export] *)
Lemma bm_Z : forall q0 q1 q2 q3, 0 <= q0 < 256 -> 0 <= q1 < 256 -> 0 <= q2 < 256 -> 0 <= q3 < 256 ->
  (Z.lor (Z.lor (Z.shiftl q1 8) q0) (Z.lor (Z.shiftl q2 16) (Z.land (bv_swrap 32 (Z.shiftl q3 24)) 18446744073709551615))) mod 2^32
  = q0 + q1 * 256 + q2 * 65536 + q3 * 16777216.
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with52Hah64__x2h71zh81Hh94__p1h:4__x3h;2c3h<2H4h=2H5h>2H6h?2H7h@7__sat10hA6__sat9hB4__x4hC4__x5hD4__x6hE1qhF1rhG7__sat11hH7__sat12hI7__sat13hJ2H8hK7__sat14hL7__sat15hM6__sat8hN2C3hO2H0hP2H1hQ2H2hR2H3hS3Hc3hT7__sat16hU1ohV2q0hW2q1hX2q2hY2q3i001xp%0p&0p;1p;2p;3p;4p;6p;5p;7p;8g002=j11Tg00;Tj1:Tg006Ej2<Tg00@nj2YTg00OYj20Tg00nnj27Tg00kWj2jTg002bj1`Tg00V7j18Tg00QVj2MTg00hMk204Tg00Klj22Tg01BBk20YTg005@j2CTg00_4S00k20=Tg00KOj23Tg00LLj25Tg006aS01j2>Tg00UCS02j2|Tg007<k10QTg007\k10OTg008Zk10KTg0098k10ITg00:Fj2_Tg00=[k20_Tg00>=k20^Tg00>Wk20]Tg00?Cj3VTg00?]k30\Tg00@<k40[Tg00`Mk20ATg00TDj1DTg00<Uk10ZTg009ck20@Tg00NSk30>Tg01Bgk20XTg01=6k40<Tg00Wak40;Tg011jj2rTg012Kj1}Tg00Q9j2BTg012dj2qTg013Kj2pTg0142j2tTg014Xj2oTg01=Qj2]Tg01>9j3^Tg00_Nk10UTg00_lk20TTg00a6j3iTg016Pk202Tg00WCk10RTg001Bk607Tg00P[k10NTg01?>j5xTg01CLk206Tg00gok10LTg00hkk30MTg00l7j3~Tg008<k20PTg00:ij4uTg00AKj7sTg00<2k30HTg00Lik30:Tg00MLk30GTg00dUk70VTg00a_j3hTg00bHk20FTg015>k20dTg015gk30ETg00Tck30DTg00Mok60cTg00Aok703Tg00O6k30CTg00=7j8vTg0000k60bTg00c4k40aTg018dk60`Tg00E7R0f1R1'Cf0R2'>p>0S%12#1p=z%82#8p>0J%82#8#8#8p>0e%82#8#8#8#8#8#8#8p=[f2R31012'3p=4%12#1#1#1#1#1#1#1p=e1331/32p=Zg00EUR4f3R5/73/21;V2p=N1331/52p=6AV453AV412+0=p=K%12#1#1#1p>0WAV412p=;1231=V42p=@20P42p=\P3g00BSR6g00C2R7P7g00CRR8P4P1g00S]P2Cug00D2R9Fsp==20@42p=FB0H412p=fB0:412p=QB0G412p=gP3P6P7P7P8P1P2K0Vp>0B20A42p=HAh412g00gCR:+0Fp=L20d42p=dB0E412p=Tg00F3R;@0D12p>0120231>0D;2p=RP3P6P7P7P8P4P1g00GFR<P2CuP9Fsp=GP3P6P7P7P8P4P1g00F_P2CuP9Fsp=?P1P6P7P7P8P2J0cp>0?P3P6P7P7P8P1P2K03p=kB0C412p=SP4P1P<P2Cup=bP5P6P7P7P8P3P1P6P7P7P8P2P9FsK03p=af6R9P6P7P7P8f5R<f4R=P5P6P7P7P8P3P1P2GvGvp=E1C02p=91C031<12'>p=IP4P=P5P3P1P2J0bp=AAV420p=X13129V43p=W1<02p=U1031/32p>09Ah412p=J20F2:p>08Ah4310022p={Ah4129h43p>00P4P3P1P2H0ap=cP<P6P7P7P8P=P5P3P6P7P7P8P1P2K03Gvp=lP1P6P7P7P8P2J0`p=yP5P6P7P7P8P3P1P2Gvp=w1<12,>3p=mB0C412:0:43p=O1331/02p>051031,35/02,3=p=PB0E431=h42p=ng00DRR6#1R:#1S03#1R>#1S04#1R?#1R@#1RA#1RB#:RC,<5S05-0S5RD%::RE%:>RF'YRG,09S06f8RH,72Q04#:RI,j9%`?RJ%86S07#1S08#zRK#:RL,j<'MQ07$0J$0e#[#[#[#[#[#[#[#:RM+04RN'7%:?R?,YEROf7RP=4HC%eBRB#:RQ,09%eBRB#:RR,0<3ZRSCNX741YEIRT,0<10PGS09/7HRU172NPOPSCNX741YELRN,0=RVPU109TRW1MJ2004M'7POPSCNX741MJVS0:%:@RM,YERX'2PU17W2POPSCNX74%:ARA-0Y=1<=A1CA=+0=Q001<<A1CA<P2PPP2%8:S0;#1#zRS#:RW,YERU=6PGRYCK10PNRZ%1B#z$0WRB#:R['3R\%1BS0<#:RB'2S0=/5[/2XR]102NR^';'>X;4,|4P21<9AP4P2PHP2A6HUGCKS0>10HNR_/3[R`/2BS0?/5[?@X^'>X;4RaPPPPPPPPPYCK1;]Z&0Q;Rb&0O;R;%\1Rc&0K4Rd&0I4Re1_46Rf==ef%FERg%`S'fS0@,Qf%`>,fgR>'gRS9=ef40B20_e8R8P2P3g00GmRhg00HMRi+0^20]23=VhidB0\401H0[Rib2b3b4X04P2P2P2A62UGRhCK^04P2PHO1Rjb1P\152[/2XS0A/;_X74PZA@2X_X74p-0Rkg00ZaRl-0A4Rm%DlRl#DRn#HRo,Lm%dRS0B/ToRp/Lm001b3RRqP;PcPdPe%FAS0C9GefRr&0Z7R7Pe20@40Rs=?efRt20?e55keRuP7Pe%`K,fgRK,SfRv9?esPe%`@,fgR@,bvCaFEP8Pib2b3b4X04W91<2ARw%91Rx/>3Ry103NRz?IzX[[^04^9kP21<HCPHP1P=O4R{b1:0>ZX15\[20XZ[DAQ0=PqP;PcPdPePrP7PePuP7Pe%F[S0D,QvRv9?esPe%FBRu,bvCaFEP8Pib2b3b4X04X9k13z[Rz?IzB\y\w^04^9kP{b1:0>\BDAH0<H0;W8P2O11CA9P4PaPYPYPPPYPYCK10YN,;]PbP;PcPdA=eSfA=eSS60BeP8Pib2b3b4X04PhP2PhPhCK^04Pjb11r\B%XBRj#}1B`B,0BQ0?5W`[1q`B%UBS0Ef9Rh/0NS0F/3[RS/2BR]?I]B[1pSB1<B0f:R]/0NS0G/3[RY/2BRa,<B1Ca0'>[1tYBf;Ra@09N[R{/BB#X\j1o{Bf<Rw/0NS0H/3[Ry?@By\j1ByBP4f=Rr/0NS0I/3[S0J/2BP41]ELS0K%UERq%9LS0L%UN[[S0M%9ERZg01AfR|A^EL1UW5S0N%9N\|^5ZS0O%DnRn#DR}#HR~%HnRn'J1JmnS0P&0U6-0T4R6%D}R}#HS0Q5i4%HlRl/JmS0R$087{o+021JnmS0S%dB/TmS0T%D}S0U#HS0VAi46~<00pS0W'L;Rb3RP;&0R4Rp%\57c3?c1pS0XPdPePeAGesuP7Pe1_4:R:9?esS0YAGe:uElP7PePeA=eus,yeP7Q08,_4S08,Su/Q:9=evCwP7PeQ0C=?efP7Pe20?e<S0Z%FCR}9GefS0[5keP71gvu==e:FEFEP8Pib2b3b4X04X64X:4X9kQ0EAI33B[g019HS0E\j10B==Wz5[1CA3Q05,>9A6V[B/;<[[[[^04^64^:4^9kP2fARz#9P=P5PzPHPhP]PrO8b1bAb@bFbEbJb?b>b=b<15\BQ0=';P415`BR`Q0AA6hUGR\/0N';X7415`[/rX%XXR`#}15SB/5[RS1BSX,0X12SX3W[1qSX%UXRS15YB/5[RY/2XRj?IjX[1pYX1<X015{B/5[R{/2XRY,<X1CY0'>[1t{X15yB/5[Ry/BX#X\`1oyXQ0J/5B/5[Ry?@Xy\`1ByXP4f>Ry/0N?6[B/5[/2XP41]EFS0J%9FS0A%UG[\qS0=A^EF1V|X5ZS05%9G\|^5ZS0\1]EWS0]%9W%UU[\qS0^A^EW1V|X5ZS0_%9U\|^5ZS0`1]EM%9MS0aPS[\qA^EM1V|X5Z%9X\|^5ZQ0KQ0MQ0NQ0OQ0SQ0<#eRW#e#e#e#:#d/TmQ0W'LAi46n/JmQ0Q%:W#d/Tl1Jm~'L7{~;Rb3RP;Q0XPdPePeAGes@P7PePtAGef@ElP7PePeA=e@s,yeP71S:KRWQ0D'Q/guQ0D'gQ08,S@/Qf5=eCwP7PeQ0C=?e:P7PeQ0ZAGe:}S0C5keP7Q0@,Q:/g>/SK9=efFEFEP8Pib2b3b4X04X64X:4X9kAmx1X\SQ0E\`105N?6[B/5[10X=;W3[1CA5Am9=CA6<UGRA/0N,;=[[[[^04^64^:4^9kP2fHRk#9P]PkPhPyf?R[PzfDRBO8b1bAb@bGbHbIbKbLbTbFbEbJb?b>b=b<Q0?P2J07b<H0<H0;W8P2O1n200100001021100011000bUP2P<P2PACKRA10<NR`&0NJ,YERS/BER@'3/2S/5@?@X^'>X;4,|4e1MJ`?@X^,>AX;4,|4RAePAQ02P4P2P9P2A69UGS02CK109NRA,MJ/2XR@/;^'>X;410HG/7h10PT/7@PO10HCS0?,3h10PQ109R3ZCNP2Q0>1MJ_?@X^'>Q01P1PhP1P\CKQ0F,MJ101NR\7@X10wG/7r10aTQ0G,MJ/2X'7POA4rwC10aQ10]RS0G3ZCNP2P5PaP5A6aUGCKQ0H,MJ?@XVP`f@RV/0GR^/7zR_10[TR@/72POA4zVC10[Q10yR3ZRSCNX7410yTRu,7`S0HP_P2POPSCNX74R_13u`R{P_10[GS0F,3VP213@AS01POPSCNX74PbP;%\3?c1pS0>PdAOf:>S0ZQ04#`,fgRS'S1SfSS04/QW5=eP8Pib2b3b4X04X64101G>052T102T;W\^04^64P2P9P[O2b110<G>05yT/;{P4Q06,3[S0D/0TR{fBR\?4zGRWP2POA4\zC10VQ10[R3ZR@CNX7413z^R^,7{S0XA@2O@X74RA13^{PAQ001;9yA6yUG,;9Q09,3V=4WT?@O@P31;P[PVfCR@=4BGRAP\P2PGPTDPA4B@C10\Q10zR3Z7@OX;4S09A4@\GS00?4^T/rO%XOR_#}S0SA4AWTRW1BWO,0O12WO3W[1qWO%UORWfERY?4BGS0WQ00;4TRj/2ORv?IvO[1pjO1<O0S0<fFRj?4YGS0O?4ATS0N/2ORv,<O1Cv0'>[Q0N/tOfGS0N?4jGS0MQ0W;4TRv/BO#X\_1ovOQ0N=4kGS0KQ0O;4TRv?@Ov\_1BvOP4fI?4kGS0bQ0M;4T/2OP41]E?S0c%9?PW[\qS0dA^E?1V|X5ZS0e%9O\|^5ZS0fQ0JQ0=Q05Q0\1]EIS0g%9IS0h%UT[\qS0iA^EI1V|X5ZS0j%9T\|^5ZS0kQ0U#D#DRZ#DR|#HRE/JmQ0T%D|R|#DRq#D#H%H|R|9i46Q0B%HZRZ%dQR?Q0V%dCRk?n~o3n3n400'LAi46E/Jm%Hq1J|nQ0B/Tl1T?|Q0V9nkZ600m'L3{;Rb3RS0VP;%\=%\97c3%\<?c5p7c1S0BPdPePe1fgJRg9GesP7PePtAGefgElS0TP7PePeA=egs,yeS0UP7Q07,_4RZ=O:>R|Q03,_4RqQ0;,_4RE;O>;OSQ08,Sg/QfRg5=eCwP7PePeA?esEPe1bE}CaP7PePeA?esqPe1bq}CaP7PePeA?esZPe1bZ}CaP7PeQ0YQ0C5keS0CP7AO:Z}%FQ7Oq%FR7OE9=efFEFES0YFEP8Pib2b3b4X04X64X:4XB4XC4XD4Amx1O\WRRQ0E\_RZA45=GS0EQ06,3<;4TB09OP3R}';[AI99CR:Q0?10hQ5ZPQ0G5W9\:\:\:[R:[[^04^64^:4^B4^C4^D4P2PHfNS0GfORQfPR6fQR~PPPwPrfJfKfLRwfMRvO<b1bMbAb@bGbHbIbFbEb?b>b=b<b8PHP2DAW8P2O1A6[UG,;PA6VUGRPQ09Q00PzPPPGPTDP/rOQ0SPAP\A6zUGPGPTDPRA1BAO,0O12AO3W[1qAOQ0WP@A6\UGPGPTDPRA/2ORP?IPO\W1pAOQ0<Q0OPBA6@UGPGPTDPR@/2ORA,<O1CA0'>[1t@OQ0MPYA6BUGPGPTDPRB/BO#X\_1oBOQ0KPjA6YUGPGPTDPRY?@OY\_1BYOP4Q0bQ0NA6jUGPGPTDP/2OP4Q0cQ0dQ0eQ0fQ0JQ0=Q05Q0\Q0]Q0^Q0_Q0`Q0gQ0iQ0jQ0kQ0VP;Q0BPdPeQ0TP7PePeQ0UP7Q0@,QE/g>=Oq>=O|S==egCwP7Q0YFEP8Pib2b3b4X04X64X:4XB4XC4XD4Q0EP<Q02PGPTDP/;}\ZP:[\R^04^64^:4^B4^C4^D4P2P]P6P~fRfSPhPyP[PwPvQ0GPQO<b1bMbAb@bGbHbIbKbLbFbEb?b>b=b<b8PHP2DAW8P2O1n200100000021100011000Q0XP^Q0DPIPbP;PpPd%FI9?esP8Pib2b3b4Q0hP2b1RH1JomQ0Q,Lm1TknQ0R'L001b3RP;Q0>PdPeQ0CP7PeQ0[9ketRkP7PeQ0Z9?esPeQ0Z/bSCaFEP8Pib2b3b4X04X64Amx1CRSA435GR5?I5T\S[^04^64P2PzP\PrPyO4b1DxDA17^{206^{DAQ01P2J07b8Q0F/7VPVP[PFPbP;PpPd%FF9?esP8Pib2b3b4Q0AP2b1RVPbP;PcPdPePkP7PePtAGef>ElP8Pib2b3b4X04AI22CRCAmx1G[^04P2PzPrO2b1DxDAQ0HPuP<PLPbP;PpPd%FL9?esP8Pib2b3b4Q0LP2b1Rr1T?l/LmQ0P$08=Rmb+01P;PcPdPePkP7PeQ049?esQ04=GeKElP8Pib2b3b4X04101TRT?ITN\C^04P2P[PaO2b1DxDA17u`206u`DAQ0I,MJ/2XP2DAW8WSP1P2O2n2001000000121000000W8X;4P1P2O2n2001000000121100000bNQ0:&0LM+04Q0:PbP;PpPd%FM9?esP8Pib2b3b4Q0aP2b180MMDA1j=LA~=LrDA1j<IA~<IHDA1j9FA~9FVDAXRDXQDXPDWOXY4XX4XW4XV4o"). Qed.

(* [comment removed for export] *)
Section C.
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
  Notation BUF' := (BUF AI L).
  Notation RDONE' := (RDONE AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  Definition RQEXIT (code : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop := aat_exit code s RNG ms.

  (* [comment removed for export] *)
  Definition main_tail (buf : AsanCtrl.aptr) (cw cfg : Z) (payload : list Z) : @Monad.M APS Z :=
    status <- runA AAllocAsan cfg payload ;;
    status' <- (if Z.testbit cw 15 then
                  n <- alloc_countA AAllocAsan ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
                else mret status) ;;
    afree_M buf ;;;
    mret status'.

  Definition main_rest (buf : AsanCtrl.aptr) (content : list Z) : @Monad.M APS Z :=
    let len := zlength content in
    if len <? HDR_MIN then io_diag ioS DShortHdr ;;; afree_M buf ;;; mret 2
    else
      let cfg_word := le16 content in
      let config_len := Z.land cfg_word 0x7fff in
      if len <? HDR_MIN + config_len then io_diag ioS DCfgOverrun ;;; afree_M buf ;;; mret 2
      else
        let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
        let payload := skipn (Z.to_nat (6 + config_len)) content in
        let cfg := if 0 <? config_len then znth content 2 else 0 in
        alloc_initA AAllocAsan bitmap ;;; main_tail buf cfg_word cfg payload.

  Lemma main_model_eq :
    main_model ioS amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan) (alloc_countA AAllocAsan) (argv_Z argv)
    = (ra <- read_all ioS amalloc_M afree_M ASTAGE arg1 ;;
       match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end).
Proof.
ltac2:(rds2_run [(constr:(742000%Z), constr:(741936%Z)); (constr:(6135808%Z), constr:(6135744%Z)); (constr:(2147543134%Z), constr:(2147543126%Z))] (kr_t_AD_main_C ()) ["CANSEC1"; "C"] "p'0h01nh12rai002rah21lh36statush47status'h51zi013bufi027contenti03<count_allocsp;1p;2p;3p;4p;5p;6p;:p;7g01CnR0p4p711R1g01DaR2p4p710p8P1g01ERR3p4p710p8P1g01FJR1p4p710p8P2p4p7211g0000R4p4p710R5p8g01GCR6p4p710R7g01H?R8p4p7210p8P8p4p73110P2p4p7210p8g01I4R9p4p70R:p1001Bp4p710p8P:P7p8p101Ikp4p7210P5p8g002=j18Tg002bj1dTg003@j1PTg007\j1HTg00X;j2JTP0j1ZTP2j2WTg00Y_j1FTg00;Tj16Tg0110j2:Tg01JWj1<Tg01K5j1MTg004Vj1KTg01Khj3cj4ITg007<j1GTg01LDj47Tg01L`j1XTP3j3>Tg01M[j35TP6j1VTg00TDj1OTg01NOj2NTg00JNj29Tg01OGR3j1DTg01PEj1@Tg00V7j14Tg00hMj2CTg00KOj2?Tg01Q:j1BTg00\8j3ETg01QZj1LTg01ROj2Qj1YTg01SJj2RTg01T?j3Sj1]Tg017^j2TTg01U3j1UTP8j53Tg01Uoj2bTg00?Cj32Tg00>=j2aTg01Vmj1`Tg01Wbj2[TP4j6=Tg01Xaj4\Tg01Y@l:^TP1j7_Tf2R1g00C2R4g00EUR8f1R2f0R0D3p=1P1P9P2g01Z;R5P3g01[;R7P0F_p=;%40#4p=0P1P8P8P2P0D3p=Ag00Y@R:g00DRR;#8R<#8#8#dR=#PR>#HR?p,4argvR@'JRAg01\:RB#ZRC/W8RDg00GmREPD%F0%6<R<':#<%MBRF%H8RGg00ZaRHP?PG%K=R=9c>8RIP@CIRJ%G8RKC7#X5>CA5C8<RLV4RM51CRNPC%V9ROP8PG%OHRHPJPKC79;CFP6P9PDP0PLPEPD1N80RPg01];RQ'9g01^39>CF%D1=1CMV4RM51CPEPD%@0%4;R;#0RR#4#0#0#0#0#0#6RS'CRT,?Q,9Pg01^n9>CF=1CM1?<T#B=E80#L,QBPEP8g00E7RT%@2/CSRS'91R2<PTn0100000020000%8;#6/?S#B=E825SBPEPD%@1%6R'T%UBRRPEP8g01_iR1,90P0P1n010000002000095C8X085ACA5C80n0110300020000f4#DA5C82V451CX485ACX385ACV451Cn0100000020000n0100000020001n10110000020021101102X1OR4D3R1n0100000020001PCPOP8P>P8P=P?PHP@%G>C7CIR>9;CFP6P9PDP0PL1b20n10110000020020101102X1OD3R232X0:P8P<PEPD1:0<#<PNP1n0100000020001=2D2X58PGP>PCPOP8A;CF0P4D3=2D2X2G1aD2PGPH%`@R4PKC71[@HE=PEPD1:<<#<PNP1n0100000020001=2D2e%FAp,5ARGC2E=1JGJP?PGPIP@C\E=PCP9PFP5P3P7%YB%]BPRP4M:^=2D2eo"). Qed.

  (* [comment removed for export] *)
  Definition HDR (A cap : Z) (DATA : list byte) (cw Lc cfg sc : Z) : Prop :=
    6 + Lc <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ ablock_range A cap
    /\ 0 <= cw < 65536 /\ Lc = Z.land cw 32767 /\ 0 <= Lc < 32768 /\ Lc <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? Lc then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  (* [comment removed for export] *)
  Notation GST8 pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition RUN0 (bufp : AsanCtrl.aptr) (A cap : Z) (DATA : list byte) (cw Lc cfg sc : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem) (junk : list byte),
      ms = GST8 0x7fc88 x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Lc) (Z_to_bv 64 (A + 6 + Lc)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - Lc)) (Z_to_bv 64 sc) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw Lc cfg sc
      /\ BUF' mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  (* [comment removed for export] *)
  Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : APS) RNG (bufp : AsanCtrl.aptr) (A cap : Z) (DATA junk : list byte)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    s_diag (St:=APS) d = stderr_fwrite msg -> ro_bytes_b asegs PA (zb msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 + 64 <= PA -> PA + 31 + 64 <= 0x20e80 ->
    BUF' mm s RNG bufp A cap DATA junk -> ABASE' stdout_init mm -> RNGS' RNG ->
    implMA RNG (s_diag d ;;; afree_M bufp ;;; mret 2) s RQEXIT
      (GST8 0x7fd18 x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
    intros until mm. intros ED RO ML MRNG LOA HIA BU BA RG.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    destruct BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). pose proof BR as (BR1 & BR2 & BR3 & BR4).
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR.
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (_ & _ & _ & GSSP).
    rewrite ED.
    apply implMA_from_evtF. zstep. apply evtF_done.
    eapply implMA_bind.
    { apply implMA_of_implAM.

eapply (afwrite_diag_proof RNG) with (lo := LO) (s := msg) (A := PA); rewrite ?unsigned_lit by lia;
        first [ exact SE | reflexivity | exact ST | exact MI | exact ROD | exact RGimg | exact RRF | exact MRNG
              | split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ P0h) | idtac ].
      all: first [ apply fmt_bytes_at; [exact MI| exact RO| lia| rewrite ML; lia]
                 | rewrite ML; lia
                 | rewrite ML; reflexivity
                 | lia
                 | unfold AFWRITE_DEPTH; lia | unfold KHIGH; lia
                 | eapply rng_sub'; [exact RGstk| lia] ]. }
    cbv beta. intros [] st' RNG' ms' [-> PO].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & SEW & SSP1 & ->).
    rewrite ?unsigned_lit in MU1, ST1 by lia. fix_ret.
    assert (HW1 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
    assert (HP1 : AHEAP AI L RNG (aps_m s) [HB bufp A cap] m1).
    { eapply (AI_frame AI); [exact P0h| exact MU1| exact WM1|]. pose proof (AI_layout AI _ _ _ _ _ P0h) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
    assert (BA1 : ABASE' stdout_init m1).
    { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA| exact HW1| exact MU1| exact WM1| exact MI1| exact ST1| exact SEW|].
      exists errv. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU1| exact WM1]| exact ERR|]. intros a' Ha'. rewrite ?errno_addr_ATP in Ha'. cbn in Ha' |- *. lia. }
    pose proof BA1 as (ST1' & _ & FR1 & AS1 & SE1 & GU1 & TR1 & HI1 & ROD1 & RCS1 & RCB1 & RSG1 & [errv1 ERR1] & SOF1). unfold AMFRAME in FR1.
    clear MU1 WM1.
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (dfree_M AI DFREE L RNG) with (lo := LO) (p := bufp) (A := A) (n := cap); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
        first [ exact HP1 | left; reflexivity | exact MI1 | exact ST1 | exact BOT | unfold AFREE_STACK; lia | exact UF_ff0 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | match goal with H : aps_ok _ _ |- aps_ok _ _ => exact H end | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
    cbv beta. intros [] s2 RNG2 ms3 [SOE3 PO].
    destruct PO as (LE2 & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
    rewrite ?(unsigned_lit (usp + -128)) in ST3, HPR3, HSP3 by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in HEAP3.
    pose proof (AI_hb_ids AI _ _ _ _ _ HP1) as ND.
    rewrite (lb_remove_headA bufp A cap [] ND) in HPR3, HEAP3.
    assert (BA3 : ABASE' stdout_init m3).
    { eapply (ABASE_after_dpost AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI canary);
        [exact HPR3| exact HSP3| exact HEAP3| exact MI3| exact ST3| exact BA1]. }
    pose proof BA3 as (_ & _ & FR3 & AS3 & SE3 & GU3 & _).
    assert (RG2' : RNGS' RNG2) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE2| exact RG]).
    pose proof RG2' as (RGstk2 & _ & RGimg2 & RGimsh2 & _ & _ & _ & _ & RG02 & _).
    apply implMA_ret. unfold RQEXIT.
    eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 USP16 USPLO USPHI canary);
      first [exact FR3 | exact ST3 | exact AS3 | exact HEAP3 | exact MI3 | exact HT | exact RGimg2 | exact RGimsh2 | exact RG02 | exact GU3 | idtac].
    - rewrite (aps_so_of_rest _ _ SOE3). cbn [aps_so aset_m]. rewrite SO0. destruct BA3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SOF3). exact SOF3.
    - apply stderr_wfile0_file. exact SE3.
    - eapply rng_sub'; [exact RGstk2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma phaseC : forall bufp content s RNG ms,
    RDONE' bufp content s RNG ms ->
    (forall DATA A cap cw Lc cfg sc s1 RNG1 ms1, content = map bv_unsigned DATA -> RUN0 bufp A cap DATA cw Lc cfg sc s1 RNG1 ms1 ->
       implMA RNG1 (main_tail bufp cw cfg (skipn (Z.to_nat (6 + Lc)) content)) s1 RQEXIT ms1) ->
    implMA RNG (main_rest bufp content) s RQEXIT ms.
Proof.
    intros bufp content s RNG ms RD K.
    destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & A & cap & fd & DATA & junk
                    & -> & HC & BU & BA & ARG & RG & FRM).
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR.
    pose proof BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). unfold MAX_INPUT in CAPR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (GSE & PSE & _ & GSSP). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
    unfold main_rest. rewrite LENZ. unfold HDR_MIN.
    remember (length DATA) as nD eqn:HnD.
    apply implMA_from_evtF. zstep. zstep.
if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      cbn [io_diag ioA io_S].
      eapply (diagC_exit DShortHdr s_short AS_SHORT); [reflexivity| apply s_short_ro| reflexivity| unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold AS_SHORT; lia| unfold AS_SHORT; lia| exact BU| exact BA| exact RG]. }
    (* [comment removed for export] *)
    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
    pose proof (u8ro_read asegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as Lc eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (Z.of_nat nD <? 6 + Lc) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      cbn [io_diag ioA io_S].
      eapply (diagC_exit DCfgOverrun s_over AS_OVER); [reflexivity| apply s_over_ro| reflexivity| unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold AS_OVER; lia| unfold AS_OVER; lia| first [exact BU | rewrite <- HnD; exact BU | rewrite HnD in BU; exact BU]| exact BA| exact RG]. }
    replace (Z.of_nat nD <? 6 + Lc) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.
    (* [comment removed for export] *)
    destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + Lc)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at asegs mm (A + 2 + Lc) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + Lc)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + Lc)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + Lc) in X by (cbn [length] in *; lia). exact X. }
    rewrite skipn_map, EQ4, le32_cons.
    remember (bv_unsigned q0 + bv_unsigned q1 * 256 + bv_unsigned q2 * 65536 + bv_unsigned q3 * 16777216) as BM eqn:EBM.
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read asegs mm _ _ 1 q1 (wa (A + 2 + Lc + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 0 q0 (wa (A + 2 + Lc)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 2 q2 (wa (A + 2 + Lc + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 3 q3 (wa (A + 2 + Lc + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. apply evtF_done.
    eapply implMA_bind. { apply atarget_alloc_init_spec. }
    cbv beta. intros [] s' RNG' ms' (-> & -> & ->).
    fix_ret.
    replace (Z_to_bv 64 (A + 2 + Lc + 4)) with (Z_to_bv 64 (A + 6 + Lc)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - Lc + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - Lc)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw Lc _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 21 eexists. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? Lc); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [first [exact BU | rewrite <- HnD; exact BU | rewrite HnD in BU; exact BU]|]. split; [exact BA|]. split; [exact ARG|]. split; [exact RG| exact FRM].
  Qed.
End C.
End CANSEC1.
