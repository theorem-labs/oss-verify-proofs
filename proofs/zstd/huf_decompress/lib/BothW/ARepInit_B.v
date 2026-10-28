(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed BothHandoff.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
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
Ltac2 kr_t_ARepInit_B () := "C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission2AS:MainExport:mimg_coverK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6arelroK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_LOC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_HIC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth>asan_mem_factsK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact00K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp01K47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact01C5ARocqVerifyHarness?AgentSubmission2AS:MainExport9mfact_eqbC5ARocqVerifyHarness?AgentSubmission2AS:MainExport:mfact_findC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8mfact_okC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesK47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kitEbytes_eq_of_unsigned'C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit;rw_cells_tlC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit;rw_cells_hdC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp04K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_ctxC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_tC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit=rw_cells_consC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7arep_rtC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bK46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit9img_chunkI47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATP88C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ATSDc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B<flags85_initc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B=cflags34_initC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8arep_rt2K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW7ACanaryApremap_canary_anyC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8arep_rt3K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_VC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_ptr_arrayC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_A3ST0C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nresC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nsecC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission5BothW4ARep9ainstanceK46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<K_SPACE_SIZEC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ@aquar_glob_constC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5Q_MAXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5Q_MINC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7Q_CACHEC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6qfirstC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5qlastC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ8abatchesC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7aqcacheI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00I5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7qbatchc00C5ARocqVerifyHarness?AgentSubmission5BothW7AQConst9AQ_GCACHEC56Stdlib6NArith6BinNat1N3eqbC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit9byte_zeroC56Stdlib6NArith6BinNat1N4div2C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit6zscanNC56Stdlib6NArith6BinNat1N3addC56Stdlib6NArith6BinNat1N3subC47Corelib7Strings:PrimString6stringI47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3powC56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N2ltK47Corelib4Init9Datatypes6option01C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6NArith6BinNat1N7add_0_rC56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;hex_byte_atC46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init5Logic9False_indc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B8zscanN_SC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6NArith6BinNat1N3divC56Stdlib6NArith6BinNat1N4succC56Stdlib6NArith4Nnat5Nat2N8inj_succC56Stdlib6NArith6BinNat1N3mulC56Stdlib6NArith6BinNat1N;pow_succ_r'C56Stdlib6NArith6BinNat1N7div_modC56Stdlib6NArith6BinNat1N6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3remC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6NArith6BinNat1N6mod_ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6NArith6BinNat1N9add_assocC47Corelib4Init9Datatypes?andb_true_introC56Stdlib6NArith6BinNat1N8div2_divC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_powC56Stdlib6ZArith4Znat3N2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat3N2Z7inj_mulC56Stdlib6ZArith4Znat3N2Z7inj_divC56Stdlib6ZArith4Znat3N2Z7inj_remC56Stdlib6ZArith4Znat3N2Z7inj_addC56Stdlib6ZArith4Znat3N2Z;inj_sub_maxI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission2AS;AsanHexScan6zscanZC4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothUTgt_huf_decompress_both_seg_bytes_003C5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_BASEC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit4SEG3C5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_SIZEC56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6leb_leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission2AS;AsanHexScan<zscanZ_soundc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B?zscanN_completeC46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B:aia_scan63C46Stdlib9micromega8ZifyInst7Inj_N_ZI47Corelib7Numbers7BinNums8positive00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8zexp_eqbC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8mwr_findC5ARocqVerifyHarness?AgentSubmission2AS:MainExport2zvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC56Stdlib6ZArith4Znat3Z2N2idC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit<img_zero_stkC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit9wr_at_subC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6aintalC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst<AIA_MAP1_LENC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_MAP1c5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_B8aia_scan".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0xb1000 0xb3000 IMG. apply IMG. lia. Qed.

  (* [comment removed for export] *)
  Lemma flags85_init : rw_cells bsegs m 0xb7b4d [C1 (Z_to_bv 8 1)].
Proof.
    mf V m HM (MCell (ZLit 752456) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells bsegs m 752456 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Lemma cflags34_init : rw_cells bsegs m 0x14be4a [C1 (Z_to_bv 8 1)].
Proof.
    mf V m HM (MCell (ZLit 1359432) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells bsegs m 1359432 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Theorem arep_rt_init : arep_rt L m.
Proof.
    unfold arep_rt.
    aimg V m HM 0xb2108 [C8 (Z_to_bv 64 0x149da0)] I1.
    aimg V m HM 0xb2118 [C8 (Z_to_bv 64 0x14be28); C8 (Z_to_bv 64 0xb7af8); C8 (Z_to_bv 64 0xba2f8);
                          C8 (Z_to_bv 64 0xbafe8); C8 (Z_to_bv 64 0xbaff0); C8 (Z_to_bv 64 0xbafe0)] I2.
    aimg V m HM 0xb2148 [C8 (Z_to_bv 64 0xb3fa8)] I3.
    aimg V m HM 0xb2c90 [C8 (Z_to_bv 64 0xbafd9)] I4.
    aimg V m HM 0xb2d80 [C8 (Z_to_bv 64 0x10)] I5.
    aimg V m HM 0xb3fa0 [C8 (Z_to_bv 64 0xab458); C8 (Z_to_bv 64 0xab85c)] I6.
    aimg V m HM 0xbafe8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x13c560 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x13c562 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x14bdc0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x5ed2a0 [C4 (Z_to_bv 64 0)] I11.
    mf V m HM (MCell (ZLit 752312) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 752320) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 752322) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 752324) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 752376) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 752380) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 752384) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 752388) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 752392) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 752420) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 752424) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells bsegs m 752424 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 762616) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 760668) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 760672) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 760676) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 765912) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 765913) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 765920) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 765948) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1295713) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1351072) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1359432) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1359520) 8 (ZLit 18446744073709551615)) F23.
    mf V m HM (MCell (ZLit 6214200) 8 (ZLit 6350392)) F24.
    mf V m HM (MCell (ZLit 6350392) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)) F26.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))) F27.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|]. split; [exact I6|].
    split; [apply rw_cells_cons; [exact F1| apply rw_cells_cons; [exact F2| apply rw_cells_cons; [exact F3| exact F4]]]|].
    split; [apply rw_cells_cons; [exact F5| apply rw_cells_cons; [exact F6| apply rw_cells_cons; [exact F7| apply rw_cells_cons; [exact F8| exact F9]]]]|].
    split; [apply rw_cells_cons; [exact F10| exact F11']|].
    split; [exact flags85_init|].
    split; [exact F12|]. split; [exact F13|]. split; [exact F14|]. split; [exact F15|].
    split; [apply rw_cells_cons; [exact F16| exact F17]|].
    split; [apply rw_cells_cons; [exact F18| exact I7]|].
    split; [exact F19|].
    split; [apply rw_cells_cons; [exact I8| apply rw_cells_cons; [exact F20| exact I9]]|].
    split; [exact F21|]. split; [exact I10|]. split; [exact F22|]. split; [exact cflags34_init|]. split; [exact F23|].
    split; [exact F24|]. split; [exact F25|]. split; [exact I11|]. split; [exact F26| exact F27].
  Qed.

  Theorem arep_rt2_init : arep_rt2 m.
Proof.
    unfold arep_rt2.
    mf V m HM (MCell (ZLit 1359656) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells bsegs m 1359656 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1359544) 8 (ZLit 0)) F2.
    aimg V m HM 0xb3f50 [C8 (Z_to_bv 64 0xabce4)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  Theorem arep_rt3_init : arep_rt3 m.
Proof.
    unfold arep_rt3.
    aimg V m HM 0xb3e98 [C8 (Z_to_bv 64 0xaada8); C8 (Z_to_bv 64 0xa7c98)] I1.
    aimg V m HM 0xb3e78 [C8 (Z_to_bv 64 0xb0b5c)] I2.
    aimg V m HM 0xb3e80 [C8 (Z_to_bv 64 0xa7a10)] I3.
    aimg V m HM 0xb3f50 [C8 (Z_to_bv 64 0xabce4)] I4.
    aimg V m HM 0xb3e68 [C8 (Z_to_bv 64 0xab35c)] I5.
    mf V m HM (MCell (ZLit 1359480) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1359648) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 762624) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 752472) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1351064) 4 (ZLit 0)) F5.
    aimg V m HM 0xb2108 [C8 (Z_to_bv 64 0x149da0); C8 (Z_to_bv 64 0xb3fe0)] I6.
    aimg V m HM 0xb3fe0 [C8 (Z_to_bv 64 0x19227)] I7.
    mf V m HM (MCell (ZLit 1351072) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1359616) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1359640) 8 (ZLit 72339073309605888)) F8.
    mf V m HM (MCell (ZLit 6346064) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].
  Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 748728) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 748744) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 748760) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 748768) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0xb6d08 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 749376) 1 (ZLit 0)) F6.
    aimg V m HM 0xb7070 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 748736) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells bsegs m 748736 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 748752) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed.

  (* [comment removed for export] *)
  Theorem aquar_glob_const_init : aquar_glob_const m.
Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 749488) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 749496) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 749504) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 749576) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 749577) 1 (ZLit 0)) F5.
    aimg V m HM 0xb700a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0xb7010 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zscanN_S : forall s f base n, zscanN s (Datatypes.S f) base n =
    (if N.eqb n 0 then true else if N.eqb n 1 then byte_zero s base
     else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool).
Proof. reflexivity. Qed.
  Lemma zscanN_complete : forall s f base n,
    (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) -> zscanN s (Datatypes.S f) base n = true.
Proof.
    intros s f. induction f as [|f IH]; intros base n Hn Hz; rewrite zscanN_S;
      (destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|]); destruct (N.eqb_spec n 1) as [E1|N1].
    1, 3: (pose proof (Hz 0%N ltac:(lia)) as Z0; rewrite N.add_0_r in Z0; unfold byte_zero; rewrite Z0; reflexivity).
    - exfalso. change (2 ^ N.of_nat 0)%N with 1%N in Hn. lia.
    - cbv iota zeta. rewrite N.div2_div. rewrite Nat2N.inj_succ, N.pow_succ_r' in Hn.
      pose proof (N.div_mod n 2 ltac:(lia)) as DM. pose proof (N.mod_lt n 2 ltac:(lia)) as ML.
      set (h := (n / 2)%N) in *. set (r := (n mod 2)%N) in *. set (p := (2 ^ N.of_nat f)%N) in *. clearbody h r p.
      apply andb_true_intro. split; apply IH.
      + lia.
      + intros i Hi. apply Hz. lia.
      + lia.
      + intros i Hi. rewrite <- N.add_assoc. apply Hz. lia.
  Qed.
  Lemma aia_scan63 : zscanZ AsanUbsan_seg_bytes_003 (AIA_BASE - SEG3) AIA_SIZE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma aia_scan : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.
Proof.
    apply (zscanN_complete _ 63).
    - apply N.leb_le. vm_compute. reflexivity.
    - intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *. lia.
  Qed.

  Theorem aintal_init : aintal false m.
Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x149d88 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xbb500 (0xbb500 + 0x81030) IMG. mwr V m HM (ZLit 724992) 5620432 W.
    assert (EQN : Z.of_N (Z.to_N AIA_SIZE) = AIA_SIZE) by (apply Z2N.id; unfold AIA_SIZE; lia).
    pose proof (img_zero_stk (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) m AIA_BASE aia_scan) as K. rewrite EQN in K.
    apply K.
    - unfold AIA_BASE, SEG3. reflexivity.
    - unfold AIA_BASE, AIA_SIZE. lia.
    - intros i Hi. apply IMG. unfold AIA_BASE, AIA_SIZE in Hi. lia.
    - eapply wr_at_sub; [exact W| unfold AIA_BASE; lia| unfold AIA_BASE; lia| unfold AIA_BASE, AIA_SIZE; lia].
  Qed.
End B.
End CANSEC1.
(* [comment removed for export] *)
