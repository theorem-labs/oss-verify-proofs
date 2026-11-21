(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (arep_rt_frameD, arelro_frameD, ashadow_avail_frameD and 7 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ACanary AModelFacts ARep ALayout AHeapP ARepKit ARepFrame AFrameD.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
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
Ltac2 kr_t_ARepFrameD () := "C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothW7AFrameD<cells_frameDC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5azeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AFrameD<azero_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5BothW7ACanaryApremap_canary_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5BothW9ARepFrameAdisjoint_from_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AFrameD;junk_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib5BothW7AFrameD=u32arr_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib5Lists4List:length_appK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5BothW9ARepFrame<max_count_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep;bstate_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6AMAGICC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5BothW:ARepFrameDAaslot_busy_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib5BothW7AFrameD;fill_frameDC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section FramesD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.

Ltac xcell := eapply cells_frameD; [eassumption | exact MU | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)

Lemma arep_rt_frameD : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) (rt_hulls L) -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma arelro_frameD : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)

Lemma ashadow_avail_frameD : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frameD; [exact Z1 | exact MU | exact D1] | eapply azero_frameD; [exact Z2 | exact MU | exact D2]].
Qed.

Lemma arep_rt2_frameD : arep_rt2 m -> disjoint_from W 0x14bf2c 1 -> disjoint_from W 0x14beb8 8 -> disjoint_from W 0xb3f50 8 -> arep_rt2 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepFrameD ()) ["CANSEC1"; "FramesD"] "h01Hh12D1h22D2h32D3h42R1h52R2h62R3p;1p;2p;3p;8p;4p10000p4p70p1000gp4p710p8g011fj1BTg006Uj15Tg0060j13Tg00;Oj1>Tg00;mj2:Tg00=ej1DTg009Lj1CTg009lj39Tg00?Oj1ATg00AoR0j2@Tg003Vj34Tg00Cdj1<Tg00D]j1;Tg00BJj8=Tg00CIj4?Tg0073j18Tg00@Dj4ETf0R1#3#8p=7%31#3p=1%81#3p=2%81#8p=0g00FPf2R2f1R3P1CEp=6p,1mR4#BP0g00GER5#7#1#2#0#0#0#1#2#0#1#5R6g00E[R7%35#1R8#>g00IUR9':#D%C7R:39R;564R<%75#1#2#0#0#2#2#0#2#1#5R=%38#1#>R>/:9#A=97:R9564R?%35#0#1#0#0#0#7#7#1#1#5R@%35#2#2#0#0#1#0#2#7#1#5,:>#A=97:R:564R7'@R>p,1WRA%55746R5%58R894A=RBA4A@8R8p,2m'RC#B[[[RDP1P0P?P7PDP1A6C6;A6C=9RDA6C@:R0'@PAP4PCP6P;f8p,2MUREP2%<;#;94A6eG=PDP0PAP4PCP=P9f4PEP3%<9#;94A=eG=PAP4PCP@P:f3PEP1%<:#;94A@eG=C?C?X38X2BX15X67X5?P3P1O2n2001000000121000000X0>X4<P3P1O2n2001000000121000000W0o"). Qed.

(* [comment removed for export] *)
Lemma arep_rt3_frameD : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
ltac2:(rds2_run [(constr:(6203920%Z), constr:(6345424%Z))] (kr_t_ARepFrameD ()) ["CANSEC1"; "FramesD"] "h03CLRh11Hh22cbh31Dh42D0h52D1h63D10h73D11h83D12h93D13h:3D14h;2D2h<2D3h=2D4h>2D5h?2D6h@2D7hA2D8hB2D9hC2R1hD3R10hE3R11hF3R12hG3R13hH3R14hI3R15hJ3R16hK3R17hL2R2hM2R3hN2R4hO2R5hP2R6hQ2R7hR2R8hS2R9hT2RThU1pp%0p;1p;2p;3p;5p;8p;4p10000p4p70p1000gp4p710p8g012^j1]Tg002<j2kTg002\j3bTg0039j3aTg003Vj3STg005Oj37Tg0060j10Tg006Uj1ITg0073j11Tg009Lj1XTg009lj34Tg00:Lj5;Tg00:kj58Tg00;Oj1WTg00;mj2GTg00>Zj1VTg00=ej1jTg00L>j1iTg00Q8j1hTg013Vj1ETg0145j2gTg014jj2\Tg00AoR0j23Tg00BJj89Tg015Dj1eTg007Xj4dTg00?Oj1[Tg00@Dj4cTg00Cdj1^Tg00D]j1ZTg00CIj4YTf0R1#0#1#1#0p=?%01#1#1#1p==%11#1#0#1p=H%01#0#1#1p=K%01#0#0#Ip=5%01#0p=Ug00E=R2P2f1R3P1Cdp=:%11#1#0#0p=C%11#1#1#1p=R%01#0#0#0p=6%11#1#1#0p=M%11#0#1#0p=A%11#0#0#1p=B%01#1#0#0p=L%11#0#1#1p=Q%01#1p=P%11#0p=O%01#0#0#1p=@%01#1#0p=N%11#0#0#0p=Jg00E[R4f2R5%I3'G#[;41p=>g00FPP5P3P1Ccp=2%11#1p=`%01#0#0#0#0#0#0#0p=FA4431p=T%[3=441p=_%^1#Z9S53p=<%^1#Zp=ff6f5S00f4f3P5P3P1CYCYp=Dp,1mR5#]1k22R6p,1WR7Ab221Aa2213SXU6R2g016H37P6P2g00GER8#?#=#H#K#5R9%U8R:#0R;#0R<#IR=':R>%?8#=#C#R#5R?%I;R@':RA%?8#=#H#6#5RB/:@RC%?8#=#M#A#5RD/:@RE%?8#=#C#H#5RF/:@RG%08#B#=#C#R#5RH/:@RI%08#B#=#M#L#5RJ/:@RK%=8#L#?#6#5RL%I:R:':RM%?8#R#?#Q#5RN%I8RO':RP%08#B#K#Q#K#5RQ/::R:%P8#B#6#O#@#5RR/:=R=%?8#=#R#C#5RS/:@RT%08#B#K#Q#L#5RU/:@RV%08#B#=#M#6#5RW/:@RX%08#B#=#M#K#5RY/:@RZ%18#U#@#A#A#A#5R[/:@R@%X6R\546R]546R^546R_546R`546Ra546Rb546Rc546Rd546Re546Rf546Rg546Rh546Ri546Rj546RkP1D;P2P>O1P6P2P>PkP3D8A762kP6P2PAPjP1D;P2PAO1P6P2PAPjP3D8A762jP6P2PCPiP1D;P2PCO1P6P2PCPiP3D8A762iP6P2PEPhP1D;P2PEO1P6P2PEPhP3D8A762hP6P2PGPgP1D;P2PGO1P6P2PGPgP3D8A762gP6P2PIPfP1D;P2PIO1P6P2PIPfP3D8A762fP6P2PKPeP1D;P2PKO1P6P2PKPeP3D8A762eP6P2PMPdP1D;P2PMO1P6P2PMPdP3D8A762dP6P2PPPcP1D;P2PPO1P6P2PPPcP3D8A762cP6P2P:PbP1D;P2P:O1P6P2P:PbP3D8A762bP6P2P=PaP1D;P2P=O1P6P2P=PaP3D8A762aP6P2PTP`P1D;P2PTO1P6P2PTP`P3D8A762`P6P2PVP_P1D;P2PVO1P6P2PVP_P3D8A762_P6P2PXP^P1D;P2PXO1P6P2PXP^P3D8A762^P6P2PZP]P1D;P2PZO1P6P2PZP]P3D8A762]P6P2P@P\P1D;P2P@O1P6P2P@P\P3D8A762\P0%U<R<#WR\%N8#A#H#A#J%N8#=#C#B#J%X4R45>\3>R29259R6%08#`#6#O#H#P#C=>\4R@925?R]%N8#=#A#@#6=>\4RZ925BR^%N8#Q#C#M#L=>\4RX925DR_%08#A#C#H#P#C=>\4RV925FR`%0<R<#0#6RT#6#F#F=>\4Ra925HR=%J<#6R<#J#6Rb#1#6#@#6#@#6#@#6#@=>\4R:925JRc1G\O#V/T4RP925LRd%W;R;/GO#j/T4RO925NRMg00IU,G\#V/T4Re925QRK1G\U1G\S/_4'_Rf925RRI%O8#L#J#O#==>\4Rg925SRGA>\T4RT925URh%0b#6#@#F=>\4Rb925WRE%0<#6#@#F#F#F#F=>\4R\925YR<%i;#hR;%18#6#?#B#P#A#5R8g017F#E#E#E#E#E#E#E#E/g1/T4R4525X2;'\RiA25[TRC'3Rj'3RA'3Rk'3R>'3Rl'3Rm'3Rn'3Ro'3Rp'3Rq'3Rr'3Rs'3Rt'3Ru'3Rvp,2m'Rw#]RxfQS01P0P]PuPxP1P0P^PtPxP1P0P_PsPxP1P0P`PrPxP1P0P=PqPxP1P0PcPpPxP1P0PdPoPxP1P0PMPnPxP1P0PKPmPxP1P0PIPlPxP1P0PGP>PxP1P0PhPkPxP1P0PEPAPxP1P0P<PjPxP1P0PiPCPxP1A2w92A2w?@R0A2wBZRyA2wDXS02A2wFVS03A2wHaS04A2wJ:S05A2wLPS06A2wNOS07A2wQeS08A2wRfS09A2wSgS0:A2wUTS0;A2wWbS0<A2wY\S0=A2w84X2;,\;S0>A2w[TS0?'3S0@'3S0A'3S0B'3S0C'3S0D'3S0E'3S0F'3R;'3R4'3R8'3Rz'3R{'3R|'3R}'3P7P5PwP9P2fmp,2MUR~p+01PA<792eG9P0P}P7P5PwP?P@fiP~p+01NA<7?@eG9PyP|P7P5PwPBPZfeP~p+01LA<7BZeG9Q02P{P7P5PwPDPXfaP~p+01JA<7DXeG9Q03PzP7P5PwPFPVf]P~p+01HA<7FVeG9Q04P8P7P5PwPHPafYP~p+01FA<7HaeG9Q05P4P7P5PwPJP:fUP~p+01DA<7J:eG9Q06P;P7P5PwPLPPQ01P~p+01BA<7LPeG9Q07Q0FP7P5PwPNPOfMP~p+01@A<7NOeG9Q08Q0EP7P5PwPQPefIP~f}A<7QeeG9Q09Q0DP7P5PwPRPffEP~f{A<7RfeG9Q0:Q0CP7P5PwPSPgfAP~fyA<7SgeG9Q0;Q0BP7P5PwPUPTf=P~fw%fTRg9S7UeG9Q0<Q0AP7P5PwPWPbf9P~fuA<7WbeG9Q0=Q0@P7P5PwPYP\Q00P~fsA<7Y\eG9Q0>Q0?%ewP7P5PwP[PTP1P~fqAS7[geG9FDFDFDFDFDFDFDFDPxeXKCXJiP3P1O2n2001000000121000000X1jXI<P3P1O2n2001000000121000000X1AXHEP3P1O2n2011000000121000000X1kXGhP3P1O2n2011000000121000000X1>XFGP3P1O2n2011000000121000000X1lXEIP3P1O2n2011000000121000000X1mXDKP3P1O2n2011000000121000000X1nXSMP3P1O2n2011000000121000000X1oXRdP3P1O2n2011000000121000000X1pXQcP3P1O2n2011000000121000000X1qXP=P3P1O2n2011000000121000000X1rXO`P3P1O2n2011000000121000000X1sXN_P3P1O2n2011000000121000000X1tXM^P3P1O2n2011000000121000000X1uXL]P3P1O2n2011000000121000000X1vXC6P3P1O2n2011000000121000000b0b:b0b9b0b8b0b7b0b6b0bBb0bAb0b@b0b?b0b>b0b=b0b<b0b;b0b5b0b4b0b3W0WTo"). Qed.

(* [comment removed for export] *)
Lemma ainstance_frameD : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma aregion_cells_frameD : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  destruct RC as (A1 & A2 & A3 & A4 & A5).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frameD; [exact A3 | exact MU | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frameD; [exact A5 | exact MU | intros _; exact De].
Qed.

(* [comment removed for export] *)
Lemma afreearray_frameD : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  destruct FA as (A1 & A2 & A3).
  split; [| split].
  - eapply u32arr_frameD; [exact A1 | exact MU |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A2 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A3 | exact MU | intros _; exact DS].
Qed.

(* [comment removed for export] *)
Lemma acache_cells_frameD : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frameD; [exact A1 | exact MU |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frameD; [exact A2 | exact MU |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)

Lemma aslot_busy_frameD : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact SB | exact MU | intros _; exact D].
Qed.

(* [comment removed for export] *)
Lemma aslots_updateD : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as (EB & D & WFB). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + destruct (WFB b eq_refl) as (C1' & K1 & FIT1).
      eapply aslot_busy_frameD; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frameD; [exact SL | exact MU | intros _; exact D].
  - eapply junk_frameD; [exact UND | exact MU | exact DU].
Qed.

(* [comment removed for export] *)
Lemma aslot_shadow_updateD : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells bsegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frameD; [exact SL | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frameD; [exact UND | exact MU | exact DU].
Qed.
End FramesD.
End CANSEC1.
