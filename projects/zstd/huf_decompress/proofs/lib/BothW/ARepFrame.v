(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (61 recorded proofs replaced by written proofs (get_cls_put_cls_eq, get_cls_put_cls_ne, max_count_eq and 58 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ACanary AModelFacts ARep ALayout AHeapP ARepKit.
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
Ltac2 kr_t_ARepFrame () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC46Stdlib5Lists4List7existsbI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps@lookup_insert_eqC46Stdlib5Lists4List6nth_okC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes2idI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC35stdpp4base6lookupC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6astate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionI59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C35stdpp8fin_maps:map_eq_iffI35stdpp8fin_maps6FinMap00C35stdpp4base4FMapI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib5BothW9ARepFrame7st_fastC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00c59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame@get_cls_set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame@get_cls_set_nextC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame;st_fast_clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame<max_count_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divc59OSSVerify5KrLib5BothW9ARepFrame@st_fast_countersC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame8shad_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz03C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib5BothW9ARepFrame9slots_sepC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC56Stdlib6ZArith6BinInt1Z7mul_1_lc59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame;aregion_modC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03C56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z7add_modC46Stdlib5Lists4List4findC59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep5aconc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9nth_errorC47Corelib4Init3Nat3subC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4ListCapp_removelast_lastC47Corelib4Init3Nat3addC46Stdlib5Lists4List>nth_error_app2C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:removelastC46Stdlib5Lists4List4lastC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib4Init5Logic4True01C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib5BothW9ARepFrameAlength_removelastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:fill_mergeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5azeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame;azero_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ACanaryApremap_canary_anyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrameAdisjoint_from_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib5BothW9ARepFrame<u32arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;bstate_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6AMAGICC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5BothW9ARepFrame@aslot_busy_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame:fill_frameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List@nth_error_repeatC46Stdlib5Lists4List2InC46Stdlib5Lists4List9find_someC46Stdlib4Bool4Bool=andb_true_iffC59OSSVerify5KrLib4Spec8AsanCtrl6rz_logC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z7pow_0_rC59OSSVerify5KrLib5BothW;AModelFacts:rz_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFacts?rounded_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame<rz_size_ge16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepFrame?rounded_size_geC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z<divide_trans".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma get_cls_put_cls_eq : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_cls_put_cls_ne : forall c c' r st, c' <> c -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma get_cls_set_next : forall v st c, get_cls (set_next v st) c = get_cls st c.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepFrame ()) ["CANSEC1"] "h01ch12sth21vp;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p710R1p1000kp4p710R0p8P1p1001Gp4p710R1p8p1001ep4p710R2p1002CR3p4p710R4p8P2P3p4p7210R3p8p1002\p4p70R5p1003Sp4p710p8P5P1p8P5p1003jp4p710p8p1004FR5p4p710R6P2p8P6P4p8P6P3p8P6p1004Zp4p73110p8P5p4p741110R5p100Pnp4p73101p8p1005Np4p710P0p8p1004lp4p7<111111111110P1p8p1005ip4p7<111111111110P1p8p1006Kp4p741110R1p100QJR0p4p7511100R6p8P6P1p8p1006dp4p741110R1P0p4p76111100R6p8P6P1p8p1007<p4p741110R1P0p4p771111100R6p8P6P1p8p1007\p4p741110R1P0p4p7:1111111100R0p8P0P1p8p100Qdp4p7200R1P5p8P5P1p8g00Icj21Tg009mj20Tg00R6g00MKg00Lmg00K8f1f0'1'0W0W1W2o"). Qed.
Lemma get_cls_set_live : forall v st c, get_cls (set_live v st) c = get_cls st c.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepFrame ()) ["CANSEC1"] "h01ch12sth21vp;4p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p710R1p1000kp4p710R0p8P1p1001Gp4p710R1p8p1001ep4p710R2p1002CR3p4p710R4p8P2P3p4p7210R3p8p1002\p4p70R5p1003Sp4p710p8P5P1p8P5p1003jp4p710p8g004FR5p4p710R6P2p8P6P4p8P6P3p8P6p1004Zp4p73110p8P5p4p741110R6p100Pnp4p73101p8p1005Np4p710P0p8p1004lp4p7<111111111110P1p8p1005ip4p7<111111111110P1p8p1006Kp4p741110R1p100QJR0p4p7511100R3p8P3P1p8p1006dp4p741110R1P0p4p76111100R3p8P3P1p8p1007<p4p741110R1P0p4p771111100R3p8P3P1p8p1007\p4p741110R1P0p4p7:1111111100R0p8P0P1p8p100Qdp4p7200R1P6p8P6P1p8P5j42Tg00Icj21Tg009mj20Tg00R6g00RTg00Rmg00SKC2g00MKg00Lmg00K8f1f0'1'0W0W1W2o"). Qed.
Lemma max_count_eq : forall st st' c, a_cinit st' = a_cinit st -> max_count st' c = max_count st c.
Proof. intros st st' c E. unfold max_count. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Definition st_fast (st : astate) (c n cnt : Z) : astate :=
  set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
    (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)).

Lemma st_fast_fields : forall st c n cnt,
     a_space_beg (st_fast st c n cnt) = a_space_beg st /\ a_ptr_array (st_fast st c n cnt) = a_ptr_array st
  /\ a_nres (st_fast st c n cnt) = a_nres st /\ a_nsec (st_fast st c n cnt) = a_nsec st
  /\ a_cinit (st_fast st c n cnt) = a_cinit st
  /\ a_live (st_fast st c n cnt) = <[ a_next st := CPrim c n ]> (a_live st)
  /\ a_next (st_fast st c n cnt) = N.succ (a_next st)
  /\ a_qloc (st_fast st c n cnt) = a_qloc st /\ a_qloc_bytes (st_fast st c n cnt) = a_qloc_bytes st
  /\ a_qglob (st_fast st c n cnt) = a_qglob st /\ a_qglob_bytes (st_fast st c n cnt) = a_qglob_bytes st.
Proof. intros. repeat split; reflexivity. Qed.

Lemma st_fast_cls : forall st c n cnt c',
  get_cls (st_fast st c n cnt) c' = if c' =? c then cls_set_count (cnt - 1) (get_cls st c) else get_cls st c'.
Proof.
  intros. unfold st_fast. rewrite get_cls_set_next, get_cls_set_live.
  destruct (Z.eqb_spec c' c) as [->|NE]; [apply get_cls_put_cls_eq | apply get_cls_put_cls_ne; exact NE].
Qed.

Lemma st_fast_counters : forall st c n cnt c',
     c_mapped_user (get_cls (st_fast st c n cnt) c') = c_mapped_user (get_cls st c')
  /\ c_allocated_user (get_cls (st_fast st c n cnt) c') = c_allocated_user (get_cls st c')
  /\ c_num_freed (get_cls (st_fast st c n cnt) c') = c_num_freed (get_cls st c')
  /\ c_mapped_free_array (get_cls (st_fast st c n cnt) c') = c_mapped_free_array (get_cls st c')
  /\ c_count (get_cls (st_fast st c n cnt) c') = (if c' =? c then cnt - 1 else c_count (get_cls st c')).
Proof. intros. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; repeat split; reflexivity. Qed.

Lemma st_fast_max_count : forall st c n cnt c', max_count (st_fast st c n cnt) c' = max_count st c'.
Proof. intros. apply max_count_eq. reflexivity. Qed.
Lemma st_fast_ndist : forall st c n cnt c', ndist (st_fast st c n cnt) c' = ndist st c'.
Proof. intros. unfold ndist. rewrite (proj1 (proj2 (st_fast_counters st c n cnt c'))). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma size_of_class_facts : forall c, 1 <= c < K_NUM_CLASSES ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  enough (B : (16 <=? size_of_class c) && (size_of_class c <=? 65536) && (size_of_class c mod 16 =? 0) = true).
  { apply andb_prop in B. destruct B as [B B3]. apply andb_prop in B. destruct B as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.eqb_eq in B3. lia. }
  assert (E : exists i, (0 <= i < 31)%nat /\ c = Z.of_nat i + 1).
  { exists (Z.to_nat (c - 1)). split; lia. }
  destruct E as (i & Hi & ->).
  do 31 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma shlen_div : forall d, shlen d = d / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_div : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma shad_add : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + d / 8.
Proof. intros a d H. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.
Lemma shad_add_shlen : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + shlen d.
Proof. intros. rewrite shlen_div. apply shad_add. assumption. Qed.
(* [comment removed for export] *)
Lemma shad_sep : forall a1 n1 a2, a1 + n1 <= a2 -> a1 mod 8 = 0 -> shad a1 + shlen n1 <= shad a2.
Proof. intros a1 n1 a2 H M. rewrite !shad_div, shlen_div. Z.div_mod_to_equations. lia. Qed.
Lemma shlen_mono : forall a b, a <= b -> shlen a <= shlen b.
Proof. intros. rewrite !shlen_div. apply Z.div_le_mono; lia. Qed.
Lemma shlen_nonneg : forall a, 0 <= a -> 0 <= shlen a.
Proof. intros. rewrite shlen_div. apply Z.div_pos; lia. Qed.
Lemma shlen_mul8 : forall q, shlen (8 * q) = q.
Proof. intros. rewrite shlen_div. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
Lemma granules_eq : forall n, 0 <= n -> granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1).
Proof. intros n H. unfold granules. rewrite !shlen_div. destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. Qed.
Lemma shlen_floor : forall n, shlen (n - n mod 8) = shlen n.
Proof. intros n. rewrite !shlen_div. Z.div_mod_to_equations. lia. Qed.

Lemma aregion_mod : forall L c, al_space_beg L mod K_ALIGN = 0 -> aregion L c mod 65536 = 0.
Proof. intros L c H. unfold aregion, K_REGION, K_ALIGN in *. change (2^32) with (65536 * 65536). Z.div_mod_to_equations. lia. Qed.

Lemma regions_sep : forall L c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2.
Proof. intros L c1 c2 H. unfold aregion, K_REGION. nia. Qed.

Lemma slots_sep : forall L c k1 k2, 0 <= k1 -> k1 < k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2.
Proof. intros L c k1 k2 H1 H2 HS. unfold aslot_addr. nia. Qed.

Lemma slots_disjoint : forall L c k1 k2, 0 <= k1 -> 0 <= k2 -> k1 <> k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2 \/ aslot_addr L c k2 + size_of_class c <= aslot_addr L c k1.
Proof.
  intros L c k1 k2 H1 H2 NE HS. destruct (Z.lt_ge_cases k1 k2).
  - left. apply slots_sep; lia.
  - right. apply slots_sep; lia.
Qed.

(* [comment removed for export] *)
Lemma slot_in_region : forall L st c k, let r := get_cls st c in let S := size_of_class c in
  0 < S -> 0 <= c_allocated_user r -> 0 <= k < ndist st c ->
  aregion L c <= aslot_addr L c k /\ aslot_addr L c k + S <= aregion L c + c_allocated_user r /\ 0 <= k * S.
Proof.
  intros L st c k r S HS HA HK. unfold ndist in HK. subst r S. unfold aslot_addr.
  set (A := c_allocated_user (get_cls st c)) in *. set (S := size_of_class c) in *.
  assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M1 : (k + 1) * S <= A / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  pose proof (Z.mul_div_le A S ltac:(lia)) as M2. rewrite Z.mul_comm in M2.
  split; [lia|]. split; [| exact P0]. rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. lia.
Qed.

Lemma slot_aligned : forall L c k, al_space_beg L mod K_ALIGN = 0 -> 1 <= c < K_NUM_CLASSES ->
  aslot_addr L c k mod 16 = 0.
Proof.
  intros L c k H Hc. pose proof (size_of_class_facts c Hc) as [_ M]. pose proof (aregion_mod L c H) as R.
  unfold aslot_addr. set (S := size_of_class c) in *. set (R0 := aregion L c) in *.
  replace (k * S) with ((k * (S / 16)) * 16) by (Z.div_mod_to_equations; nia).
  rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xcons (b : xbusy) (upd : Z -> xclass -> xclass) (X : aconc) : aconc :=
  mkAConc (fun c => if c =? xb_class b then upd c (x_cls X c) else x_cls X c) (b :: x_busy X).

Lemma busy_of_cons : forall b bs X c k,
  busy_of (mkAConc X (b :: bs)) c k =
    if (xb_class b =? c) && (xb_slot b =? k) then Some b else busy_of (mkAConc X bs) c k.
Proof. intros. unfold busy_of. cbn. destruct ((xb_class b =? c) && (xb_slot b =? k)); reflexivity. Qed.

Lemma busy_slots_cons : forall b bs X c,
  busy_slots (mkAConc X (b :: bs)) c = (if xb_class b =? c then [xb_slot b] else []) ++ busy_slots (mkAConc X bs) c.
Proof. intros. unfold busy_slots. cbn. destruct (xb_class b =? c); reflexivity. Qed.

Lemma busy_of_x_cls : forall X X' bs c k, busy_of (mkAConc X bs) c k = busy_of (mkAConc X' bs) c k.
Proof. reflexivity. Qed.
Lemma busy_slots_x_cls : forall X X' bs c, busy_slots (mkAConc X bs) c = busy_slots (mkAConc X' bs) c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cache_split_last : forall (l : list Z) k,
  nth_error l (length l - 1) = Some k -> l = removelast l ++ [k].
Proof.
  intros l k H. destruct l as [|a l'] eqn:E; [cbn in H; discriminate|]. rewrite <- E in *.
  assert (NE : l <> []) by (subst; discriminate).
  rewrite (app_removelast_last k NE) at 1. f_equal. f_equal.
  rewrite (app_removelast_last k NE) in H.
  rewrite length_app in H. cbn [length] in H. rewrite nth_error_app2 in H by lia.
  replace (length (removelast l) + 1 - 1 - length (removelast l))%nat with 0%nat in H by lia. cbn in H. congruence.
Qed.

Lemma length_removelast : forall {A} (l : list A), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros A l NE. induction l as [|a l IH]; [congruence|]. destruct l as [|b l'].
  - reflexivity.
  - cbn [removelast length]. cbn [removelast length] in IH. rewrite IH by discriminate. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

Lemma junk_frame : forall W m m' A n, junk_at m A n -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU WM D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma fill_frame : forall W m m' A n v, fill_at m A n v -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU WM D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma cells_frame : forall W m m' A cs, rw_cells bsegs m A cs -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
Proof. intros. eapply rw_cells_transport; eauto. Qed.

Lemma u64arr_frame : forall W m m' A ws, u64arr bsegs m A ws -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
Proof. intros. eapply u64arr_transport; eauto. Qed.
Lemma u32arr_frame : forall W m m' A ws, u32arr bsegs m A ws -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr bsegs m' A ws.
Proof. intros. eapply u32arr_transport; eauto. Qed.

(* [comment removed for export] *)
Lemma fill_cons : forall m A n v, 0 <= v < 256 -> 0 <= n ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 v)] -> fill_at m (A + 1) n v -> fill_at m A (1 + n) v.
Proof.
  intros m A n v Hv Hn H1 H2. apply (fill_merge m A 1 n v); [| exact H2 | lia | lia].
  unfold fill_at. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op].
  eapply rw_cells_recast; [exact H1 | cbn; tauto | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma cb_app : forall m A n1 bs1 n2 bs2,
  rw_cells bsegs m A [CB n1 bs1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells bsegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells bsegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge bsegs m A [] ([CB n1 bs1] ++ [CB n2 bs2]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exact M.
Qed.

Lemma cb_of_C1 : forall m A (b : byte), rw_cells bsegs m A [C1 b] -> rw_cells bsegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity]. Qed.

Lemma cb_of_fill : forall m A n v, fill_at m A n v ->
  rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof. intros m A n v H. exact H. Qed.

Lemma cb_nil : forall m A n bs, rw_cells bsegs m A [CB n bs] -> rw_cells bsegs m (A + Z.of_nat n) [CB 0 []].
Proof.
  intros m A n bs H. pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 _]]] [W0 [W1 _]]]. cbn in L, B1, W1.
  rewrite app_nil_r in B1. rewrite L in B1. rewrite Nat.add_0_r in W1.
  split; [split; [cbn; tauto|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac dforall H :=
  lazymatch type of H with
  | Forall _ (_ :: _) => let A := fresh "D" in pose proof (Forall_inv H) as A; cbn [fst snd] in A;
                         apply Forall_inv_tail in H; dforall H
  | _ => clear H
  end.

Section CANSEC2. Context {rc : runConstT}.
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Ltac xcell := eapply cells_frame; [eassumption | exact MU | exact WM | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)
Definition rt_hulls : list (Z * Z) :=
  [(0xb2108, 8); (0xb2118, 48); (0xb2148, 8); (0xb2c90, 8); (0xb2d80, 8); (0xb3fa0, 16);
   (0xb7ab8, 13); (0xb7af8, 20); (0xb7b24, 12); (0xb7b4d, 1); (0xba2f8, 8); (0xb9b5c, 1);
   (0xb9b60, 1); (0xb9b64, 4); (0xbafd8, 2); (0xbafe0, 24); (0xbaffc, 4); (0x13c560, 3);
   (0x149da0, 8); (0x14bdc0, 16); (0x14be48, 8); (0x14be4a, 1); (0x14bea0, 8); (ATP88, 8); (ATSD, 8);
   (0x5ed2a0, 4); (al_ctx L + 8, 4); (al_ctx L + 152, 8)]%Z.

Lemma arep_rt_frame : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt_hulls -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma arelro_frame : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
Lemma azero_frame : forall A n, azero m A n -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros A n [Z0 WR] MU' WM' D. split.
  - intros i Hi. rewrite <- (Z0 i Hi). pose proof WR as (W0 & W1 & _).
    pose proof (MU' (wa (A + i))) as E. rewrite wa_unsigned in E by lia. apply E.
    eapply disjoint_outside; [apply D; lia | lia].
  - eapply wr_at_transport; [exact WR | exact WM'].
Qed.

Lemma ashadow_avail_frame : forall st st' c,
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
  split; [eapply azero_frame; [exact Z1 | exact MU | exact WM | exact D1] | eapply azero_frame; [exact Z2 | exact MU | exact WM | exact D2]].
Qed.

Lemma arep_rt2_frame : arep_rt2 m -> disjoint_from W 0x14bf2c 1 -> disjoint_from W 0x14beb8 8 -> disjoint_from W 0xb3f50 8 -> arep_rt2 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepFrame ()) ["CANSEC2"; "Frames"] "h01Hh12D1h22D2h32D3h42R1h52R2h62R3p;1p;2p;3p;9p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p710R1p1000kp4p710R0p8P1p1001Gp4p710R1p8p1001ep4p710R2p1002CR3p4p710R4p8P2P3p4p7210R3p8p1002\p4p70R5p1003Sp4p710p8P5P1p8P5p1003jp4p710p8p1004FR5p4p710R6P2p8P6P4p8P6P3p8P6p1004Zp4p73110p8P5p4p741110R5p100Pnp4p73101p8p102RUp6051000R6P0p8P6p102R3p4p710p8P6p102N5p4p710p8P6p1005Np4p710R6p8P6P0p8p1004lp4p7<111111111110P1p8p1005ip4p7<111111111110P1p8p1006Kp4p741110R1p100QJR0p4p7511100R6p8P6P1p8p1006dp4p741110R1P0p4p76111100R6p8P6P1p8p1007<p4p741110R1P0p4p771111100R6p8P6P1p8p1007\p4p741110R1P0p4p7:1111111100R0p8P0P1p8p100Qdp4p7200R1P5p8P5P1p8g03L9j1BTg00[cj15Tg01>Aj13Tg020Aj1>Tg02i>j2:Tg02mcj1DTg01:[j1CTg01K;j39Tg03:>j1ATg00Z2R1j2@Tg02S[j34Tg02bVj1<Tg012=j1;Tg03;hl9=Tg00ZMj4?Tg014Oj18Tg02a`j4ETf0R5#3#8p=7%35#3p=1%85#3p=2%85#8p=0g02f]f2R0f1R6P5CEp=6p,1mR3#BP1g00eNR4#7#1#2#0#0#0#1#2#0#1#5R2g02gRR7%34#1R8#>g00V_R9':#D%C7R:39R;563R<%74#1#2#0#0#2#2#0#2#1#5R=%38#1#>R>/:9#A=97:R9563R?%34#0#1#0#0#0#7#7#1#1#5R@%34#2#2#0#0#1#0#2#7#1#5,:>#A=97:R:563R7'@R>p,1WRA%54742R4%58R894A=RBA4A@8R8p,2m'RC#B[[[RDP5P1P?P7PDP5A6C2;A6C=9RDA6C@:R1'@PAP3PCP2P;f8p,2MUREp,2WMRFP0%<;#;94A2eM9=PDP1PAP3PCP=P9f4PEPFP6%<9#;94A=eM9=PAP3PCP@P:f3PEPFP5%<:#;94A@eM9=C?C?X38X2BX14X67X5?P6P5O2n2001000000121000000X0>X4<P6P5O2n2001000000121000000W0o"). Qed.

(* [comment removed for export] *)
Definition rt3_hulls : list (Z * Z) :=
  [(0xb3e98, 16); (0xb3e78, 8); (0xb3e80, 8); (0xb3f50, 8); (0xb3e68, 8); (0x14be78, 8); (0x14bf20, 8);
   (0xba300, 4); (0xb7b58, 1); (0x149d98, 4);
   (0xb2108, 16); (0xb3fe0, 8); (0x149da0, 8); (0x14bf00, 8); (0x14bf18, 8); (0x60d550, 8)]%Z.   (* [comment removed for export] *)
Lemma arep_rt3_frame : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
ltac2:(rds2_run [(constr:(6203920%Z), constr:(6345424%Z))] (kr_t_ARepFrame ()) ["CANSEC2"; "Frames"] "h03CLRh11Hh22cbh31Dh42D0h52D1h63D10h73D11h83D12h93D13h:3D14h;2D2h<2D3h=2D4h>2D5h?2D6h@2D7hA2D8hB2D9hC2R1hD3R10hE3R11hF3R12hG3R13hH3R14hI3R15hJ3R16hK3R17hL2R2hM2R3hN2R4hO2R5hP2R6hQ2R7hR2R8hS2R9hT2RThU1pp%0p;1p;2p;3p;5p;9p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p710R1p1000kp4p710R0p8P1p1001Gp4p710R1p8p1001ep4p710R2p1002CR3p4p710R4p8P2P3p4p7210R3p8p1002\p4p70R5p1003Sp4p710p8P5P1p8P5p1003jp4p710p8p1004FR5p4p710R6P2p8P6P4p8P6P3p8P6p1004Zp4p73110p8P5p4p741110R5p100Pnp4p73101p8p102RUp6051000R6P0p8P6p102R3p4p710p8P6p102N5p4p710p8P6p1005Np4p710R6p8P6P0p8p1004lp4p7<111111111110P1p8p1005ip4p7<111111111110P1p8p1006Kp4p741110R1p100QJR0p4p7511100R6p8P6P1p8p1006dp4p741110R1P0p4p76111100R6p8P6P1p8p1007<p4p741110R1P0p4p771111100R6p8P6P1p8p1007\p4p741110R1P0p4p7:1111111100R0p8P0P1p8p100Qdp4p7200R1P5p8P5P1p8g03M1j1]Tg02Uij2kTg035?j3bTg035\j3aTg02S[j3STg0369j37Tg01>Aj10Tg00[cj1ITg014Oj11Tg01:[j1XTg01K;j34Tg037Qj5;Tg0380j58Tg020Aj1WTg02i>j2GTg039Ij1VTg02mcj1jTg02VIj1iTg00YRj1hTg011^j1ETg02YKj2gTg01EXj2\Tg00Z2R1j23Tg03;hl99Tg03Mij1eTg02TWj4dTg03:>j1[Tg02a`j4cTg02bVj1^Tg012=j1ZTg00ZMj4YTf0R5#0#1#1#0p=?%05#1#1#1p==%15#1#0#1p=H%05#0#1#1p=K%05#0#0#Ip=5%05#0p=Ug00LmR0P0f1R6P5Cdp=:%15#1#0#0p=C%15#1#1#1p=R%05#0#0#0p=6%15#1#1#0p=M%15#0#1#0p=A%15#0#0#1p=B%05#1#0#0p=L%15#0#1#1p=Q%05#1p=P%15#0p=O%05#0#0#1p=@%05#1#0p=N%15#0#0#0p=Jg02gRR3f2R4%I6'G#[;45p=>g02f]P4P6P5Ccp=2%15#1p=`%05#0#0#0#0#0#0#0p=FA4365p=T%[6=435p=_%^5#Z9S46p=<%^5#Zp=ff6f5S00f4f3P4P6P5CYCYp=Dp,1mR4#]1k00R2p,1WR7Ab005Aa0053SXU2R0g03Nm37P2P0g00eNR8#?#=#H#K#5R9%U8R:#0R;#0R<#IR=':R>%?8#=#C#R#5R?%I;R@':RA%?8#=#H#6#5RB/:@RC%?8#=#M#A#5RD/:@RE%?8#=#C#H#5RF/:@RG%08#B#=#C#R#5RH/:@RI%08#B#=#M#L#5RJ/:@RK%=8#L#?#6#5RL%I:R:':RM%?8#R#?#Q#5RN%I8RO':RP%08#B#K#Q#K#5RQ/::R:%P8#B#6#O#@#5RR/:=R=%?8#=#R#C#5RS/:@RT%08#B#K#Q#L#5RU/:@RV%08#B#=#M#6#5RW/:@RX%08#B#=#M#K#5RY/:@RZ%18#U#@#A#A#A#5R[/:@R@%X2R\542R]542R^542R_542R`542Ra542Rb542Rc542Rd542Re542Rf542Rg542Rh542Ri542Rj542RkP5D;P0P>O1P2P0P>PkP6D8A720kP2P0PAPjP5D;P0PAO1P2P0PAPjP6D8A720jP2P0PCPiP5D;P0PCO1P2P0PCPiP6D8A720iP2P0PEPhP5D;P0PEO1P2P0PEPhP6D8A720hP2P0PGPgP5D;P0PGO1P2P0PGPgP6D8A720gP2P0PIPfP5D;P0PIO1P2P0PIPfP6D8A720fP2P0PKPeP5D;P0PKO1P2P0PKPeP6D8A720eP2P0PMPdP5D;P0PMO1P2P0PMPdP6D8A720dP2P0PPPcP5D;P0PPO1P2P0PPPcP6D8A720cP2P0P:PbP5D;P0P:O1P2P0P:PbP6D8A720bP2P0P=PaP5D;P0P=O1P2P0P=PaP6D8A720aP2P0PTP`P5D;P0PTO1P2P0PTP`P6D8A720`P2P0PVP_P5D;P0PVO1P2P0PVP_P6D8A720_P2P0PXP^P5D;P0PXO1P2P0PXP^P6D8A720^P2P0PZP]P5D;P0PZO1P2P0PZP]P6D8A720]P2P0P@P\P5D;P0P@O1P2P0P@P\P6D8A720\P1%U<R<#WR\%N8#A#H#A#J%N8#=#C#B#J%X3R35>\3>R09249R2%08#`#6#O#H#P#C=>\3R@924?R]%N8#=#A#@#6=>\3RZ924BR^%N8#Q#C#M#L=>\3RX924DR_%08#A#C#H#P#C=>\3RV924FR`%0<R<#0#6RT#6#F#F=>\3Ra924HR=%J<#6R<#J#6Rb#1#6#@#6#@#6#@#6#@=>\3R:924JRc1G\O#V/T3RP924LRd%W;R;/GO#j/T3RO924NRMg00V_,G\#V/T3Re924QRK1G\U1G\S/_3'_Rf924RRI%O8#L#J#O#==>\3Rg924SRGA>\T3RT924URh%0b#6#@#F=>\3Rb924WRE%0<#6#@#F#F#F#F=>\3R\924YR<%i;#hR;%18#6#?#B#P#A#5R8g01PC#E#E#E#E#E#E#E#E/g5/T3R3524X2;'\RiA24[TRC'3Rj'3RA'3Rk'3R>'3Rl'3Rm'3Rn'3Ro'3Rp'3Rq'3Rr'3Rs'3Rt'3Ru'3Rvp,2m'Rw#]RxfQS01P1P]PuPxP5P1P^PtPxP5P1P_PsPxP5P1P`PrPxP5P1P=PqPxP5P1PcPpPxP5P1PdPoPxP5P1PMPnPxP5P1PKPmPxP5P1PIPlPxP5P1PGP>PxP5P1PhPkPxP5P1PEPAPxP5P1P<PjPxP5P1PiPCPxP5A2w90A2w?@R1A2wBZS02A2wDXS03A2wFVS04A2wHaS05A2wJ:S06A2wLPS07A2wNOS08A2wQeS09A2wRfS0:A2wSgS0;A2wUTS0<A2wWbS0=A2wY\S0>A2w83X2;,\;S0?A2w[TS0@'3S0A'3S0B'3S0C'3S0D'3S0E'3S0F'3S0G'3R;'3R3'3R8'3Ry'3Rz'3R{'3R|'3P7P4PwP9P0fmp,2MUR}p,2WMR~p+01PA<790eM99P1P|P7P4PwP?P@fiP}P~p+01NA<7?@eM99Q02P{P7P4PwPBPZfeP}P~p+01LA<7BZeM99Q03PzP7P4PwPDPXfaP}P~p+01JA<7DXeM99Q04PyP7P4PwPFPVf]P}P~p+01HA<7FVeM99Q05P8P7P4PwPHPafYP}P~p+01FA<7HaeM99Q06P3P7P4PwPJP:fUP}P~p+01DA<7J:eM99Q07P;P7P4PwPLPPQ01P}P~p+01BA<7LPeM99Q08Q0GP7P4PwPNPOfMP}P~p+01@A<7NOeM99Q09Q0FP7P4PwPQPefIP}P~f}A<7QeeM99Q0:Q0EP7P4PwPRPffEP}P~f{A<7RfeM99Q0;Q0DP7P4PwPSPgfAP}P~fyA<7SgeM99Q0<Q0CP7P4PwPUPTf=P}P~fw%fTRg9S7UeM99Q0=Q0BP7P4PwPWPbf9P}P~fuA<7WbeM99Q0>Q0AP7P4PwPYP\Q00P}P~fsA<7Y\eM99Q0?Q0@%ewP7P4PwP[PTP5P}P~fqAS7[geM99FDFDFDFDFDFDFDFDPxeXKCXJiP6P5O2n2001000000121000000X1jXI<P6P5O2n2001000000121000000X1AXHEP6P5O2n2011000000121000000X1kXGhP6P5O2n2011000000121000000X1>XFGP6P5O2n2011000000121000000X1lXEIP6P5O2n2011000000121000000X1mXDKP6P5O2n2011000000121000000X1nXSMP6P5O2n2011000000121000000X1oXRdP6P5O2n2011000000121000000X1pXQcP6P5O2n2011000000121000000X1qXP=P6P5O2n2011000000121000000X1rXO`P6P5O2n2011000000121000000X1sXN_P6P5O2n2011000000121000000X1tXM^P6P5O2n2011000000121000000X1uXL]P6P5O2n2011000000121000000X1vXC2P6P5O2n2011000000121000000b0b:b0b9b0b8b0b7b0b6b0bBb0bAb0b@b0b?b0b>b0b=b0b<b0b;b0b5b0b4b0b3W0WTo"). Qed.

(* [comment removed for export] *)
Lemma ainstance_frame : forall st st',
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
Lemma aregion_cells_frame : forall st st' c,
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
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frame; [exact A5 | exact MU | exact WM | intros _; exact De].
Qed.

(* [comment removed for export] *)
Lemma afreearray_frame : forall st st' X X' c,
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
  - eapply u32arr_frame; [exact A1 | exact MU | exact WM |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A2 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact DS].
Qed.

(* [comment removed for export] *)
Lemma acache_cells_frame : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frame; [exact A1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frame; [exact A2 | exact MU | exact WM |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)
Definition xb_fits (b : xbusy) : Prop :=
  match xb_st b with
  | BBatch => True
  | _ => 0 <= xb_n b /\ 16 <= rz_size (xb_n b) /\ rz_size (xb_n b) + xb_n b <= size_of_class (xb_class b)
  end.

Lemma aslot_busy_frame : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact SB | exact MU | exact WM | intros _; exact D].
Qed.

(* [comment removed for export] *)
Lemma aslots_update : forall st st' X X' c k0,
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
      eapply aslot_busy_frame; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

(* [comment removed for export] *)
Lemma aslot_shadow_update : forall st st' X X' c k0,
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
    eapply cells_frame; [exact SL | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
Lemma azero_cb : forall m A n k, azero m A n -> 0 <= k <= n ->
  rw_cells bsegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. rewrite repeat_length. split; [lia|].
    intros i Hi. unfold mrd. rewrite Z0 by lia. symmetry. apply nth_error_repeat. exact Hi.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros i Hi. apply WR. lia.
Qed.
Lemma azero_split : forall m A n k, azero m A n -> 0 <= k <= n -> azero m (A + k) (n - k).
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split.
  - intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply Z0. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply WR. lia.
Qed.

(* [comment removed for export] *)
Lemma busy_of_Some_facts : forall X c k b, busy_of X c k = Some b -> In b (x_busy X) /\ xb_class b = c /\ xb_slot b = k.
Proof.
  intros X c k b Hb. unfold busy_of in Hb. apply find_some in Hb. destruct Hb as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Lemma rz_size_ge16 : forall n, 16 <= rz_size n.
Proof.
  intros n. rewrite rz_size_eq. assert (0 <= rz_log n) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
  assert (1 <= 2 ^ rz_log n) by (apply Z.pow_le_mono_r with (a := 2) in H; [| lia]; rewrite Z.pow_0_r in H; lia). lia.
Qed.

Lemma rounded_size_ge : forall n, n <= rounded_size n.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma awf_fits : forall L st X b, awf L st X -> In b (x_busy X) -> xb_fits b.
Proof.
  intros L st X b WF Hb. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. unfold xb_fits.
  pose proof (rz_size_ge16 (xb_n b)) as R. pose proof (rounded_size_ge (xb_n b)) as RS.
  destruct (xb_st b); [| | exact I]; destruct M as (N & FIT & _); (split; [clear -N; lia|]); split; clear -R RS FIT; lia.
Qed.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma mod16_of_class : forall a s, a mod s = 0 -> s mod 16 = 0 -> 0 < s -> a mod 8 = 0.
Proof.
  intros a s H1 H2 Hs. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; [| exact H1]. eapply Z.divide_trans; [| exact H2]. exists 2. reflexivity.
Qed.

End CANSEC2.
(* [comment removed for export] *)
