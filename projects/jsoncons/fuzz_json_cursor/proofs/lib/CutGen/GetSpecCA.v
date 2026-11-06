(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA PmCurSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GSP.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Definition get_string_on (P : PMCUR.sevent -> Prop) (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o V E sp r : Z) (e : PMCUR.sevent) (g : PML.ls_state),
    P e ->
    PMSA.cps_asan L ar HI pc r sp PMCSA.GETSTR_SCR LB FF LK cr A PMCSA.GET_D
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R (V + 8) /\ PMSA.a3 R E /\
                  PMCUR.ev_at (hl_segs L) M V e /\ PMCSA.ev_srcA M LB e /\ L5.defined M V 48 /\ PMLA.ec_at (hl_segs L) IC M E 0 /\ PMLA.img_ro IC M /\
                  PMLA.ls_ok (hl_segs L) IC g M /\ g <> PML.LS0 /\
                  PMSA.fobj M FF o 24 /\ L5.defined M o 24 /\ PMSA.fobj M FF E 16 /\ PMLA.apart o 24 E 16 /\ PMLA.apart o 24 V 48 /\ PMLA.apart V 48 E 16 /\
                  acredit_ok L cr (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)) /\
                  PMSA.fobj M FF V 48 /\ PMSA.stksh ar M sp PMCSA.GETSTR_SCR /\ sp mod 32 = 0)
      (fun R M R' M' LB' cr' LBk W => exists (code : Z) (g' : PML.ls_state),
          PMCSA.s2_postA L ar (Z.max 48 (match e with PMCUR.EvStr _ n | PMCUR.EvKey _ n => PML.str_cap n | _ => 0 end)) LB FF cr M' o LB' cr' /\ LBk = LB /\
          PMLA.u32 (hl_segs L) M' E code /\ L5.defined M' E 16 /\ PMLA.ls_ok (hl_segs L) IC g' M' /\
          ((PMCSA.conv_ok e /\ code = 0 /\ g' = g /\ PMLA.ec_at (hl_segs L) IC M' E 0) \/
           (~ PMCSA.conv_ok e /\ code = 11 /\ g' = PML.regC g /\ PMCSA.ec_conv_atA L IC M' E 11)) /\
          W = [(o, 24); (E, 16); (PMLA.CONVCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)]).
Definition is_cont (e : PMCUR.sevent) : Prop := match e with PMCUR.EvBeginObj | PMCUR.EvEndObj | PMCUR.EvBeginArr | PMCUR.EvEndArr => True | _ => False end.
Definition is_lit (e : PMCUR.sevent) : Prop := match e with PMCUR.EvNull | PMCUR.EvBool _ => True | _ => False end.
Definition is_int (e : PMCUR.sevent) : Prop := match e with PMCUR.EvI64 _ | PMCUR.EvU64 _ => True | _ => False end.
Definition is_txt (e : PMCUR.sevent) : Prop := match e with PMCUR.EvStr _ _ | PMCUR.EvKey _ _ => True | _ => False end.
Definition is_dbl (e : PMCUR.sevent) : Prop := match e with PMCUR.EvDbl _ => True | _ => False end.
Lemma get_string_of : forall pc, get_string_on is_cont pc -> get_string_on is_lit pc -> get_string_on is_int pc -> get_string_on is_txt pc -> get_string_on is_dbl pc ->
  PMCSA.get_string_specA L ar HI IC pc.
Proof.
  intros pc HC HL HN HT HD LB FF LK cr A o V E sp r e g.
  destruct e; [apply HL | apply HL | apply HN | apply HN | apply HD | apply HT | apply HT | apply HC | apply HC | apply HC | apply HC]; exact I.
Qed.
End S.
End GSP.
