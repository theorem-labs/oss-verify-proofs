(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfGc CxfL1 CxfL2 CxfL3 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFGL.
Import CXFG.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import APC.
Import APCL.
Section G.
Variable nx0 : nat.
Fixpoint expr_vars_tF (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => if CXNAT.ltbF n nx0 then acc else pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_tF x (expr_vars_tF y acc)
  | EExt _ _ _ x => expr_vars_tF x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_tF (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_tF PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_tF (a_base a) (expr_vars_tF v acc)
                                      | KZero a n => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KBlob a n _ => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KWr a n => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KFill a n _ => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KUnk a n => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_tF (am_base m) (expr_vars_tF (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_tF (fst p) (expr_vars_tF (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_tF (fst p) (expr_vars_tF (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_tF l (expr_vars_tF o acc) | _ => acc end in
  expr_vars_tF (a_brk cs) acc.
Definition cs_gcF (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_tF cs in
  set_kn cs (List.filter (kn_gc_entry_t nx0 spb spk live) (kn cs)).
Definition hi_agree (t' t : ptree unit) : Prop := forall v, (nx0 <= v)%nat -> in_live_t t' v = in_live_t t v.
End G.
Lemma L_CXFGL_expr_vars_tF : @expr_vars_tF = @CXFG.expr_vars_tF.
Proof. unfold expr_vars_tF. rewrite ?AX2L.L_AX2L_pt_set, ?APCL.L_APCL_vkey, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CXFGL_live_vars_tF : @live_vars_tF = @CXFG.live_vars_tF.
Proof. unfold live_vars_tF. rewrite ?L_CXFGL_expr_vars_tF, ?APCL.L_APCL_kn. reflexivity. Qed.

Lemma L_CXFGL_cs_gcF : @cs_gcF = @CXFG.cs_gcF.
Proof. unfold cs_gcF. rewrite ?L_CXFGL_live_vars_tF, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_gc_entry_t, ?APCL.L_APCL_reg, ?APCL.L_APCL_set_kn, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_CXFGL_hi_agree : @hi_agree = @CXFG.hi_agree.
Proof. unfold hi_agree. rewrite ?APCL.L_APCL_in_live_t. reflexivity. Qed.

End CXFGL.
