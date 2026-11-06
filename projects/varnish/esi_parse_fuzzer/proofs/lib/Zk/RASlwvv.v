(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.

Module ASlot_W5.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux MRepAux MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallmv3 Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
  intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
  rewrite upd_meta_put. reflexivity.
Qed.

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
  intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
  rewrite !upd_meta_put.
  match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
  rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
  f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
  rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

End CEIL.

Section DEQ.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

Definition deq_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End DEQ.
End ASlot_W5.

Module ASlot_W6.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux MRepAux MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallmv3 Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section M.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

Definition m_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Definition full_skip : bool := (f =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End M.
End ASlot_W6.

Module ASlot_W7.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux MRepAux MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallmv3 Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

(* [comment removed for export] *)
End SPANLOOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACT.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

Definition act_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac act_prefix MR MSL Hmem Hgh CH W8 :=
  mchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
  step; step;
  let bs := fresh "bs" in let RD8 := fresh "RD8" in let L8 := fresh "L8" in let MOD8 := fresh "MOD8" in
  destruct (mrep_group_word8 st _ b gh MR Hgh) as (bs & RD8 & L8 & MOD8); unfold wa in RD8;
  step;
  set (W8 := bv_extract 0 64 (le_bytes_to_word bs)) in *;
  let W8R := fresh "W8R" in
  pose proof (bv_unsigned_in_range _ W8) as W8R; change (bv_modulus 64) with (2^64) in W8R;
  step; rewrite (sllw2_word (bv_unsigned W8)) by lia; rewrite MOD8; fold ai0;
  step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
  step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land;
  step.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACT.
End ASlot_W7.

Module ASlot_W8.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux MRepAux MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallmv3 Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section ENTRY.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (m : mem) (sc lo : Z).
Hypothesis MR : mrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

(* [comment removed for export] *)
End ENTRY.
End ASlot_W8.

Module RASlz6s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_ntf_C.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_C.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RF_egfy RF_m8yt SlotMisc RF_ntf_A RF_ntf_C RAlllfc RASlot_I Malluin.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.SlotMisc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition ta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 junk; C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
  mrep st' m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono rsegs m0 m ->
  evt rsegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom rsegs)
      /\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ mrep st' m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 SSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24524) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (first [ pose proof (MR') as dR_1; dand4 dR_1 as _ _ (_ & _ & _ & _ & GUARD) _ | pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _) ]).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold SSP_GUARD, ta_frame in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : mrep st' mX)
      by (eapply mrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FIN.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="CLO MASK MSL MR"] Lemma fin_walk :
  forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
  bv_unsigned gw = G ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' a3' : word) m' k,
      0 <= k < 32 /\ lowbit mask = 2 ^ k /\
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ mrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 SSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23e64) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (first [ pose proof ((meta_chunk_facts st m g MR MSL)) as dR_2; dand6 dR_2 as CH Gpos GC GI1 GI2 _ | pose proof (meta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _) ]). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  (first [ pose proof ((lowbit_facts mask ltac:(lia))) as dR_3; dex1 dR_3 as k; destruct dR_3 as [Hk LB] | pose proof ((lowbit_facts mask ltac:(lia))) as dR_3; dand3 dR_3 as k Hk LB | destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB) ]).
  assert (P2 : 0 < 2 ^ k <= mask).
  { (first [ pose proof ((lowbit_nonzero mask ltac:(lia))) as dR_4; dex1 dR_4 as k'; dand3 dR_4 as Hk' E L | pose proof ((lowbit_nonzero mask ltac:(lia))) as dR_4; dand4 dR_4 as k' Hk' E L | destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L) ]). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold ta_frame, SSP_GUARD in *.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tauto ];
    rewrite HG in H;
    pose proof (mrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold DEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.
  (* [comment removed for export] *)
  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia | lia | exact MU | exact WM]. }
  cbv beta. (intros ms'; (first [ intro dR_5; dex3 dR_5 as a1' a2' m'; dand6 dR_5 as -> MU' WM' MI' ST' MR' | intro dR_5; dand9 dR_5 as a1' a2' m' -> MU' WM' MI' ST' MR' | intros (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR') ])).
  do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.
End RASlz6s.


Module RASlh1b.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_ntf_C.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_C.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RF_egfy RF_m8yt SlotMisc RF_ntf_A RF_ntf_C RAlllfc RASlot_I Malluin.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.SlotMisc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Ltac mchunk MR MSq CH :=
  pose proof (mrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENTRY.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : mrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

#[using="AMS CLO SC MR"] Lemma ras_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  a0 = Z_to_bv 64 sc ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' : word) m' junk,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz run_guard) a1' (pw st (active st sc)) a3 a4 a5 a6 a7
                   a1 s3 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc)) (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (match active st sc with None => 0x23ea4 | Some _ => 0x23d28 end)) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (ta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk rsegs m' lo (bv_unsigned sp + -144)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep st m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 alloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros HA ST LO MI. subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _). unfold wz in G4.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold alloc_slot_entry, CTX, MLOCK, GOT_SSP, SSP_GUARD in *.
  (* [comment removed for export] *)
  step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step.
  rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : mrep st mX) by (eapply (mrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]) end.
  pose proof (mrep_active_read st _ sc (wa (402528 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
  step. clear RDA.
  (* [comment removed for export] *)
  step.
  replace (402520 + sc * 8 + 88) with (402528 + 80 + 8 * sc) by lia.
  replace (402520 + sc * 8) with (402520 + 8 * sc) by lia.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K.
  - destruct (active st sc) as [g|] eqn:HA.
    { exfalso. (first [ pose proof ((meta_slot_bounds st m g MR (AMS g eq_refl))) as dR_1; dand3 dR_1 as Gpos GC _ | pose proof (meta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
  - destruct (active st sc) as [g|] eqn:HA.
    2:{ exfalso. apply K. reflexivity. }
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section T1.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

(* [comment removed for export] *)
Definition t1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc))
      (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
#[using="AVR MSL MR Rr Clg"] Lemma t1_fin_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr <> 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (t1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23e64) fc None m (seg_rom rsegs))
    (MS (t1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d28) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros AVNZ MI. unfold t1_regs.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_2; dand5 dR_2 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr G in CH. fold G in CH.
  pose proof (sxv_range (m_avail mr)) as RA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
  { exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
  step. step.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="MSL MR Rr Clg"] Lemma t1_deq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr = 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (t1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23d4c) fc None m (seg_rom rsegs))
    (MS (t1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d28) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros AV0 FR0 MI. unfold t1_regs.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_3; dand5 dR_3 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. unfold pw, wz. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="FRR SC MSL MR"] Lemma t1_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (t1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23d8c) fc None m' (seg_rom rsegs)
      /\ munch [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (set_active sc (m_next mr) st) m')
    (MS (t1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d28) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros AV0 FRNZ MI. unfold t1_regs.
  pose proof (munch_refl [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_4; dand5 dR_4 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
  pose proof (sxv_range (m_freed mr)) as RF.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. step.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
  { exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (402528 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold CTX in MR2 end.
  raw_store_finish0 (402528 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section DEQ.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

(* [comment removed for export] *)
#[using="SC MSL MR"] Lemma rdeq_self_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_next mr = Some g -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23ea4) fc None m' (seg_rom rsegs)
      /\ munch [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (put_meta g (clr mr) (set_active sc None st)) m')
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d4c) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros GN MI. unfold t1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_5; dand5 dR_5 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  unfold CTX, MLOCK, SSP_GUARD in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step.
  (* [comment removed for export] *)
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (402528 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_active st mX sc None MR SC) as MR1; unfold CTX in MR1 end.
  raw_store_finish0 (402528 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
  set (st1 := set_active sc None st) in MR1.
  assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).
  (* [comment removed for export] *)
  meta_open G MUg WMg.
  mchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
  st1. st1.
  meta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.
  (* [comment removed for export] *)
  pose proof (mrep_active_read _ _ sc (wa (402528 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

(* [comment removed for export] *)
#[using="HA SC MSL MR"] Lemma rdeq_other_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
  m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  mem_inv rsegs m ->
  let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
  let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
  let st3 := set_active sc (Some nx) st2 in
  let st4 := put_meta g (clr mr) st3 in
  evt rsegs (fun ms' => exists (a1' : word) m',
      ms' = MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23d8c) fc None m' (seg_rom rsegs)
      /\ munch [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep st4 m')
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d4c) fc None m (seg_rom rsegs)).
Proof.
  intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold t1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_6; dand5 dR_6 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  (first [ pose proof ((meta_slot_bounds st m nx MR MSn)) as dR_7; dand5 dR_7 as Npos NC NI _ _ | pose proof (meta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _) ]).
  (first [ pose proof ((meta_slot_bounds st m pv MR MSp)) as dR_8; dand5 dR_8 as Ppos PC PI _ _ | pose proof (meta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _) ]).
  assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply conc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  unfold CTX, MLOCK, SSP_GUARD in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  mchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  step. clear CH.
  (* [comment removed for export] *)
  meta_open (conc st pv) MUp WMp.
  mchunk MR MSp CH.
  st1.
  meta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  (* [comment removed for export] *)
  mchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. step. clear CH.
  (* [comment removed for export] *)
  meta_open (conc st nx) MUn WMn.
  mchunk MR1 MSn1 CH.
  st1.
  meta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  (* [comment removed for export] *)
  pose proof (mrep_active_read st2 _ sc (wa (402528 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  mchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
  unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. clear CH. step.
  (* [comment removed for export] *)
  (first [ pose proof (MR2) as dR_9; dand3 dR_9 as _ (_ & ACTS & _) _ | pose proof MR2 as (_ & (_ & ACTS & _) & _) ]).
  pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (wa (402528 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold CTX in MR3 end.
  raw_store_finish0 (402528 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
  fold st3 in MR3.
  assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).
  (* [comment removed for export] *)
  meta_open G MUg WMg.
  mchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
  replace (get_meta_rec st3 g) with mr in CH.
  2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1.
  meta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.
  (* [comment removed for export] *)
  pose proof (mrep_active_read _ _ sc (wa (402528 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
  change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End DEQ.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section M.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

(* [comment removed for export] *)
#[using="MW FRR MSL MR Rr Clg"] Lemma rm_act_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  full_skip st g = false -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23db8) fc None m (seg_rom rsegs))
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d8c) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros NSK MI. unfold t1_regs.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_10; dand5 dR_10 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (Malluin.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *) apply evt_done. do 2 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  { apply evt_done. do 2 eexists. reflexivity. }
  exfalso. unfold full_skip in NSK. fold mr f in NSK.
  assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
  rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

(* [comment removed for export] *)
#[using="MW FRR SC MSL MR f"] Lemma rm_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
  full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
  0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23db8) fc None m' (seg_rom rsegs)
      /\ munch [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (set_active sc (Some mn) st) m')
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23d8c) fc None m (seg_rom rsegs)).
Proof.
  intros until mn. intros FSK GN MSn FNR MI. unfold t1_regs.
  pose proof (munch_refl [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_11; dand5 dR_11 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  (first [ pose proof ((meta_slot_bounds st m mn MR MSn)) as dR_12; dand5 dR_12 as Npos NC NI _ _ | pose proof (meta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _) ]).
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (Malluin.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
  apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
  unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.
  (* [comment removed for export] *)
  step. clear CH.
  (* [comment removed for export] *)
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (402528 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold CTX in MR2 end.
  raw_store_finish0 (402528 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
  mchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
  step. rewrite sx32_wz_sxv by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End M.
End RASlh1b.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_ntf_C.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_C.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RF_egfy RF_m8yt SlotMisc RF_ntf_A RF_ntf_C RAlllfc RASlot_I Malluin.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.SlotMisc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module ASlooxi.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux MRepAux MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallmv3 Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ag_frame (sc : Z) (j : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (Z_to_bv 64 (sc * 2)); CB 40 j; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section AG1.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.

(* [comment removed for export] *)
(* [comment removed for export] *)
End AG1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EPI.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (lo : Z).
Hypothesis CLO : alloc_ceiling <= lo.

(* [comment removed for export] *)

(* [comment removed for export] *)
End EPI.
End ASlooxi.

Module RF_muly.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3 RF_egfy Malls02.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
  upd_ctx (set_mmap_counter v)
    (put_meta g (big_meta rid n)
      (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).
Lemma big_ml_eq n : 0 <= n < 2^32 -> big_ml n = (n + 4115) / 4096.
Proof.
  intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.
Lemma cell_read_hdr_havoc_fresh : forall st b o,
  (s_shadow st) !! (fst b) = None -> snd b mod 16 = 0 -> 0 <= o < 12 ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.
Lemma meta_word_big_range rid n : 0 <= n < 2^32 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Lemma zeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
  (forall o, 0 <= o < Z.of_nat k -> bytes_at rsegs m (x + o) [b8 0]) -> bytes_at rsegs m x (zeros k).
Proof.
  intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  (first [ pose proof ((H (Z.of_nat i) ltac:(lia))) as dR_1; dand3 dR_1 as _ _ HB | destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB) ]). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed.

(* [comment removed for export] *)
Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

Lemma big_word_eq rid n : 0 <= n < 2^32 ->
  Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof.
  intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
  unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  replace (n + 4064 + 51) with (n + 4115) by lia.
  assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
    destruct (Z.lt_ge_cases i 12).
    - rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma big_fail1_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom rsegs)
                        /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x239ec) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Lemma big_fail2b_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom rsegs)
                        /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23bb8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Lemma big_fail2a_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
  rw_cells rsegs m MLOCK [C4 (wz 0)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x23bb8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) xw ndw a2 a3 a4 a5 a6 a7
                                     s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 munmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23ae0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros LK. unfold MLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x23bac)) with (Z_to_bv 64 0x23bac) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold munmap_entry. reflexivity.
Qed.

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition seq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x23ae0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK)
                  a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 alloc_meta_entry) fc None m' (seg_rom rsegs)
    /\ munch [(CTX + 848, CTX + 880); (CTX + 912, CTX + 913)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ mrep st' m'.

(* [comment removed for export] *)
Lemma big_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
    (lo n : Z) (st : mstate),
  mrep st m -> 0 <= c_seq (ctx st) < 256 ->
  bv_unsigned xw <> 2^64 - 1 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv rsegs m ->
  evt rsegs (seq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK)
               xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x239ec) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(CTX + 848, CTX + 880); (CTX + 912, CTX + 913)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold NEED_LOCKS, CTX, MLOCK, alloc_meta_entry in *. unfold ctx_tail_cells in C6.
  replace (402528 + 912) with 403440 in C6 by reflexivity. replace (402528 + 848) with 403376 in US by reflexivity.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
  (* [comment removed for export] *)
  step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
  (* [comment removed for export] *)
  step. rewrite ?zxb_b8 by lia. step.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> mrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk rsegs mj lo (bv_unsigned sp + -48) -> mem_inv rsegs mj ->
    munch [(402528 + 848, 402528 + 880); (402528 + 912, 402528 + 913)]%Z m mj -> wmono rsegs m mj ->
    evt rsegs (seq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 402520)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x23ad8) fc None mj (seg_rom rsegs))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    (first [ pose proof (MRj) as dR_2; dand3 dR_2 as _ (_ & _ & _ & _ & _ & C6j) _ | pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _) ]). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold CTX in C6j.
    replace (402528 + 912) with 403440 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 403440) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (mrep_set_seq stj mX ns MRj NS) as MR1; unfold CTX in MR1 end.
    raw_store_finishR (402528 + 912) [b8 ns] FRj STj MUj WMj SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. unfold seq_post, CTX, MLOCK, alloc_meta_entry. do 3 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr rsegs m1 403376 (zeros 32)).
    { apply (u8arr_of_rw_cells rsegs m1 403376 32). apply (rw_cells_congr rsegs m1 403376 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono rsegs m m1 |- _ =>
    assert (MRz : mrep stz m1);
    [ eapply (mrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold CTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold CTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold CTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold CTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold CTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold CTX; lia]
      | left; unfold CTX; replace (402528 + 912) with 403440 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX, FRc : rw_cells rsegs ?mX (bv_unsigned sp + -48) _, STc : stk rsegs ?mX _ _, MIc : mem_inv rsegs ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.

End CEIL.

Section SUCC.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="CLO NR CR HC SHN AN GN RR MSL G0 TK MR"] Lemma big_succ_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
  bv_unsigned gw = G ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a0' a1' : word) m',
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK)
                   a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23c78) fc None m' (seg_rom rsegs)
      /\ munch [(G, G + 40); (x, x + 8); (CTX + 12, CTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
      /\ mrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK)
             gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23ae0) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (CTX + 12, CTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). (first [ pose proof (WF) as dR_3; dand5 dR_3 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  (first [ pose proof ((meta_chunk_facts st m g MR MSL)) as dR_4; dand7 dR_4 as CH Gpos GC GI1 GI2 GRG (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0) | pose proof (meta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)) ]).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  (first [ pose proof ((WR rid r0 RR)) as dR_5; dand5 dR_5 as X0 _ XL XC XRF | destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF) ]). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
  (* [comment removed for export] *)
  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells rsegs m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply zeros_bytes_at; [lia| cbn; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
  (* [comment removed for export] *)
  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  unfold ctx_head_cells in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix rsegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl rsegs m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells rsegs mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (mrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (mrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : mrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (mrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold CTX in R1. lia.
    - unfold MLOCK in R2. lia.
    - unfold NEED_LOCKS in R3. lia.
    - unfold PAGE_SIZE_A in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      (first [ pose proof ((area_conc st ak ar WF Hak)) as dR_6; dex1 dR_6 as rga; dand7 dR_6 as Hra Ca Sa0 Sa1 _ NK _ | pose proof ((area_conc st ak ar WF Hak)) as dR_6; dand8 dR_6 as rga Hra Ca Sa0 Sa1 _ NK _ | destruct (area_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _) ]).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (area_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      (first [ pose proof ((group_conc st b gh WF Hb)) as dR_7; dex1 dR_7 as rb; dand6 dR_7 as Hrb Cb Kb Sb0 Sb1 _ | pose proof ((group_conc st b gh WF Hb)) as dR_7; dand7 dR_7 as rb Hrb Cb Kb Sb0 Sb1 _ | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ]).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold GOT_SSP in R5. lia.
    - unfold SSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : mrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (mrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (big_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells rsegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (mrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.
  (* [comment removed for export] *)
  step. rewrite (sx32_wz_sxv c) by lia. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX 402528 _ |- _ =>
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 402540) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold CTX in MRD end.
  clear MRC.
  raw_store_finishR (402528 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed.
End SUCC.
End RF_muly.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Ltac mchunk MR MSq CH :=
  pose proof (mrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Lemma meta_word_upd_af mr a f' : meta_word (m_set_avail a (m_set_freed f' mr)) = meta_word mr.
Proof. reflexivity. Qed.
Lemma decay_bounces_eq sc st :
  decay_bounces sc st =
  if ((7 <=? sc) && (sc <? 39)) && negb (bounces st (sc - 7) =? 0) then set_bounce (sc - 7) (bounces st (sc - 7) - 1) st else st.
Proof. reflexivity. Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lw_slli52_srli58_sc mq : mw_ok mq ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (meta_word mq)))) 52))) 58)
  = Z_to_bv 64 (m_sizeclass mq).
Proof.
  intros MWq. pose proof (meta_word_range _ MWq) as WR. (first [ pose proof (MWq) as dR_1; dand4 dR_1 as LI FB SCR ML | pose proof MWq as (LI & FB & SCR & ML) ]).
  f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite swrap32_eq'.
  unfold meta_word.
  Z.div_mod_to_equations. nia.
Qed.

Section AVZ.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

(* [comment removed for export] *)
#[using="AV0 MSL MR mr Rr Clg"] Lemma ravz_pre_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
  bv_unsigned gw = G -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (t1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23dec) fc None m (seg_rom rsegs))
    (MS (t1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23de0) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros HG MI. unfold t1_regs.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_2; dand5 dR_2 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  apply evt_done. reflexivity.
Qed.

#[using="SC0 BNC MASK MW FR32 AI Hgh Hmem AV0 MSL MR b"] Lemma avz_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
  bv_unsigned gw = G -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (t1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x23e64) fc None m' (seg_rom rsegs)
      /\ munch [(G, G + 40); (CTX + 880, CTX + 912)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep st5 m')
    (MS (t1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23dec) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros HG MI. unfold t1_regs.
  pose proof (munch_refl [(G, G + 40); (CTX + 880, CTX + 912)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_3; dand5 dR_3 as Gpos GC GI G4 G24 | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI, G4, G24.
  pose proof (meta_word_range _ MW) as MWR.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
  { apply amo_aligned_intro; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|]. rewrite HG. clear -G4; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
  clear G4 G24.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK, SSP_GUARD in *.
  mchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  (* [comment removed for export] *)
  step.
  (first [ pose proof ((mrep_group_read st _ b gh MR Hgh)) as dR_4; dand4 dR_4 as _ w8 RD8 L8 | destruct (mrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8) ]). unfold wa in RD8.
  pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
  step.
  (* [comment removed for export] *)
  step. step.
  assert (W8M : bv_unsigned w8 mod 32 = ai).
  { unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
  unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
  rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
  set (y := 2 ^ (ai + 1)).
  (* [comment removed for export] *)
  step. step. rewrite negw_word.
  (* [comment removed for export] *)
  pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
  step. rewrite sx32_wz_sxv by lia.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  (* [comment removed for export] *)
  clear CH. meta_open G MUa WMa. rewrite <- HG in MUa.
  mchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  step. if_false.
  amo_step AMO.
  step. if_false.
  step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.
  (* [comment removed for export] *)
  step. rewrite addiw_m1_word.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  step.
  (* [comment removed for export] *)
  assert (AI31 : Z.land ai 31 = ai).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
  assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
  assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
  pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
  pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
  pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : mrep st4 mX) end.
  { rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply mrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
    eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tauto].
    unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
    rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
  clear MUa WMa.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.
  2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
      rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite ?Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
  clear K1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HRW : ov_read_bytes rsegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
      by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read rsegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
  step. step. step.
  rewrite (lw_slli52_srli58_sc mr MW).
  pose proof MW as (_ & _ & SCR & _). fold mr in SCR.
  set (sc := m_sizeclass mr) in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite ?Z.land_ones in K2 by lia.
  - (* [comment removed for export] *)
    assert (NR : (7 <=? sc) && (sc <? 39) = false).
    { destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
      apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
    apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
    split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
  - (* [comment removed for export] *)
    assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; try (generalize alloc_ceiling_val); clear -K2 H SCR; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia]).
    rewrite Z.mod_small in K2 by lia.
    assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    (* [comment removed for export] *)
    step.
    pose proof (mrep_bounces_read (Clg:=Clg) st4 _ (sc - 7) (wa (402528 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
    change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
    pose proof (BNC (sc - 7)) as BR.
    step. rewrite ?zxb_b8 by lia.
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
    + (* [comment removed for export] *)
      step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
      (first [ pose proof (MR4) as dR_5; dand3 dR_5 as _ (_ & _ & _ & _ & X5 & _) _ | pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _) ]).
      pose proof (u8arr_store_ok rsegs _ _ _ (sc - 7) (Z_to_bv 64 (402520 + (sc + -7) + 888)) X5
                    ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear X5 RDB.
      st1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
        pose proof (mrep_set_bounce (Clg:=Clg) st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold CTX in MR5 end.
      raw_store_finish0 (402528 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
      apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|].
      split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
End AVZ.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section SPANLOOP.

Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

#[using="SZ"] Lemma rspan_loop_walk : forall (F : nat) (c span : Z)
    (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= c -> 0 <= span -> span + size * (Z.of_nat F + 2) < 2^31 -> c + 1 + Z.of_nat F < 2^31 ->
  span_exit F span size = true -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' a6' : word),
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (span_loop F (c + 1) span size)) (wz size) a6' (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x241f4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp (wz span) t1 t2 s0 s1 a0 a1 a2 a3 (wz c) (wz size) (wz (span + size - 1)) (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x241e0) fc None m (seg_rom rsegs)).
Proof.
  induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
  cbn [span_exit] in EX. cbn [span_loop].
  rewrite Nat2Z.inj_succ in SB, CB.
  pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.
  (* [comment removed for export] *)
  step. rewrite ?wz_unsigned by lia.
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
  rewrite (Z.lxor_comm (span + size - 1) span).
  (* [comment removed for export] *)
  step. if_cases K.
  - (* [comment removed for export] *)
    assert (LT : Z.lxor span (span + size - 1) < 4096).
    { unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
    replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
    replace (c + 2) with (c + 1 + 1) by lia.
    eapply (IH (c + 1) (span + size)); try assumption; try lia.
  - assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
    { intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
    replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. do 3 eexists. reflexivity.
Qed.
End SPANLOOP.
Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
  Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof.
  intros Hw Hv. apply Z.bits_inj'. intros n Hn.
  change 256 with (2^8). change 31 with (Z.ones 5).
  rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  replace 224 with (Z.shiftl 7 5) by reflexivity.
  destruct (Z.ltb_spec n 5).
  - rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
  - replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ACT.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

(* [comment removed for export] *)
Ltac act_prefix CH w8 :=
  mchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
  step;
  let RD8 := fresh "RD8" in let L8 := fresh "L8" in
  destruct (mrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
  let W8R := fresh "W8R" in
  pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
  step;
  let W8M := fresh "W8M" in
  assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
  step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
  step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
  step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

(* [comment removed for export] *)
#[using="MASKR AI0 Hgh Hmem MSL MR mr b Rr Clg"] Lemma ract_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) <> 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' a3' a4' : word),
      ms' = MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x23de0) fc None m (seg_rom rsegs))
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x23db8) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros NZ MI. unfold t1_regs.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_6; dand5 dR_6 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  (first [ pose proof ((group_bounds st m b gh MR Hgh)) as dR_7; dand4 dR_7 as B0 BC BI _ | pose proof (group_bounds st m b gh MR Hgh) as (B0 & BC & BI & _) ]).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold CTX, MLOCK, SSP_GUARD in *.
  act_prefix CH w8.
  pose proof (Malluin.mask_upto_range ai0 AI0) as MUR.
  pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
  step. if_cases K; zify_cond K.
  2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
      rewrite ?wz_unsigned in K by (apply sxv_range).
      first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
  apply evt_done. do 4 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="AI0 Hgh Hmem SC MSL MR b"] Lemma ract_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' a3' a4' : word) m',
      ms' = MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x23de0) fc None m' (seg_rom rsegs)
      /\ munch [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (set_active sc (Some mn) st) m')
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x23db8) fc None m (seg_rom rsegs)).
Proof.
  intros until mn. intros ZR GN NEn MSn MI. unfold t1_regs.
  pose proof (munch_refl [(CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_8; dand5 dR_8 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  (first [ pose proof ((meta_slot_bounds st m mn MR MSn)) as dR_9; dand5 dR_9 as Npos NC NI _ _ | pose proof (meta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _) ]).
  (first [ pose proof ((group_bounds st m b gh MR Hgh)) as dR_10; dand4 dR_10 as B0 BC BI _ | pose proof (group_bounds st m b gh MR Hgh) as (B0 & BC & BI & _) ]).
  assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply conc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold CTX, MLOCK, SSP_GUARD in *.
  act_prefix CH w8.
  pose proof (Malluin.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN in CH. cbn [oconc] in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (402528 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold CTX in MR2 end.
  raw_store_finish0 (402528 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
(* [comment removed for export] *)
#[using="AI0 Hgh MSL MR ai0"] Lemma rspan_tail_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
  1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc))
                   (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x23dec) fc None m' (seg_rom rsegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc))
             (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x24204) fc None m (seg_rom rsegs)).
Proof.
  intros until wv. intros C2R WVR UNK GM AV0 MI.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_11; dand5 dR_11 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  (first [ pose proof ((group_bounds st m b gh MR Hgh)) as dR_12; dand4 dR_12 as B0 BC BI _ | pose proof (group_bounds st m b gh MR Hgh) as (B0 & BC & BI & _) ]).
  pose proof MR as (_ & _ & _ & _ & GR & _). (first [ pose proof ((GR b gh Hgh)) as dR_13; dex1 dR_13 as w8o; destruct dR_13 as [RWB Hw8o] | pose proof ((GR b gh Hgh)) as dR_13; dand3 dR_13 as w8o RWB Hw8o | destruct (GR b gh Hgh) as (w8o & RWB & Hw8o) ]). clear GR.
  unfold CTX, MLOCK, SSP_GUARD in *.
  pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl rsegs m) as WMb.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
  pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
  pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
  rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
  set (nbv := Z.lor _ _).
  (* [comment removed for export] *)
  step. rewrite (le1_mod nbv). mem_after_store.
  pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
  pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
  lazymatch goal with H : rw_cells rsegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : mrep (set_group_active_idx b (cnt2 - 1) st) mX);
    [ eapply (mrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
    | ] end.
  { rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
  { lazymatch goal with H : rw_cells rsegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
  { rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }
  (* [comment removed for export] *)
  assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
  mchunk MR2 MS2 CH.
  replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
  replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
  rewrite AV0 in CH.
  step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.

(* [comment removed for export] *)
#[using="AI0 Hgh Hmem MSL MR"] Lemma ract_span_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 ->
  mem_inv rsegs m ->
  let sc' := m_sizeclass mr in
  let cnt := ai0 + 2 in
  let size := size_class sc' * UNIT in
  let span := UNIT + size * cnt in
  let cnt1 := span_loop 300 cnt span size in
  let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
  evt rsegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc))
                   (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x23dec) fc None m' (seg_rom rsegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x23db8) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold t1_regs.
  (first [ pose proof ((meta_slot_bounds st m g MR MSL)) as dR_14; dand5 dR_14 as Gpos GC GI _ _ | pose proof (meta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI.
  (first [ pose proof ((group_bounds st m b gh MR Hgh)) as dR_15; dand4 dR_15 as B0 BC BI _ | pose proof (group_bounds st m b gh MR Hgh) as (B0 & BC & BI & _) ]).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & _ & ML).
  pose proof (size_class_range sc' ltac:(lia)) as SZR.
  unfold CTX, MLOCK, SSP_GUARD, SIZE_CLASSES in *.
  act_prefix CH w8.
  pose proof (Malluin.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.
  (* [comment removed for export] *)
  assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
  step.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ =>
    pose proof (size_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold SIZE_CLASSES in SCRD end.
  step. rewrite zx16_wz by lia. clear SCRD.
  fold cnt.
  assert (SZB : 16 <= size <= 131056) by (unfold size, UNIT; lia).
  assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
  assert (PR : 0 <= cnt * size <= 33 * 131128) by nia.
  assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
  assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
  assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
  pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
  assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
  assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
  clearbody size cnt span cnt1 cnt2.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
  step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
  replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
  step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
  step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
  replace (span + size - 16 + 15) with (span + size - 1) by lia.
  step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
  step.
  (* [comment removed for export] *)
  eapply evt_cut.
  { change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
    eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
  (intros ms'; (first [ intro dR_16; dand4 dR_16 as t0' t1' a6' -> | intros (t0' & t1' & a6' & ->) ])). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
  - replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. (intros ms2; (first [ intro dR_17; dex4 dR_17 as a1'' a2'' a4'' m'; dand5 dR_17 as -> MU WM MI' MR' | intro dR_17; dand9 dR_17 as a1'' a2'' a4'' m' -> MU WM MI' MR' | intros (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR') ])). do 10 eexists. split; [reflexivity|]. eauto.
  - (* [comment removed for export] *)
    step.
    replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. (intros ms2; (first [ intro dR_18; dex4 dR_18 as a1'' a2'' a4'' m'; dand5 dR_18 as -> MU WM MI' MR' | intro dR_18; dand9 dR_18 as a1'' a2'' a4'' m' -> MU WM MI' MR' | intros (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR') ])). do 10 eexists. split; [reflexivity|]. eauto.
Qed.
End ACT.