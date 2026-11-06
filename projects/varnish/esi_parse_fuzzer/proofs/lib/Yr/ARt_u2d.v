(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface ACells AIcpm9j ARtStmts AMTac.

Module ARt_srv.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition classid_mach (s : Z) : Z :=
  let x   := Z.shiftr (uw s) 1 in
  let x0  := Z.lor (uw s) (uw x) in
  let x1  := Z.shiftr (uw x0) 2 in
  let x2  := Z.lor (uw x0) (uw x1) in
  let x3  := Z.shiftr (uw x2) 4 in
  let x4  := Z.lor (uw x2) (uw x3) in
  let x5  := Z.shiftr (uw x4) 8 in
  let x6  := Z.lor (uw x4) (uw x5) in
  let x7  := Z.shiftr (uw x6) 16 in
  let x8  := Z.lor (uw x6) (uw x7) in
  let x9  := Z.shiftr (uw x8) 32 in
  let x10 := Z.lor (uw x8) (uw x9) in
  let x11 := Z.lxor (uw x10) 18446744073709551615 in
  let x12 := Z.shiftr (uw x11) 1 in
  let x13 := Z.land (uw x12) 6148914691236517205 in
  let x14 := uw x11 - uw x13 in
  let x15 := Z.land (uw x14) 3689348814741910323 in
  let x16 := Z.shiftr (uw x14) 2 in
  let x17 := Z.land (uw x16) 3689348814741910323 in
  let x18 := x15 + x17 in
  let x19 := Z.shiftr (uw x18) 4 in
  let x20 := x18 + x19 in
  let x21 := Z.land (uw x20) 1085102592571150095 in
  let x22 := uw x21 * 72340172838076673 in
  let x23 := Z.shiftr (uw x22) 56 in
  let x24 := bv_swrap 32 (62 - uw x23) in
  let x25 := Z.shiftl (uw x23) 1 in
  let x26 := Z.shiftr (uw s) (uw x24 mod 64) in
  let x27 := bv_swrap 32 (Z.shiftl 18446744073709551615 (uw x24 mod 32)) in
  let x28 := Z.lxor (uw x25) 126 in
  let x29 := Z.land (uw x26) 1 in
  let x30 := Z.lxor (uw x27) 18446744073709551615 in
  let x31 := Z.land (uw s) (uw x30) in
  let x32 := Z.lor (uw x28) (uw x29) in
  let x33 := x32 + bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x31)) in
  x33 + -2.

(* [comment removed for export] *)
Fixpoint all_from (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S n' => f lo && all_from f (lo + 1) n' end.
Lemma all_from_sound : forall f n lo, all_from f lo n = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
  intros f n. induction n as [|n IH]; intros lo H i Hi; [cbn in Hi; lia|].
  cbn [all_from] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec i lo) as [->|NE]; [exact H1|].
  apply (IH (lo + 1) H2). rewrite Nat2Z.inj_succ in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uwf (z : Z) : Z := if (0 <=? z) && (z <? 18446744073709551616) then z else uw z.
Lemma uwf_eq : forall z, uwf z = uw z.
Proof.
  intros z. unfold uwf. destruct ((0 <=? z) && (z <? 18446744073709551616)) eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold uw. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.
Definition bindZ (a : Z) (k : Z -> Z) : Z := k a.
Lemma bindZ_ext : forall (a a' : Z) (k k' : Z -> Z), a = a' -> (forall x, k x = k' x) -> bindZ a k = bindZ a' k'.
Proof. intros a a' k k' -> H. exact (H a'). Qed.
Definition classid_mach_g (U : Z -> Z) (s : Z) : Z :=
  bindZ (Z.shiftr (U s) 1) (fun x =>
  bindZ (Z.lor (U s) (U x)) (fun x0 =>
  bindZ (Z.shiftr (U x0) 2) (fun x1 =>
  bindZ (Z.lor (U x0) (U x1)) (fun x2 =>
  bindZ (Z.shiftr (U x2) 4) (fun x3 =>
  bindZ (Z.lor (U x2) (U x3)) (fun x4 =>
  bindZ (Z.shiftr (U x4) 8) (fun x5 =>
  bindZ (Z.lor (U x4) (U x5)) (fun x6 =>
  bindZ (Z.shiftr (U x6) 16) (fun x7 =>
  bindZ (Z.lor (U x6) (U x7)) (fun x8 =>
  bindZ (Z.shiftr (U x8) 32) (fun x9 =>
  bindZ (Z.lor (U x8) (U x9)) (fun x10 =>
  bindZ (Z.lxor (U x10) 18446744073709551615) (fun x11 =>
  bindZ (Z.shiftr (U x11) 1) (fun x12 =>
  bindZ (Z.land (U x12) 6148914691236517205) (fun x13 =>
  bindZ (U x11 - U x13) (fun x14 =>
  bindZ (Z.land (U x14) 3689348814741910323) (fun x15 =>
  bindZ (Z.shiftr (U x14) 2) (fun x16 =>
  bindZ (Z.land (U x16) 3689348814741910323) (fun x17 =>
  bindZ (x15 + x17) (fun x18 =>
  bindZ (Z.shiftr (U x18) 4) (fun x19 =>
  bindZ (x18 + x19) (fun x20 =>
  bindZ (Z.land (U x20) 1085102592571150095) (fun x21 =>
  bindZ (U x21 * 72340172838076673) (fun x22 =>
  bindZ (Z.shiftr (U x22) 56) (fun x23 =>
  bindZ (bv_swrap 32 (62 - U x23)) (fun x24 =>
  bindZ (Z.shiftl (U x23) 1) (fun x25 =>
  bindZ (Z.shiftr (U s) (U x24 mod 64)) (fun x26 =>
  bindZ (bv_swrap 32 (Z.shiftl 18446744073709551615 (U x24 mod 32))) (fun x27 =>
  bindZ (Z.lxor (U x25) 126) (fun x28 =>
  bindZ (Z.land (U x26) 1) (fun x29 =>
  bindZ (Z.lxor (U x27) 18446744073709551615) (fun x30 =>
  bindZ (Z.land (U s) (U x30)) (fun x31 =>
  bindZ (Z.lor (U x28) (U x29)) (fun x32 =>
  bindZ (x32 + bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x31))) (fun x33 =>
  x33 + -2))))))))))))))))))))))))))))))))))).
Lemma classid_mach_g_ext : forall U V : Z -> Z, (forall z, U z = V z) -> forall s, classid_mach_g U s = classid_mach_g V s.
Proof.
  intros U V H s. unfold classid_mach_g.
  repeat (apply bindZ_ext; [rewrite ?H; reflexivity | intro]).
  rewrite ?H. reflexivity.
Qed.
Lemma all_from_ext : forall (f g : Z -> bool) n lo, (forall i, f i = g i) -> all_from f lo n = all_from g lo n.
Proof. intros f g n. induction n as [|n IH]; intros lo H; [reflexivity|]. cbn [all_from]. rewrite (H lo), (IH (lo + 1) H). reflexivity. Qed.
Lemma classid_mach_check_f : all_from (fun k => Z.eqb (classid_mach_g uwf (8 * k)) (size_class (8 * k))) 65 8128 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma classid_mach_check : all_from (fun k => Z.eqb (classid_mach (8 * k)) (size_class (8 * k))) 65 8128 = true.
Proof.
  rewrite (all_from_ext _ (fun k => Z.eqb (classid_mach_g uwf (8 * k)) (size_class (8 * k)))); [exact classid_mach_check_f|].
  intros k. change (classid_mach (8 * k)) with (classid_mach_g uw (8 * k)). rewrite (classid_mach_g_ext uwf uw uwf_eq). reflexivity.
Qed.

Lemma classid_mach_ok : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> classid_mach s = size_class s.
Proof.
  intros s Hs H8. rewrite (proj2 (Z.div_exact s 8 ltac:(lia)) H8).
  apply Z.eqb_eq. apply (all_from_sound _ _ _ classid_mach_check (s / 8)).
  replace (65 + Z.of_nat 8128) with 8193 by (vm_compute; reflexivity).
  pose proof (Z.div_mod s 8 ltac:(lia)). lia.
Qed.

Ltac gen_regs :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        tryif is_var e then fail else tryif is_Zlit e then fail else
          (let x := fresh "x" in let H := fresh "Hx" in remember e as x eqn:H) end
  end.

(* [comment removed for export] *)
Ltac gen_regs_set :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        tryif is_var e then fail else tryif is_Zlit e then fail else
          (let x := fresh "x" in set (x := e)) end
  end.
Theorem classid_blk_ok : classid_blk_stmt.
Proof.
  unfold classid_blk_stmt. intros until Q. intros HS H8 K. unfold classid_blk_entry, classid_blk_exit in *.
  do 55 (step; gen_regs_set).
  match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    match R with context [Some (Z_to_bv 64 ?e)] =>
      constr_eq e x34; replace (Z_to_bv 64 x34) with (Z_to_bv 64 (size_class s)); [apply K|] end end.
  f_equal. rewrite <- (classid_mach_ok s HS H8).
  subst x34 x33 x32 x31 x30 x29 x28 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x17 x16 x15 x14 x13 x12 x11 x10
        x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 x.
  reflexivity.
Qed.
End ARt_srv.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require LayoutPA.

Module ARt_yhn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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

Lemma uw_range : forall z, 0 <= uw z < 2^64.
Proof. intros z. unfold uw. apply (zr_word (Z_to_bv 64 z)). Qed.
(* [comment removed for export] *)

Lemma lxor_u64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia].
Qed.

Lemma depot_hashC_range : forall k, 0 <= depot_hashC k < 2^64.
Proof. intros k. unfold depot_hashC. cbv zeta. apply lxor_u64; apply uw_range. Qed.

(* [comment removed for export] *)
Fixpoint w_cells (ws : list Z) : list cell := match ws with [] => [] | w :: ws' => C8 (wz w) :: w_cells ws' end.
Lemma w_cells_size : forall ws, Z.of_nat (cells_size (w_cells ws)) = 8 * Z.of_nat (length ws).
Proof. induction ws; cbn [w_cells cells_size csize length]; [reflexivity|]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, IHws. lia. Qed.

Lemma ro_cells_cons_split : forall m A c cs,
  ro_cells rsegs m A (c :: cs) -> ro_cells rsegs m A [c] /\ ro_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [WF BA]. cbn [cells_wf] in WF. destruct WF as [WF1 WF2].
  cbn [cells_bytes] in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite (cbytes_length c WF1) in BA2.
  split; split; cbn [cells_wf cells_bytes]; try tauto. rewrite app_nil_r. exact BA1.
Qed.

(* [comment removed for export] *)
Section Loop.
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variable Q : machine_state -> Prop.

  Lemma hash_loop : forall (ws : list Z) (ptr fin h : Z) (ra t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 : word),
    ws <> [] -> Forall (fun w => 0 <= w < 2^64) ws ->
    mem_inv rsegs m -> ro_cells rsegs m ptr (w_cells ws) -> fin = ptr + 8 * Z.of_nat (length ws) -> fin <= 2^47 ->
    (forall (a5' a6' : word),
        evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz murmur_M) (wz fin) (wz (fold_left murmur_mix ws h)) a3 (wz fin) a5' a6' a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x78eac) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz murmur_M) (wz ptr) (wz h) a3 (wz fin) a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x78e88) fc None m (seg_rom rsegs)).
  Proof.
    induction ws as [|w ws IH]; intros ptr fin h ra t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 NE FA MI RO FIN FHI K; [congruence|].
    apply Forall_cons_iff in FA. destruct FA as [Wr FA].
    pose proof (ro_cells_bound _ _ _ _ RO) as B. rewrite w_cells_size in B. cbn [length] in FIN.
    unfold murmur_M in *. change (w_cells (w :: ws)) with (C8 (wz w) :: w_cells ws) in RO. cbn [length] in B.
    do 8 (step; gen_regs).
    assert (X5 : x5 = murmur_mix h w) by (subst x5 x4 x3 x2 x1 x0; reflexivity).
    clear Hx5. subst x5. subst x.
    step. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      destruct ws as [|w' ws']; [exfalso; cbn [length] in FIN; rewrite ?unsigned_lit in KB by lia; lia|].
      apply ro_cells_cons_split in RO as [_ RO]. change (Z.of_nat (csize (C8 (wz w)))) with 8 in RO.
      cbn [length] in FIN. rewrite Nat2Z.inj_succ in FIN.
      apply (IH (ptr + 8) fin (murmur_mix h w)); [congruence | exact FA | exact MI | exact RO | cbn [length]; lia | exact FHI | exact K].
    - (* [comment removed for export] *)
      destruct ws as [|w' ws']; [| exfalso; cbn [length] in FIN; rewrite !Nat2Z.inj_succ in FIN; rewrite ?unsigned_lit in KB by lia; lia].
      cbn [length] in FIN. subst fin. replace (ptr + 8 * 1) with (ptr + 8) in K by lia. cbn [fold_left] in K. apply K.
  Qed.

End Loop.

  (* [comment removed for export] *)
  Lemma shl44_shr42 : forall a, 0 <= a -> Z.shiftr (uw (Z.shiftl a 44)) 42 = 4 * (a mod 2^20).
  Proof.
    intros a Ha. unfold uw. rewrite unsigned_lit_wrap.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    change (2^64) with (2^20 * 2^44). rewrite Z.mul_mod_distr_r by lia.
    change (2^44) with (4 * 2^42). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
  Qed.

  Lemma hash_block : forall (sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : word -> option byte) (Q : machine_state -> Prop) (k : list Z) (tr : Z) (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    k <> [] -> Forall (fun w => 0 <= w < 2^64) k -> (length k < 256)%nat ->
    mem_inv rsegs m -> ro_cells rsegs m tr (w_cells k) -> tr + 8 * Z.of_nat (length k) <= 2^47 ->
    let s1 := wz 0x197298 in
    (forall (a0' a1' a2' a4' a5' a6' : word),
        evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' (wz 0x400000) a4' a5' a6' a7
                         (wz (0x197298 + 4 * (depot_hashC k mod 2^20))) (wz (depot_hashC k)) s4 s5
                         (wz 0xffff) (wz 0x7fffffff) s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x78ef8) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz tr) (wz (Z.of_nat (length k))) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x78e50) fc None m (seg_rom rsegs)).
  Proof.
    intros until t6. intros NE FA LEN MI RO THI s1 K. subst s1. unfold murmur_M in *.
    pose proof (ro_cells_bound _ _ _ _ RO) as B. rewrite w_cells_size in B.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x78e88) _ _ _ _) => fail | _ => step; gen_regs end).
    (* [comment removed for export] *)
    assert (U0 : bv_unsigned (Z_to_bv 64 x0) = x0) by (apply unsigned_lit; lia).
    assert (X1 : x1 = x0).
    { rewrite Hx1, U0. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (X3 : x3 = 8 * x0).
    { rewrite Hx3, X1, U0. rewrite Z.shiftl_mul_pow2 by lia. lia. }
    apply hash_loop with (ws := k) (ptr := tr) (fin := x5) (h := x4); [exact NE | exact FA | exact MI | exact RO | lia | lia |].
    intros a5' a6'. unfold murmur_M.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x78ef8) _ _ _ _) => fail | _ => step; gen_regs end).
    assert (HF : x17 = depot_hashC k).
    { rewrite Hx17, Hx16, Hx15, Hx14, Hx13, Hx12, Hx11, Hx10, Hx9, Hx8, Hx7, Hx6, Hx4, Hx2, Hx1, Hx, Hx0. reflexivity. }
    pose proof (depot_hashC_range k) as HR.
    assert (HB : x20 = 1667736 + 4 * (depot_hashC k mod 2^20)).
    { rewrite Hx20, Hx19, Hx18, HF. unfold uw. rewrite (unsigned_lit (depot_hashC k)) by lia.
      fold (uw (Z.shiftl (depot_hashC k) 44)). rewrite shl44_shr42 by lia. reflexivity. }
    rewrite HB, HF. apply K.
  Qed.
End ARt_yhn.


Module ARt_dmf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From stdpp Require Import bitvector.definitions.
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
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint chain_ok (lnk : Z -> Z) (c : list Z) : Prop :=
  match c with [] => True | s :: rest => lnk s = hd 0 rest /\ chain_ok lnk rest end.
Fixpoint cfind (hsh : Z -> Z) (h : Z) (c : list Z) : Z :=
  match c with [] => 0 | s :: rest => if Z.eqb (hsh s) h then s else cfind hsh h rest end.

Lemma srliw16_small : forall s, 0 <= s < 65536 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 s) 16) = 0.
Proof.
  intros s Hs. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.
Lemma idx16 : forall s, 0 <= s < 65536 -> Z.shiftl (Z.land (s mod 4294967296) 65535) 4 = 16 * s.
Proof.
  intros s Hs. rewrite Z.mod_small by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.mod_small by lia.
  rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Section Find.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop).
  Variables (h n0 nmax : Z) (hsh lnk sid : Z -> Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis HR : 0 <= h < 2^64.
  Hypothesis N0 : aobj n0 kDepotNodesBlock.   (* [comment removed for export] *)
  Hypothesis N1 : n0 + kDepotNodesBlock <= alloc_ceiling.
  Hypothesis NMAX : 0 <= nmax < 65536.
  Hypothesis MAP : ro_cells rsegs m 0x5972a8 [C8 (wz n0)].
  Hypothesis NODES : forall s, 1 <= s <= nmax ->
    rw_cells rsegs m (n0 + 16 * s) [C8 (wz (hsh s)); C4 (wz (lnk s)); C4 (wz (sid s))]
    /\ 0 <= hsh s < 2^64 /\ 0 <= lnk s <= nmax /\ 0 <= sid s < 2^31.

  Definition find_st (a0 a1 a2 : word) (pc : Z) : machine_state :=
    MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz h) s4 s5 (wz 0xffff) s7 (wz 0x5972a8) s9 s10 s11 t3 t4 t5 t6)
       F (wz pc) fc None m (seg_rom rsegs).

  #[using="NODES MAP NMAX N0 HR sid n0 Clg"] Lemma find_loop : forall (c : list Z) (a0 a2 : word),
    chain_ok lnk c -> Forall (fun s => 1 <= s <= nmax) c ->
    (cfind hsh h c = 0 -> forall a0' a2', evt rsegs Q (find_st a0' (wz 0) a2' 0x78f70)) ->
    (forall s, cfind hsh h c = s -> s <> 0 -> forall a1' a2', evt rsegs Q (find_st (wz s) a1' a2' 0x7901c)) ->
    evt rsegs Q (find_st a0 (wz (hd 0 c)) a2 0x78f18).
  Proof.
    unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kDepotNodesBlock in *. aobj_lin_allS. pose proof alloc_ceiling_val as CV.
    induction c as [|s rest IH]; intros a0 a2 CH FA KNF KF; unfold find_st; cbn [hd].
    - zstep. br_taken. apply (KNF eq_refl).
    - apply Forall_cons_iff in FA. destruct FA as [SR FA]. destruct CH as [LNK CH].
      (first [ pose proof ((NODES s SR)) as dR_1; dand4 dR_1 as ND HSR LR SIDR | destruct (NODES s SR) as (ND & HSR & LR & SIDR) ]).
      zstep. br_not_taken.
      zstep. zstep. rewrite srliw16_small by lia.
      zstep. zstep. zstep. zstep. br_not_taken. zstep. zstep. zstep. zstep. rewrite idx16 by lia.
      zstep. remember (n0 + 16 * s) as nd eqn:ND_.
      zstep. zstep. rewrite sx32_small by lia.
      zstep. if_cases KB; zify_cond KB.
      + (* [comment removed for export] *)
        rewrite LNK. apply IH; [exact CH | exact FA | |].
        * intros NF. apply KNF. cbn [cfind]. destruct (Z.eqb_spec (hsh s) h); [lia | exact NF].
        * intros s' FS NZ. apply KF; [|exact NZ]. cbn [cfind]. destruct (Z.eqb_spec (hsh s) h); [lia | exact FS].
      + (* [comment removed for export] *)
        zstep. apply (KF s); [| plia]. cbn [cfind]. destruct (Z.eqb_spec (hsh s) h); [reflexivity | plia].
  Qed.
End Find.
End ARt_dmf.


Module ARt_wg1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARtStmts.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_dmf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Notation key := (list Z) (only parsing).
Definition bkt (d : key) : Z := depot_hashC d mod 2^20.

Fixpoint chainL (D : list key) (b : Z) (i : Z) : list Z :=
  match D with [] => [] | d :: D' => chainL D' b (i + 1) ++ (if Z.eqb (bkt d) b then [i] else []) end.
Definition headL (D : list key) (b : Z) : Z := hd 0 (chainL D b 1).
Definition keyL (D : list key) (i : Z) : key := nth (Z.to_nat (i - 1)) D [].
Definition linkL (D : list key) (i : Z) : Z := headL (firstn (Z.to_nat (i - 1)) D) (bkt (keyL D i)).
Definition sidL (D : list key) (i : Z) : Z := depot_off D (Z.to_nat (i - 1)) + 1.
Definition hshL (D : list key) (i : Z) : Z := depot_hashC (keyL D i).

(* [comment removed for export] *)
Lemma chainL_app : forall D1 D2 b i, chainL (D1 ++ D2) b i = chainL D2 b (i + Z.of_nat (length D1)) ++ chainL D1 b i.
Proof.
  induction D1 as [|d D1 IH]; intros D2 b i; cbn [app chainL length].
  - rewrite app_nil_r. f_equal. lia.
  - rewrite IH, <- app_assoc. f_equal. f_equal. lia.
Qed.

Lemma chainL_snoc : forall D d b i,
  chainL (D ++ [d]) b i = (if Z.eqb (bkt d) b then [i + Z.of_nat (length D)] else []) ++ chainL D b i.
Proof. intros. rewrite chainL_app. cbn [chainL]. rewrite app_nil_l. reflexivity. Qed.

Lemma chainL_bounds : forall D b i x, In x (chainL D b i) -> i <= x < i + Z.of_nat (length D).
Proof.
  induction D as [|d D IH]; intros b i x Hx; cbn [chainL length] in *; [tauto|].
  apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
  - apply IH in Hx. lia.
  - destruct (Z.eqb (bkt d) b); cbn in Hx; [|tauto]. destruct Hx as [<-|[]]. lia.
Qed.

Lemma chainL_bkt : forall D b i x, In x (chainL D b i) -> bkt (nth (Z.to_nat (x - i)) D []) = b.
Proof.
  induction D as [|d D IH]; intros b i x Hx; cbn [chainL] in Hx; [tauto|].
  apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
  - pose proof (chainL_bounds _ _ _ _ Hx). apply IH in Hx.
    replace (Z.to_nat (x - i)) with (S (Z.to_nat (x - (i + 1)))) by lia. cbn [nth]. exact Hx.
  - destruct (Z.eqb_spec (bkt d) b); cbn in Hx; [|tauto]. destruct Hx as [<-|[]].
    rewrite Z.sub_diag. cbn. assumption.
Qed.

Lemma chainL_complete : forall D b i j, (j < length D)%nat -> bkt (nth j D []) = b -> In (i + Z.of_nat j) (chainL D b i).
Proof.
  induction D as [|d D IH]; intros b i j Hj Hb; cbn [length] in Hj; [lia|].
  cbn [chainL]. apply in_app_iff. destruct j as [|j].
  - right. cbn [nth] in Hb. rewrite Hb, Z.eqb_refl. cbn. left. lia.
  - left. cbn [nth] in Hb. replace (i + Z.of_nat (S j)) with ((i + 1) + Z.of_nat j) by lia. apply IH; [lia| exact Hb].
Qed.

Lemma chainL_cons_inv : forall D b i s rest, chainL D b i = s :: rest ->
  rest = chainL (firstn (Z.to_nat (s - i)) D) b i /\ i <= s < i + Z.of_nat (length D).
Proof.
  induction D as [|d D IH] using rev_ind; intros b i s rest E; [cbn in E; discriminate|].
  rewrite chainL_snoc in E. rewrite length_app. cbn [length].
  destruct (Z.eqb_spec (bkt d) b) as [Hb|Hb]; cbn [app] in E.
  - injection E as <- <-. replace (Z.to_nat (i + Z.of_nat (length D) - i)) with (length D) by lia.
    rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. split; [reflexivity| plia].
  - destruct (IH b i s rest E) as [R B]. split; [|lia].
    rewrite firstn_app. replace (Z.to_nat (s - i) - length D)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact R.
Qed.

(* [comment removed for export] *)
Lemma chain_ok_ext : forall f g c, chain_ok f c -> (forall x, In x c -> g x = f x) -> chain_ok g c.
Proof.
  induction c as [|s c IH]; intros CH AG; cbn in *; [exact I|].
  destruct CH as [L CH]. split; [rewrite AG by (left; reflexivity); exact L|].
  apply IH; [exact CH|]. intros x Hx. apply AG. right; exact Hx.
Qed.

Lemma nth_firstn_lt : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|a l IH]; intros n i d Hi; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma keyL_firstn : forall D n x, 1 <= x <= Z.of_nat n -> keyL (firstn n D) x = keyL D x.
Proof. intros D n x Hx. unfold keyL. apply nth_firstn_lt. lia. Qed.

Lemma firstn_firstn_le : forall {A} (l : list A) a b, (a <= b)%nat -> firstn a (firstn b l) = firstn a l.
Proof. intros. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma linkL_firstn : forall D n x, 1 <= x <= Z.of_nat n -> linkL (firstn n D) x = linkL D x.
Proof. intros D n x Hx. unfold linkL. rewrite keyL_firstn, firstn_firstn_le by lia. reflexivity. Qed.

Lemma chainL_ok : forall n D b, (length D <= n)%nat -> chain_ok (linkL D) (chainL D b 1).
Proof.
  induction n as [|n IH]; intros D b Hlen.
  - destruct D; [exact I| cbn in Hlen; lia].
  - destruct (chainL D b 1) as [|s rest] eqn:E; [exact I|].
    destruct (chainL_cons_inv _ _ _ _ _ E) as [R B]. cbn [chain_ok]. split.
    + (* [comment removed for export] *)
      unfold linkL, headL. assert (Hb : bkt (keyL D s) = b).
      { unfold keyL. apply (chainL_bkt D b 1). rewrite E. left; reflexivity. }
      rewrite Hb, <- R. reflexivity.
    + rewrite R. apply chain_ok_ext with (f := linkL (firstn (Z.to_nat (s - 1)) D)).
      * apply IH. rewrite firstn_length. lia.
      * intros x Hx. symmetry. apply linkL_firstn. pose proof (chainL_bounds _ _ _ _ Hx) as HB. rewrite firstn_length in HB. lia.
Qed.

Lemma chainL_range : forall D b x, In x (chainL D b 1) -> 1 <= x <= Z.of_nat (length D).
Proof. intros D b x Hx. pose proof (chainL_bounds _ _ _ _ Hx). lia. Qed.

(* [comment removed for export] *)
Lemma cfind_spec : forall hsh h c,
  (cfind hsh h c = 0 /\ forall x, In x c -> hsh x <> h) \/ (In (cfind hsh h c) c /\ hsh (cfind hsh h c) = h).
Proof.
  intros hsh h c. induction c as [|s c IH]; cbn; [left; tauto|].
  destruct (Z.eqb_spec (hsh s) h) as [E|NE].
  - right. tauto.
  - destruct IH as [[Z0 NF]|[IN HH]]; [left|right]; [split; [exact Z0|]| tauto].
    intros x [<-|Hx]; [exact NE| apply NF; exact Hx].
Qed.

Lemma depot_findC_spec : forall D h i,
  match depot_findC D h i with
  | Some j => i <= j < i + Z.of_nat (length D) /\ depot_hashC (nth (Z.to_nat (j - i)) D []) = h
  | None => forall j, (j < length D)%nat -> depot_hashC (nth j D []) <> h
  end.
Proof.
  induction D as [|d D IH]; intros h i; cbn [depot_findC length].
  - intros j Hj. lia.
  - destruct (Z.eqb_spec (depot_hashC d) h) as [E|NE].
    + rewrite Z.sub_diag. cbn. split; [lia| exact E].
    + specialize (IH h (i + 1)). destruct (depot_findC D h (i + 1)) as [j|].
      * destruct IH as [B Hh]. split; [lia|]. replace (Z.to_nat (j - i)) with (S (Z.to_nat (j - (i + 1)))) by lia. exact Hh.
      * intros [|j] Hj; cbn [nth]; [exact NE| apply IH; lia].
Qed.

Lemma NoDup_map_nth : forall {A B} (f : A -> B) (l : list A) d i j,
  NoDup (map f l) -> (i < length l)%nat -> (j < length l)%nat -> f (nth i l d) = f (nth j l d) -> i = j.
Proof.
  intros A B f l d. induction l as [|a l IH]; intros i j ND Hi Hj E; cbn [length] in *; [lia|].
  inversion ND as [|x l' NI ND']; subst.
  destruct i as [|i], j as [|j]; cbn [nth] in E; [reflexivity| exfalso | exfalso | f_equal; apply IH; auto; lia].
  - apply NI. rewrite E. apply in_map_iff. exists (nth j l d). split; [reflexivity| apply nth_In; lia].
  - apply NI. rewrite <- E. apply in_map_iff. exists (nth i l d). split; [reflexivity| apply nth_In; lia].
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma cfind_putC : forall D k h, NoDup (map depot_hashC D) -> h = depot_hashC k ->
  (cfind (hshL D) h (chainL D (h mod 2^20) 1) = 0 -> depot_findC D h 1 = None) /\
  (cfind (hshL D) h (chainL D (h mod 2^20) 1) <> 0 -> depot_findC D h 1 = Some (cfind (hshL D) h (chainL D (h mod 2^20) 1))).
Proof.
  intros D k h ND Hk.
  pose proof (depot_findC_spec D h 1) as FS.
  destruct (cfind_spec (hshL D) h (chainL D (h mod 2^20) 1)) as [[R0 NF]|[IN HH]].
  - split; [|intros; congruence]. intros _.
    destruct (depot_findC D h 1) as [j|]; [exfalso|reflexivity]. destruct FS as [B Hh].
    apply (NF j); [| unfold hshL, keyL; exact Hh].
    replace j with (1 + Z.of_nat (Z.to_nat (j - 1))) at 1 by lia. apply chainL_complete; [lia|].
    unfold bkt. rewrite Hh. reflexivity.
  - set (c := cfind _ _ _) in *. clearbody c. pose proof (chainL_range _ _ _ IN) as CR.
    split; [intros; lia|]. intros _.
    destruct (depot_findC D h 1) as [j|].
    + destruct FS as [B Hh]. f_equal.
      assert (LJ : (Z.to_nat (j - 1) < length D)%nat) by (try (generalize alloc_ceiling_val); clear -B; try pose proof alloc_ceiling_val; lia).
      assert (LC : (Z.to_nat (c - 1) < length D)%nat) by (try (generalize alloc_ceiling_val); clear -CR; try pose proof alloc_ceiling_val; lia).
      assert (E : Z.to_nat (j - 1) = Z.to_nat (c - 1)).
      { apply (NoDup_map_nth depot_hashC D []); [exact ND| exact LJ| exact LC|].
        rewrite Hh. unfold hshL, keyL in HH. rewrite HH. reflexivity. }
      try (generalize alloc_ceiling_val); clear -E B CR; try pose proof alloc_ceiling_val. lia.
    + exfalso. apply (FS (Z.to_nat (c - 1))); [try (generalize alloc_ceiling_val); clear -CR; try pose proof alloc_ceiling_val; lia|]. unfold hshL, keyL in HH. exact HH.
Qed.

End CEIL.

(* [comment removed for export] *)
Lemma headL_snoc : forall D k b, headL (D ++ [k]) b = if Z.eqb (bkt k) b then Z.of_nat (length D) + 1 else headL D b.
Proof. intros. unfold headL. rewrite chainL_snoc. destruct (Z.eqb (bkt k) b); cbn; [lia|reflexivity]. Qed.

Lemma keyL_snoc_old : forall D k i, 1 <= i <= Z.of_nat (length D) -> keyL (D ++ [k]) i = keyL D i.
Proof. intros. unfold keyL. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma keyL_snoc_new : forall D k, keyL (D ++ [k]) (Z.of_nat (length D) + 1) = k.
Proof. intros. unfold keyL. rewrite app_nth2 by lia. replace (_ - _)%nat with 0%nat by lia. reflexivity. Qed.

Lemma linkL_snoc_old : forall D k i, 1 <= i <= Z.of_nat (length D) -> linkL (D ++ [k]) i = linkL D i.
Proof.
  intros D k i Hi. unfold linkL. rewrite keyL_snoc_old by lia. rewrite firstn_app.
  replace (Z.to_nat (i - 1) - length D)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma linkL_snoc_new : forall D k, linkL (D ++ [k]) (Z.of_nat (length D) + 1) = headL D (bkt k).
Proof.
  intros D k. unfold linkL. rewrite keyL_snoc_new. rewrite firstn_app, firstn_all2 by lia.
  replace (_ - _)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma depot_off_app1 : forall D k i, (i <= length D)%nat -> depot_off (D ++ [k]) i = depot_off D i.
Proof. intros. unfold depot_off. rewrite firstn_app. replace (i - length D)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity. Qed.
Lemma sidL_snoc_old : forall D k i, 1 <= i <= Z.of_nat (length D) -> sidL (D ++ [k]) i = sidL D i.
Proof. intros. unfold sidL. rewrite depot_off_app1 by lia. reflexivity. Qed.
Lemma sidL_snoc_new : forall D k, sidL (D ++ [k]) (Z.of_nat (length D) + 1) = depot_total D + 1.
Proof. intros. unfold sidL, depot_total. replace (Z.to_nat _) with (length D) by lia. rewrite depot_off_app1 by lia. reflexivity. Qed.

Lemma depot_off_nonneg : forall D i, 0 <= depot_off D i.
Proof. intros D i. unfold depot_off. induction (firstn i D); cbn; lia. Qed.
Lemma depot_total_snoc : forall D k, depot_total (D ++ [k]) = depot_total D + 1 + Z.of_nat (length k).
Proof.
  intros D k. unfold depot_total, depot_off. rewrite !firstn_all.
  rewrite fold_right_app. cbn [fold_right].
  induction D as [|d D IH]; cbn [fold_right app]; [lia|]. rewrite IH. lia.
Qed.
End ARt_wg1.


Module ARt_fts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_dmf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From stdpp Require Import bitvector.definitions.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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

(* [comment removed for export] *)
Ltac scstep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i; exec_cbv; cbv beta iota zeta delta [amo_aligned amo_bytes]; simp_is_x0; simp_regs; fold_lit_ux; fold_xlits;
          eval_lit_tests; solve_amo_align; rewrite ?Z.eqb_refl; cbv beta iota; vnorm_for i;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_for i; try fix_lit_store; fix_le1_lit; mem_after_store_opt; post_step i; fold_xlits ]
      end end
  end.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma lock_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p v lo : Z) (Q : machine_state -> Prop),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
  a0 = wz p -> 0 <= v < 2^31 -> p mod 4 = 0 -> 0 <= p -> p + 4 <= 0x700000 ->
  rw_cells rsegs m p [C4 (wz v)] ->
  bv_unsigned ra mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' wl : word) m',
      rw_cells rsegs m' p [C4 wl] ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp); (p, p + 4)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
      stk rsegs m' lo (bv_unsigned sp) ->
      evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz v) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz 0x7956c) fc None m (seg_rom rsegs)).
Proof.
  intros until Q. intros MI ST LOLE CEIL A0 VR PAL P0 PHI TAB RA K. pose proof alloc_ceiling_val as CV.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (p, p + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  subst a0.
  carve_frame 48%nat ST.
  do 10 amz.
  amz. rewrite sx32_small by lia.
  amz. br_taken.
  amz. amz. rewrite sx32_small by lia.
  amz. replace (negb (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 v))) with false by (unfold bv_eqb; rewrite Z.eqb_refl; reflexivity). cbv iota.
  scstep; zsimp. amz. if_false.
  amz. replace (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 v)) with true by (unfold bv_eqb; rewrite Z.eqb_refl; reflexivity). cbv iota.
  do 7 amz.
  release_frame FR ST (bv_unsigned sp).
  eapply K; [exact TAB | | exact WM | exact MI | exact ST].
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact MU.
Qed.

End CEIL.
End ARt_fts.


Module ARt_51v.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Lemma firstn_S_nth_error : forall {A} (l : list A) i x, nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof.
  intros A l. induction l as [|a l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn. f_equal. apply IH. exact H.
Qed.

Section M.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop).
  Variables (dst src n : Z) (bs : list byte).
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis N1 : 1 <= n.
  Hypothesis DHI : dst + n < 2^64.
  Hypothesis SHI : src + n < 2^64.
  Hypothesis D0 : 0 <= dst.
  Hypothesis S0 : 0 <= src.
  Hypothesis DISJ : dst + n <= src \/ src + n <= dst.

  (* [comment removed for export] *)
  #[using="DISJ S0 D0 SHI DHI N1 LEN"] Lemma imemcpy_loop : forall k i m (ds : list byte) (a4 : word),
    Z.of_nat k = n - i -> 0 <= i < n ->
    mem_inv rsegs m -> u8ro rsegs m src bs -> u8arr rsegs m dst ds -> length ds = length bs ->
    firstn (Z.to_nat i) ds = firstn (Z.to_nat i) bs ->
    (forall m' (a1' a3' a4' : word), mem_inv rsegs m' -> u8arr rsegs m' dst bs ->
        munch [(dst, dst + n)] m m' -> wmono rsegs m m' ->
        evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1' (wz (dst + n)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz (src + i)) (wz (dst + n)) (wz (dst + i)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x6a220) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i m ds a4 HK HI MI SRC DA LD PRE K; [lia|].
    pose proof (munch_refl [(dst, dst + n)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
    pose proof (u8ro_read rsegs m src bs i b (Z_to_bv 64 (src + i)) SRC NB ltac:(lia) ltac:(unfold wa; reflexivity)) as RD.
    zstep. cbv beta. change (Z_to_bv 64 (bv_unsigned b)) with (zxb b).
    pose proof (u8arr_store_ok rsegs m dst ds i (Z_to_bv 64 (dst + i)) DA ltac:(rewrite LD; lia) ltac:(unfold wa; reflexivity)) as SOK.
    zstep. rewrite le1_zxb.
    change (write_to_mem m (Z_to_bv 64 (dst + i)) [b]) with (write_to_mem m (wa (dst + i)) [b]).
    pose proof (u8arr_write rsegs m dst ds i b DA ltac:(rewrite LD; lia)) as DA2. clear DA.
    store_done.
    zstep. zstep. zstep.
    assert (LD2 : length (upd ds (Z.to_nat i) b) = length bs) by (rewrite upd_length; exact LD).
    assert (PRE2 : firstn (Z.to_nat (i + 1)) (upd ds (Z.to_nat i) b) = firstn (Z.to_nat (i + 1)) bs).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (firstn_S_nth_error _ _ b) by (apply nth_error_upd_same; rewrite LD; lia).
      rewrite (firstn_S_nth_error bs _ b NB). f_equal.
      rewrite upd_firstn_skipn by (rewrite LD; lia). rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length.
      replace (Z.to_nat i - _)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact PRE. }
    if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
    - (* [comment removed for export] *)
      replace (dst + i + 1) with (dst + (i + 1)) by lia. replace (src + i + 1) with (src + (i + 1)) by lia.
      apply (IH (i + 1) _ (upd ds (Z.to_nat i) b)); [lia | lia | exact MI | exact SRC | exact DA2 | exact LD2 | exact PRE2 |].
      intros m' a1' a3' a4' MI' DA' MU' WM'. apply K; [exact MI' | exact DA' | eapply munch_trans; [exact MU | exact MU'] | eapply wmono_trans; [exact WM | exact WM']].
    - (* [comment removed for export] *)
      zstep. apply K; [exact MI | | exact MU | exact WM].
      replace bs with (upd ds (Z.to_nat i) b); [exact DA2|].
      rewrite <- (firstn_all (upd _ _ _)), <- (firstn_all bs), LD2.
      replace (length bs) with (Z.to_nat (i + 1)) by lia. exact PRE2.
  Qed.

  (* [comment removed for export] *)
  #[using="DISJ S0 D0 SHI DHI N1 LEN"] Lemma imemcpy_spec : forall m (junk : list byte) (a3 a4 : word),
    mem_inv rsegs m -> u8ro rsegs m src bs -> u8arr rsegs m dst junk -> length junk = length bs ->
    (forall m' (a1' a3' a4' : word), mem_inv rsegs m' -> u8arr rsegs m' dst bs ->
        munch [(dst, dst + n)] m m' -> wmono rsegs m m' ->
        evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1' (wz (dst + n)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz src) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x6a214) fc None m (seg_rom rsegs)).
  Proof.
    intros m junk a3 a4 MI SRC DA LD K.
    zstep. br_not_taken. zstep. zstep.
    pose proof (fun a4 => imemcpy_loop (Z.to_nat n) 0 m junk a4 ltac:(lia) ltac:(lia) MI SRC DA LD eq_refl K) as L.
    rewrite !Z.add_0_r in L. apply L.
  Qed.
End M.
End ARt_51v.


Module ARt_pkh.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_dmf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_51v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From stdpp Require Import bitvector.definitions.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)

Definition SS : Z := 0x187288.   (* [comment removed for export] *)
Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_toA pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA end).

Lemma shl44_shr41 : forall a, 0 <= a < 2^20 -> Z.shiftr ((Z.shiftl a 44) mod 18446744073709551616) 41 = 8 * a.
Proof.
  intros a Ha. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change 18446744073709551616 with (2^20 * 2^44); nia).
  change (2^44) with (8 * 2^41). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma amo_add_wz : forall a b, amo_val AMO_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. cbn [amo_val]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma rw_cells_split2 : forall m A c1 c2,
  rw_cells rsegs m A [c1; c2] -> rw_cells rsegs m A [c1] /\ rw_cells rsegs m (A + Z.of_nat (csize c1)) [c2].
Proof.
  intros m A c1 c2 [[WF BA] WR]. cbn [cells_wf] in WF. destruct WF as (W1 & W2 & _).
  cbn [cells_bytes] in BA. rewrite app_nil_r in BA. apply bytes_at_app in BA. destruct BA as [B1 B2].
  rewrite (cbytes_length c1 W1) in B2. cbn [cells_size] in WR. rewrite Nat.add_0_r, Nat2Z.inj_add in WR.
  destruct WR as (R0 & R1 & R2).
  split; (split; [split; cbn [cells_wf cells_bytes]; [tauto| rewrite app_nil_r; assumption] |]);
    cbn [cells_size]; rewrite Nat.add_0_r; (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply R2. lia.
  - replace (A + Z.of_nat (csize c1) + i) with (A + (Z.of_nat (csize c1) + i)) by lia. apply R2. lia.
Qed.
Lemma rw_cells_join2 : forall m A c1 c2,
  rw_cells rsegs m A [c1] -> rw_cells rsegs m (A + Z.of_nat (csize c1)) [c2] -> rw_cells rsegs m A [c1; c2].
Proof.
  intros m A c1 c2 [[W1 B1] R1] [[W2 B2] R2]. cbn [cells_wf] in W1, W2. cbn [cells_bytes] in B1, B2. rewrite app_nil_r in B1, B2.
  cbn [cells_size] in R1, R2. rewrite Nat.add_0_r in R1, R2.
  split; [split|].
  - cbn [cells_wf]. tauto.
  - cbn [cells_bytes]. rewrite app_nil_r. apply bytes_at_app. rewrite (cbytes_length c1 (proj1 W1)). tauto.
  - cbn [cells_size]. rewrite Nat.add_0_r, Nat2Z.inj_add. destruct R1 as (R10 & R11 & R12), R2 as (R20 & R21 & R22).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (csize c1))); [apply R12; lia|].
    replace (A + i) with (A + Z.of_nat (csize c1) + (i - Z.of_nat (csize c1))) by lia. apply R22. lia.
Qed.

Lemma blk_off_zero : forall T, 0 <= T < 2^20 -> Z.land (Z.shiftr T 16) 18446744073709551600 = 0.
Proof.
  intros T HT. rewrite Z.shiftr_div_pow2 by lia.
  assert (HB : 0 <= T / 2^16 < 16) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (q := T / 2^16) in *. clearbody q.
  assert (E : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15) by lia.
  destruct E as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]]]]; reflexivity.
Qed.

Lemma amo_w_bytes : forall a b, 0 <= a -> 0 <= b -> a + b < 2^32 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 a)))) (low32 (Z_to_bv 64 b))))
  = le4 (Z_to_bv 64 (a + b)).
Proof.
  intros a b Ha Hb Hab. unfold le4 at 2. f_equal. cbn [amo_val]. unfold low32.
  rewrite bv_add_unsigned, !bv_extract_0_unsigned, le_bytes_to_word_le4, !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  rewrite (Z.mod_small a (2^32)) by lia. rewrite (Z.mod_small a (2^32)) by lia. rewrite (Z.mod_small b (2^32)) by lia.
  rewrite (Z.mod_small (a + b) (2^32)) by lia. reflexivity.
Qed.

Lemma land_pow2_small : forall x n, 0 <= n -> 0 <= x < 2^n -> Z.land x (2^n) = 0.
Proof.
  intros x n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  rewrite (Z.pow2_bits_eqb n i) by lia.
  destruct (Z.eqb_spec n i) as [<-|NE]; [| apply Bool.andb_false_r].
  rewrite Bool.andb_true_r. apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma lxor_full_flag : forall x, 0 <= x < 2^20 -> Z.lxor x 1048576 = x + 1048576.
Proof. intros x Hx. symmetry. apply Z.add_nocarry_lxor. apply (land_pow2_small x 20); lia. Qed.

Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma le8_small_split : forall v, 0 <= v < 2^32 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. rewrite <- store_bytes_8. unfold le4. rewrite !unsigned_lit by lia.
  change (width_bytes 64) with (4 + 4)%nat. rewrite Z_to_le_bytes_add. f_equal.
  change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.
Lemma rw_cells_C8_44 : forall m A v rest, rw_cells rsegs m A (C8 (Z_to_bv 64 v) :: rest) -> 0 <= v < 2^32 ->
  rw_cells rsegs m A (C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: rest).
Proof.
  intros m A v rest [[WF BA] WR] Hv. cbn [cells_wf] in WF. split; [split|].
  - cbn [cells_wf]. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite le8_small_split in BA by lia. rewrite <- app_assoc in BA. exact BA.
  - cbn [cells_size csize] in *. exact WR.
Qed.

Section St.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop).
  Variables (nd ap tr h T f0 lo : Z) (k : list Z).
  Let n := Z.of_nat (length k).

  Lemma node_store_spec : forall (ra s0 t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem)
      (j1 : list byte) (j2 : list byte) (j3 : list byte) (j4 j5 j6 j7 : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    bv_unsigned sp <= 2^47 ->
    (1 <= length k <= 255)%nat -> Forall (fun w => 0 <= w < 2^64) k -> 0 <= h < 2^64 ->
    0 <= T -> T + 1 + n < 2^20 ->
    aobj nd 16 -> nd + 16 <= alloc_ceiling ->             (* [comment removed for export] *)
    aobj f0 0x800000 -> f0 + 0x800000 <= alloc_ceiling ->
    bv_unsigned sp <= ap -> ap + 16 <= 2^47 -> bv_unsigned sp <= tr -> tr + 8 * n <= 2^47 ->
    (* [comment removed for export] *)
    nd + 16 <= f0 + 8 * T \/ f0 + 8 * (T + 1 + n) <= nd ->
    rw_cells rsegs m ap [C8 (wz tr); C4 (wz n); C4 (wz 0)] ->
    rw_cells rsegs m nd [CB 8 j1; CB 4 j2; CB 4 j3] ->
    rw_cells rsegs m SS [C8 (wz T); CB 8 j4; C8 (wz f0); C4 (wz T); CB 4 j5] ->
    rw_cells rsegs m (f0 + 8 * T) [CB 8 j6; CB (Z.to_nat (8 * n)) j7] ->
    u8ro rsegs m tr (u64s (map (Z_to_bv 64) k)) ->
    bv_unsigned ra mod 2 = 0 ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
        mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        rw_cells rsegs m' ap [C8 (wz tr); C4 (wz n); C4 (wz 0)] ->
        rw_cells rsegs m' nd [C8 (wz h); CB 4 j2; C4 (wz (T + 1))] ->
        rw_cells rsegs m' SS [C8 (wz (T + 1 + n)); CB 8 j4; C8 (wz f0); C4 (wz (T + 1 + n)); CB 4 j5] ->
        rw_cells rsegs m' (f0 + 8 * T) [C8 (wz n); CB (Z.to_nat (8 * n)) (u64s (map (Z_to_bv 64) k))] ->
        u8ro rsegs m' tr (u64s (map (Z_to_bv 64) k)) ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (nd, nd + 16); (SS, SS + 36); (f0 + 8 * T, f0 + 8 * (T + 1 + n))] m m' ->
        wmono rsegs m m' ->
        evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (T + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz nd) a1 (wz ap) (wz h) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x78af0) fc None m (seg_rom rsegs)).
  Proof.
    intros until j7. intros MI ST LOLE CEIL SPHI LK FK HR T0 TB ND0 ND1 F00 F01 AP0 AP1 TR0 TR1 SEP ARGS NODE SSC FRM TRC RA K.
    pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, SS in *. aobj_lin_all.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (nd, nd + 16); (1602184, 1602184 + 36); (f0 + 8 * T, f0 + 8 * (T + 1 + n))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (N1 : 1 <= n <= 255) by (subst n; lia).
    remember (f0 + 8 * T) as fp eqn:FP.
    carve_frame 32%nat ST.
    run_toA 0x78b18. amz. (* [comment removed for export] *)
    rename FR into FR1. carve_frame 64%nat ST.
    run_toA 0x76850. rewrite !sx32_small by lia. rewrite ?Z.lor_0_r. br_auto.
    run_toA 0x76850. if_cases KB; zify_cond KB; [ | amz; replace (Z_to_bv 64 255) with (Z_to_bv 64 n) by (f_equal; lia) ].
    all: run_toA 0x76850. all: amz. (* [comment removed for export] *)
    all: rename FR into FR2; carve_frame 16%nat ST.
    all: run_toA 0x76914.
    all: amz. (* [comment removed for export] *)
    all: amz; amz; rewrite (Z.shiftr_div_pow2 T 20), (Z.div_small T (2^20)) by lia.
    all: amz; amz; rewrite (Z.shiftr_div_pow2 (n + T) 20), (Z.div_small (n + T) (2^20)) by lia.
    all: amz; [if_false|..]. (* [comment removed for export] *)
    all: amz; rewrite (Z.shiftr_div_pow2 T 32), (Z.div_small T (2^32)) by lia.
    all: amz; [if_true|..]. (* [comment removed for export] *)
    all: amz; amz; amz; amz. (* [comment removed for export] *)
    all: amz; br_auto. (* [comment removed for export] *)
    all: amz; amz; rewrite shl44_shr41 by lia.
    all: amz; rewrite <- FP.
    all: do 4 amz. (* [comment removed for export] *)
    all: release_frame FR ST (bv_unsigned sp + -96).
    all: amz; [br_auto|..]. (* [comment removed for export] *)
    all: amz; amz; amz; rewrite (Z.lor_0_l n).
    all: amz. (* [comment removed for export] *)
    all: amz; amz; rewrite (Z.shiftl_mul_pow2 n 3) by lia; replace (n * 2 ^ 3) with (8 * n) by lia.
    all: amz. (* [comment removed for export] *)
    all: apply rw_cells_split2 in FRM as [FRH FRB]; change (Z.of_nat (csize (C8 (Z_to_bv 64 n)))) with 8 in FRB.
    all: assert (LD : length j7 = Z.to_nat (8 * n)) by (destruct FRB as [[[W _] _] _]; exact W).
    all: pose proof (u8arr_of_rw_cells _ _ _ _ _ FRB) as DA; clear FRB.
    all: eapply imemcpy_spec with (dst := fp + 8) (src := tr) (n := 8 * n) (bs := u64s (map (Z_to_bv 64) k));
      [ rewrite u64s_length, map_length; lia | lia | lia | lia | lia | lia | lia | exact MI | exact TRC | exact DA | rewrite LD, u64s_length, map_length; lia |].
    all: clear DA; intros m' a1' a3' a4' MI' DA' MU' WM'.
    all: replace (ret_pc (Z_to_bv 64 485492)) with (Z_to_bv 64 485492) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: transport_after_call rsegs m1 m' MU' WM'; clear MU' WM' MI.
    all: pose proof (rw_cells_of_u8arr _ _ _ _ DA') as FRB; clear DA'; rewrite u64s_length, map_length in FRB.
    all: amz; amz; amz; rewrite blk_off_zero by lia.
    all: amz; amz. (* [comment removed for export] *)
    all: amz; rewrite (amo_w_bytes T (n + 1)) by lia; mem_after_store; rewrite sx32_small by lia. (* [comment removed for export] *)
    all: rewrite amo_add_wz in SSC.
    all: do 4 amz; rewrite (Z.mod_small T 4294967296) by lia.
    all: amz; amz. (* [comment removed for export] *)
    all: replace (n + 1 + T) with (T + (n + 1)) by lia; rewrite lxor_full_flag by lia.
    all: apply rw_cells_C8_44 in FR2; [|lia].
    all: amz; rewrite sx32_small by lia. (* [comment removed for export] *)
    all: amz; amz; amz; amz; rewrite (swrap32_small (T + 1)) by lia.
    all: replace (Z.b2z (T + (n + 1) + 1048576 <? 1)) with 0 in FR1 by (symmetry; apply b2z_ltb_false; lia).
    all: change (0 + 0) with 0 in FR1.
    all: do 9 amz. (* [comment removed for export] *)
    all: release_frame FR2 ST (bv_unsigned sp + -32).
    all: amz; amz. (* [comment removed for export] *)
    all: amz; [if_false|..]. (* [comment removed for export] *)
    all: do 4 amz. (* [comment removed for export] *)
    all: release_frame FR1 ST (bv_unsigned sp).
    all: apply rw_cells_join2 with (c1 := C8 (Z_to_bv 64 n)) in FRB; [| exact FRH].
    all: replace (T + (n + 1)) with (T + 1 + n) in SSC by lia.
    all: replace (8 * length k)%nat with (Z.to_nat (8 * n)) in FRB by (subst n; lia).
    all: eapply K; [exact MI' | exact ST | exact ARGS | exact NODE | exact SSC | exact FRB | exact TRC | | exact WM].
    all: subst fp; replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia;
         replace (f0 + 8 * T + 8 + 8 * n) with (f0 + 8 * (T + 1 + n)) in MU by lia; exact MU.
  Qed.
End St.
End ARt_pkh.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_yhn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_dmf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_pkh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From stdpp Require Import bitvector.definitions.

Module ARt_a0k.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Ltac gen_regs_set :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 ?e)] =>
        tryif is_var e then fail else tryif is_Zlit e then fail else
          (let x := fresh "x" in set (x := e)) end
  end.
Theorem classid_blk2_ok : classid_blk2_stmt.
Proof.
  unfold classid_blk2_stmt. intros until Q. intros HS H8 K. unfold classid_blk2_entry, classid_blk2_exit in *.
  do 55 (step; gen_regs_set).
  match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    match R with context [Some (Z_to_bv 64 ?e)] =>
      constr_eq e x34; replace (Z_to_bv 64 x34) with (Z_to_bv 64 (size_class s)); [apply K|] end end.
  f_equal. rewrite <- (classid_mach_ok s HS H8).
  subst x34 x33 x32 x31 x30 x29 x28 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x17 x16 x15 x14 x13 x12 x11 x10
        x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 x.
  reflexivity.
Qed.
End ARt_a0k.

Module ARt_m2s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
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
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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

Definition m2s_fs_entry : Z := 0x42cdc.
Definition m2s_al_entry : Z := 0x586c4.
Definition m2s_po_entry : Z := 0x5a290.

Definition m2s_consts (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa9190 [C8 (wz 0xb53b8)] /\ ro_cells rsegs m 0xb53b8 [C8 (wz kShadowOffset)]
  /\ ro_cells rsegs m 0xa9198 [C8 (wz 0xb60a8)] /\ ro_cells rsegs m 0xa91a0 [C8 (wz 0xb60b0)] /\ ro_cells rsegs m 0xa91a8 [C8 (wz 0xb60a0)]
  /\ ro_cells rsegs m 0xb60a0 [C8 (wz kHighMemEnd); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition m2s_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (2147450880 + Z.shiftr p 3)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Definition m2s_stmt (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z),
  mem_inv rsegs m -> m2s_consts m -> a0 = wz p -> m2s_in p -> bv_unsigned ra mod 2 = 0 ->
  evt rsegs (m2s_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom rsegs)).

Section CEIL.
Context {Clg : Ceiling}.

Lemma poison_consts_m2s : forall m, poison_consts m -> m2s_consts m.
Proof. intros m PC. (first [ dand10 PC as _ _ _ P4 P5 P6 P7 P8 P9 _ | destruct PC as (_ & _ & _ & P4 & P5 & P6 & P7 & P8 & P9 & _) ]). unfold m2s_consts. tauto. Qed.

End CEIL.

(* [comment removed for export] *)
Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstep1 := first [ zstep; fold_xlits | if_false | if_true | br_auto ].
Ltac run_to_a pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep1 end).

(* [comment removed for export] *)
Ltac m2s_walk join :=
  intros until p; intros MI MC A0 HP RA;
  let Cgotsh := fresh "Cgotsh" in let Cshoff := fresh "Cshoff" in let Cgotmid := fresh "Cgotmid" in
  let Cgotmide := fresh "Cgotmide" in let Cgothi := fresh "Cgothi" in let Chivars := fresh "Chivars" in
  (first [ dand6 MC as Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars | destruct MC as (Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars) ]);
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => pose proof (munch_refl [] m) as MU; pose proof (wmono_refl rsegs m) as WM end;
  unfold m2s_fs_entry, m2s_al_entry, m2s_po_entry, m2s_in, kShadowOffset, kHighMemEnd, kHighMemBeg, kLowMemEnd in *; subst;
  destruct HP as [HP|HP];
  [ run_to_a join | run_to_a join ];
  [ zstep; zstep; zstep | zstep; zstep; zstep ];
  [ finish | finish ].

Theorem m2s_fs_ok : m2s_stmt m2s_fs_entry.
Proof. unfold m2s_stmt. m2s_walk 0x42d3c. Qed.

Theorem m2s_al_ok : m2s_stmt m2s_al_entry.
Proof. unfold m2s_stmt. m2s_walk 0x58724. Qed.

(* [comment removed for export] *)
End ARt_m2s.


Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)

Definition TAB : Z := 0x197298.
Definition NUNIQ : Z := 0x597298.
Definition MAP1 : Z := 0x5972a8.

(* [comment removed for export] *)
Definition byte_at (m : mem) (a : Z) : byte := match m (wz a) with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint rdbytes (m : mem) (a : Z) (n : nat) : list byte :=
  match n with O => [] | S n' => byte_at m a :: rdbytes m (a + 1) n' end.
Lemma rdbytes_length : forall m n a, length (rdbytes m a n) = n.
Proof. intros m n. induction n; intros a; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
Lemma rdbytes_nth : forall m n a i, (i < n)%nat -> nth_error (rdbytes m a n) i = Some (byte_at m (a + Z.of_nat i)).
Proof.
  intros m n. induction n as [|n IH]; intros a i Hi; [lia|].
  destruct i as [|i]; cbn [rdbytes nth_error]. { rewrite Z.add_0_r. reflexivity. }
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.
Lemma mapped_rw_cells : forall m a n, mapped m a n -> 0 <= a -> 0 <= n -> a + n <= 2^64 ->
  rw_cells rsegs m a [CB (Z.to_nat n) (rdbytes m a (Z.to_nat n))].
Proof.
  intros m a n HM Ha Hn0 Hn.
  assert (BA : bytes_at rsegs m a (rdbytes m a (Z.to_nat n))).
  { split; [lia|]. split; [rewrite rdbytes_length; lia|].
    intros i Hi. rewrite rdbytes_length in Hi. rewrite rdbytes_nth by exact Hi.
    unfold mrd, wa, byte_at. destruct (m (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
    exfalso. apply (HM (Z.of_nat i)); [lia| exact E]. }
  split; [split|].
  - cbn. rewrite rdbytes_length. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|].
    intros i Hi E. apply (HM i Hi). unfold wview, wa in E. destruct (m (Z_to_bv 64 (a + i))); [discriminate| reflexivity].
Qed.

(* [comment removed for export] *)
Definition depot_repL (L : alayout) (segs : list Segment) (D : list (list Z)) (n0 f0 : Z) (m : mem) : Prop :=
  (forall b, 0 <= b < 2^20 -> rw_cells segs m (al_theDepot L + 4 * b) [C4 (wz (headL D b))]) /\
  rw_cells segs m (al_depot_n_uniq_ids L) [C4 (wz (Z.of_nat (length D)))] /\
  ro_cells segs m (al_depot_nodes_map1 L) [C8 (wz n0)] /\
  (forall i, 1 <= i <= Z.of_nat (length D) ->
     rw_cells segs m (n0 + 16 * i) [C8 (wz (hshL D i)); C4 (wz (linkL D i)); C4 (wz (sidL D i))]) /\
  (exists j4 j5, rw_cells segs m (al_stackStore L) [C8 (wz (depot_total D)); CB 8 j4; C8 (wz f0); C4 (wz (depot_total D)); CB 4 j5]) /\
  mapped m n0 kDepotNodesBlock /\ mapped m f0 kStackStoreBlockBytes /\
  n0 mod 16 = 0 /\ f0 mod 8 = 0 /\ (n0 + kDepotNodesBlock <= f0 \/ f0 + kStackStoreBlockBytes <= n0) /\
  0 <= depot_total D /\
  (* [comment removed for export] *)
  (al_stackStore L + 36 <= al_theDepot L /\ al_theDepot L + 4 * 2^20 <= al_depot_n_uniq_ids L /\
   al_depot_n_uniq_ids L + 4 <= al_depot_nodes_map1 L /\ 16 * (Z.of_nat (length D) + 1) <= kDepotNodesBlock).

(* [comment removed for export] *)
Lemma headL_range : forall D b, headL D b = 0 \/ 1 <= headL D b <= Z.of_nat (length D).
Proof.
  intros D b. unfold headL. destruct (chainL D b 1) as [|s rest] eqn:E; [left; reflexivity| right]. cbn.
  apply (chainL_range D b). rewrite E. left; reflexivity.
Qed.
Lemma fold_frames_nonneg : forall (l : list (list Z)), 0 <= fold_right (fun k acc => 1 + Z.of_nat (length k) + acc) 0 l.
Proof. induction l; cbn; lia. Qed.
Lemma depot_off_mono : forall D i, (i <= length D)%nat -> depot_off D i <= depot_total D.
Proof.
  intros D i Hi. unfold depot_total, depot_off. rewrite firstn_all.
  rewrite <- (firstn_skipn i D) at 2. rewrite fold_right_app.
  pose proof (fold_frames_nonneg (skipn i D)) as Ht.
  set (t := fold_right _ 0 (skipn i D)) in *. clearbody t.
  induction (firstn i D); cbn; lia.
Qed.
Lemma linkL_range : forall D i, 1 <= i <= Z.of_nat (length D) -> 0 <= linkL D i <= Z.of_nat (length D).
Proof.
  intros D i Hi. unfold linkL. destruct (headL_range (firstn (Z.to_nat (i - 1)) D) (bkt (keyL D i))) as [->|B]; [lia|].
  rewrite firstn_length in B. lia.
Qed.
Lemma sidL_range : forall D i, 1 <= i <= Z.of_nat (length D) -> 1 <= sidL D i <= depot_total D + 1.
Proof.
  intros D i Hi. unfold sidL. pose proof (depot_off_mono D (Z.to_nat (i - 1)) ltac:(lia)). pose proof (depot_off_nonneg D (Z.to_nat (i - 1))). lia.
Qed.

Lemma w_cells_wf : forall k, cells_wf (w_cells k).
Proof. induction k; cbn; [exact I|]. split; [exact I| exact IHk]. Qed.
Lemma w_cells_bytes : forall k, cells_bytes (w_cells k) = u64s (map (Z_to_bv 64) k).
Proof. induction k; cbn [w_cells cells_bytes map u64s cbytes]; [reflexivity|]. rewrite IHk. reflexivity. Qed.
Lemma w_cells_of_bytes : forall m tr k, bytes_at rsegs m tr (u64s (map (Z_to_bv 64) k)) -> ro_cells rsegs m tr (w_cells k).
Proof. intros m tr k BA. split; [apply w_cells_wf|]. rewrite w_cells_bytes. exact BA. Qed.
Lemma land_31_small : forall v, 0 <= v < 2^31 -> Z.land v 2147483647 = v.
Proof. intros v Hv. change 2147483647 with (Z.ones 31). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[WF BA] WR].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite (cells_bytes_length cs1 WF1) in BA2.
  rewrite cells_size_app, Nat2Z.inj_add in WR. (first [ dand3 WR as W0 W1 W2 | destruct WR as (W0 & W1 & W2) ]).
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply W2. lia.
Qed.
Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] R1] [[W2 B2] R2]. split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length cs1 W1). tauto.
  - rewrite cells_size_app, Nat2Z.inj_add. destruct R1 as (R10 & R11 & R12), R2 as (R20 & R21 & R22).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply R12; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply R22. lia.
Qed.
Lemma rw_cells_C8_44p : forall m A pre v rest, rw_cells rsegs m A (pre ++ C8 (Z_to_bv 64 v) :: rest) -> 0 <= v < 2^32 ->
  rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: rest).
Proof.
  intros m A pre v rest H Hv. apply rw_cells_app_split in H as [H1 H2]. apply rw_cells_app_join; [exact H1|].
  apply rw_cells_C8_44; assumption.
Qed.

Lemma amo_w_bytes_lit : forall a b, 0 <= a -> 0 <= b -> a + b < 2^32 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 a)))) (Z_to_bv 32 b)))
  = le4 (Z_to_bv 64 (a + b)).
Proof.
  intros a b Ha Hb Hab. unfold le4 at 2. f_equal. cbn [amo_val].
  rewrite bv_add_unsigned, bv_extract_0_unsigned, le_bytes_to_word_le4, (unsigned_lit a), (unsigned_lit (a + b)), Z_to_bv_unsigned by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  rewrite (Z.mod_small a (2^32)) by lia. rewrite (Z.mod_small a (2^32)) by lia. rewrite (Z.mod_small b (2^32)) by lia.
  rewrite (Z.mod_small (a + b) (2^32)) by lia. reflexivity.
Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma mapped_mono : forall m m' a n, mapped m a n -> wmono rsegs m m' -> aobj a n -> a + n <= alloc_ceiling -> mapped m' a n.   (* [comment removed for export] *)
Proof.
  intros m m' a n HM WM Ha Hn i Hi E. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold kHighMemBeg in Ha. aobj_lin_all.
  apply (WM (wz (a + i))).
  - unfold wview. destruct (m (Z_to_bv 64 (a + i))) eqn:E0; [discriminate|]. exfalso. exact (HM i Hi E0).
  - unfold wview. rewrite E.
    replace (find_segment rsegs (bv_unsigned (Z_to_bv 64 (a + i))) 1) with (@None Segment); [reflexivity|].
    symmetry. apply (asI_find_segment_outside (Z_to_bv 64 (a + i))).
    unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. rewrite unsigned_lit by lia. lia.
Qed.

Definition keep (P : Prop) : Prop := P.

Theorem depot_put_ok : depot_put_stmt depot_repL.
Proof.
  unfold depot_put_stmt. intros until lo. intros MI ST LOLE CEIL A0 A1 LK FK TRB TRLO TRHI REP ND LD TB N00 N01 F00 F01 RA.
  pose proof alloc_ceiling_val as CV.
  (first [ dand12 REP as RTAB RNU RMAP RNODES (j4 & j5 & RSS) NMAP FMAP N0A F0A NF TOT0 LAY | destruct REP as (RTAB & RNU & RMAP & RNODES & (j4 & j5 & RSS) & NMAP & FMAP & N0A & F0A & NF & TOT0 & LAY) ]).
  unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kStackStoreBlockFrames in *. aobj_lin_all.
  cbn [al_stackStore al_depot_nodes_map1 al_theDepot al_depot_n_uniq_ids AL_pasan] in *. unfold TAB, NUNIQ, MAP1, SS in *.
  set (n := Z.of_nat (length k)) in *.
  set (h := depot_hashC k). set (b := h mod 2^20).
  pose proof (depot_hashC_range k) as HR. fold h in HR.
  assert (BR : 0 <= b < 2^20) by (subst b; apply Z.mod_pos_bound; lia).
  set (N := Z.of_nat (length D)) in *.
  set (nd := n0 + 16 * (N + 1)). set (fp := f0 + 8 * depot_total D). set (tb := 1667736 + 4 * b).
  assert (TBA : tb mod 4 = 0).
  { replace tb with ((416934 + b) * 4) by (cbv delta [tb]; lia). apply Z_mod_mult. }
  (* [comment removed for export] *)
  pose proof (RTAB b BR) as TBK. fold tb in TBK.
  assert (RMAP0 : keep (ro_cells rsegs m 5862056 [C8 (wz n0)])) by exact RMAP.
  pose proof (munch_refl ((bv_unsigned sp - 512, bv_unsigned sp) :: (tb, tb + 4) :: (5862040, 5862044) :: (nd, nd + 16) :: (1602184, 1602184 + 36) :: (fp, fp + 8 * (1 + n)) :: nil) m) as MU.
  pose proof (munch_refl ((bv_unsigned sp - 512, bv_unsigned sp) :: nil) m) as MU0.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bytes_at_bound _ _ _ _ TRB) as TRB2. rewrite u64s_length, map_length in TRB2.
  assert (HD : forall b', headL D b' = 0 \/ 1 <= headL D b' <= N) by (intros; apply headL_range).
  subst a0 a1. unfold depot_put_entry in *.
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 112%nat ST.
  run_toA 0x78e50. rewrite Z.add_0_r, (swrap32_small n) by lia. br_auto.
  amz. br_auto.
  eapply hash_block with (k := k) (tr := tr); [destruct k; [exfalso; cbn in LK; lia | discriminate] | exact FK | lia | exact MI | apply w_cells_of_bytes; exact TRB | lia |].
  intros a0' a1' a2' a4' a5' a6'. fold h. fold b. fold tb.
  pose proof (HD b) as HB.
  amz; rewrite sx32_small by lia.
  amz; amz; amz; amz; rewrite land_31_small by lia.
  amz; amz; amz.
  (* [comment removed for export] *)
  assert (NODES0 : forall s, 1 <= s <= N ->
          rw_cells rsegs m0 (n0 + 16 * s) [C8 (wz (hshL D s)); C4 (wz (linkL D s)); C4 (wz (sidL D s))]
          /\ 0 <= hshL D s < 2^64 /\ 0 <= linkL D s <= N /\ 0 <= sidL D s < 2^31).
  { intros s Hs; split; [ eapply rw_cells_transport; [apply RNODES; exact Hs | exact MU | exact WM | cbn; lia]
                          | split; [apply depot_hashC_range | split; [apply linkL_range; exact Hs | pose proof (sidL_range D s Hs); lia]]]. }
  unfold headL.
  eapply find_loop with (n0 := n0) (nmax := N) (hsh := hshL D) (lnk := linkL D) (sid := sidL D) (c := chainL D b 1).
  all: try exact MI; try exact NODES0.
  all: match goal with
    | |- 0 <= _ < 2^64 => exact HR
    | |- kHighMemBeg <= _ => unfold kHighMemBeg; plia
    | |- aobj _ _ => plia   (* [comment removed for export] *)
    | |- _ + kDepotNodesBlock <= _ => unfold kDepotNodesBlock; lia
    | |- 0 <= _ < 65536 => try (generalize alloc_ceiling_val); clear -LD; try pose proof alloc_ceiling_val; subst N; lia
    | |- ro_cells _ _ _ _ => exact RMAP
    | |- chain_ok _ _ => apply (chainL_ok (length D)); lia
    | |- Forall _ _ => apply Forall_forall; intros x Hx; apply (chainL_range D b x Hx)
    | |- _ => idtac
    end.
  - (* [comment removed for export] *)
    intros NF0 a0x a2x0. unfold find_st. clear MU0.
    destruct (cfind_putC D k h (proj1 (NoDup_ListNoDup _) ND) eq_refl) as [PF _]. fold b in PF. specialize (PF NF0).
    amz. amz. (* [comment removed for export] *)
    eapply lock_spec with (p := tb) (v := hd 0 (chainL D b 1)) (lo := lo);
      [exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | lia | reflexivity | unfold headL in HB; lia
      | exact TBA | cbv delta [tb]; lia | cbv delta [tb]; lia | exact TBK | reflexivity |].
    intros t0' t1' t2' a1x a2x a3x a4x wl m1 TBK1 MU1 WM1 MI1 ST1. rewrite unsigned_lit in MU1, ST1 by lia.
    replace (ret_pc (Z_to_bv 64 495480)) with (Z_to_bv 64 495480) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    transport_after_call rsegs m0 m1 MU1 WM1. clear MI MU1 WM1.
    amz. amz. replace (bv_eqb (Z_to_bv 64 (hd 0 (chainL D b 1))) (Z_to_bv 64 (hd 0 (chainL D b 1)))) with true by (unfold bv_eqb; rewrite Z.eqb_refl; reflexivity). cbv iota.
    amz. amz. amz.
    amz; rewrite (amo_w_bytes_lit N 1) by lia; mem_after_store; rewrite sx32_small by lia. (* [comment removed for export] *)
    amz; rewrite (swrap32_small (N + 1)) by lia.
    amz; amz; rewrite (Z.mod_small (N + 1) 4294967296) by lia.
    amz; br_auto. (* [comment removed for export] *)
    amz. amz; rewrite (Z.shiftr_div_pow2 (N + 1) 16), (Z.div_small (N + 1) (2^16)) by lia.
    amz; amz; amz. amz; br_auto. (* [comment removed for export] *)
    amz. replace (Z.land (N + 1) 65535) with (N + 1) by (change 65535 with (Z.ones 16); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    amz; rewrite (Z.shiftl_mul_pow2 (N + 1) 4) by lia. amz.
    replace (n0 + (N + 1) * 2 ^ 4) with nd by (cbv delta [nd]; lia).
    amz; amz; amz; amz.
    replace (n0 + (N + 1) * 16) with nd by (cbv delta [nd]; lia).
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
      destruct (rw_cells_app_split m2 (bv_unsigned sp + -112) [c0] (c1 :: c2 :: rest) FR) as [FRa FRbc];
      change (Z.of_nat (cells_size [c0])) with 8 in FRbc;
      destruct (rw_cells_app_split m2 _ [c1; c2] rest FRbc) as [FRb FRc]; clear FRbc;
      change (Z.of_nat (cells_size [c1; c2])) with 16 in FRc
    end.
    replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in FRb, FRc by lia.
    replace (bv_unsigned sp + -104 + 16) with (bv_unsigned sp + -88) in FRc by lia.
    apply (rw_cells_C8_44p m2 _ [C8 (Z_to_bv 64 tr)] n []) in FRb; [|lia]. cbn [app] in FRb.
    assert (NMAP2 : mapped m2 n0 1048576) by (eapply mapped_mono; [exact NMAP | exact WM | unfold kHighMemBeg; plia | plia]).
    assert (FMAP2 : mapped m2 f0 8388608) by (eapply mapped_mono; [exact FMAP | exact WM | unfold kHighMemBeg; plia | plia]).
    assert (NDM : mapped m2 nd 16).
    { intros i Hi. replace (nd + i) with (n0 + (16 * (N + 1) + i)) by (cbv delta [nd]; lia). apply NMAP2. clear -Hi LD; try pose proof alloc_ceiling_val. subst N. lia. }
    pose proof (mapped_rw_cells m2 nd 16 NDM ltac:(cbv delta [nd]; lia) ltac:(lia) ltac:(cbv delta [nd]; lia)) as NODE.
    apply (rw_cells_split_CB rsegs m2 nd [] 16 _ [] [8; 4; 4]%nat) in NODE; [|reflexivity]. cbn [app mk_CB_cells] in NODE.
    assert (FPM : mapped m2 fp (8 * (1 + n))).
    { intros i Hi. replace (fp + i) with (f0 + (8 * depot_total D + i)) by (cbv delta [fp]; lia). apply FMAP2. lia. }
    pose proof (mapped_rw_cells m2 fp (8 * (1 + n)) FPM ltac:(cbv delta [fp]; lia) ltac:(lia) ltac:(cbv delta [fp]; lia)) as FRM.
    apply (rw_cells_split_CB rsegs m2 fp [] (Z.to_nat (8 * (1 + n))) _ [] [8; Z.to_nat (8 * n)]%nat) in FRM; [| cbn [sum_nat]; lia]. cbn [app mk_CB_cells] in FRM.
    amz. (* [comment removed for export] *)
    eapply node_store_spec with (nd := nd) (ap := bv_unsigned sp + -104) (tr := tr) (h := h) (T := depot_total D) (f0 := f0) (lo := lo) (k := k).
    all: try exact MI1; try exact FK; try exact LK; try exact HR; try exact FRb; try exact NODE; try exact RSS; try exact FRM; try exact TRB; try exact TOT0.
    all: rewrite ?unsigned_lit by lia.
    all: try match goal with
      | |- stk _ _ _ _ => exact ST1
      | |- kHighMemBeg <= _ => unfold kHighMemBeg; cbv delta [nd]; plia
      | |- aobj _ _ => cbv delta [nd]; plia   (* [comment removed for export] *)
      | |- _ mod 2 = 0 => reflexivity
      | |- _ \/ _ => cbv delta [nd fp]; try (generalize alloc_ceiling_val); clear -NF LD TB TOT0 N0A F0A LK; try pose proof alloc_ceiling_val; subst N n; lia
      | |- evt _ _ _ => idtac
      | |- _ => cbv delta [nd fp]; subst n N; lia
      end.
    intros t0z t1z t2z a1z a2z a3z a4z a5z a6z a7z t3z t4z t5z t6z m3 MI3 ST3 ARGS3 NODE3 SSC3 FRM3 TRC3 MU3 WM3.
    rewrite ?unsigned_lit in MU3, ST3 by lia.
    unfold SS in MU3, SSC3. fold n in MU3. fold n in FRM3. fold n in ARGS3.
    replace (f0 + 8 * (depot_total D + 1 + n)) with (fp + 8 * (1 + n)) in MU3 by (cbv delta [fp]; lia).
    fold fp in MU3. fold fp in FRM3.
    replace (ret_pc (Z_to_bv 64 495616)) with (Z_to_bv 64 495616) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear NODE FRM FRb RSS TRB.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MI1 MU3 WM3.
    amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    do 13 amz.
    (* [comment removed for export] *)
    eapply stk_release in FRa; [| exact ST3 | plia]. cbn [cells_size csize Nat.add] in FRa.
    change (Z.of_nat 8%nat) with 8 in FRa. replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in FRa by lia.
    eapply stk_release in ARGS3; [| exact FRa | plia]. cbn [cells_size csize Nat.add] in ARGS3.
    change (Z.of_nat 16%nat) with 16 in ARGS3. replace (bv_unsigned sp + -104 + 16) with (bv_unsigned sp + -88) in ARGS3 by lia.
    eapply stk_release in FRc; [| exact ARGS3 | plia]. cbn [cells_size csize Nat.add] in FRc.
    change (Z.of_nat 88%nat) with 88 in FRc. replace (bv_unsigned sp + -88 + 88) with (bv_unsigned sp) in FRc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    (subst hotQ; apply evt_done); unfold depot_putC; fold h; rewrite PF; cbn [fst snd]; fold N;
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, kDepotNodesL1; cbn [outside]; cbv delta [tb nd fp]; try (generalize alloc_ceiling_val); clear -BR LD TB TOT0 N00 F00 LK; try pose proof alloc_ceiling_val; subst N n; intros x Hx; lia. }
    split; [exact WM|]. split; [exact MI3|]. split; [exact FRc|].
    (* [comment removed for export] *)
    unfold depot_repL. cbn [al_stackStore al_depot_nodes_map1 al_theDepot al_depot_n_uniq_ids AL_pasan]. unfold TAB, NUNIQ, MAP1, SS.
    split. { intros b' Hb'. rewrite headL_snoc. change (bkt k) with b. destruct (Z.eqb_spec b b') as [<-|NE].
             - fold N. exact TBK1.
             - eapply rw_cells_transport; [apply RTAB; exact Hb' | exact MU | exact WM | cbn; cbv delta [tb nd fp]; try (generalize alloc_ceiling_val); clear -Hb' NE BR N00 F00 TOT0 LOLE CEIL CV LD TB LK; try pose proof alloc_ceiling_val; subst N n; lia]. }
    split. { rewrite length_app. cbn [length]. replace (Z.of_nat (length D + 1)) with (N + 1) by (subst N; lia). exact RNU. }
    split. { eapply ro_cells_transport; [exact RMAP0 | exact MU | cbn; cbv delta [tb nd fp]; try (generalize alloc_ceiling_val); clear -BR LD N00 F00 TOT0 TB LK LOLE CEIL CV; try pose proof alloc_ceiling_val; subst N n; lia]. }
    split. { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite Nat2Z.inj_add in Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. fold N in Hi.
             destruct (Z.eq_dec i (N + 1)) as [->|NE].
             - unfold hshL. cbv delta [N]. rewrite keyL_snoc_new, linkL_snoc_new, sidL_snoc_new. change (bkt k) with b. unfold headL.
               cbv delta [nd N] in NODE3. exact NODE3.
             - unfold hshL. cbv delta [N]. rewrite keyL_snoc_old, linkL_snoc_old, sidL_snoc_old by lia. fold N.
               eapply rw_cells_transport; [apply RNODES; lia | exact MU | exact WM | cbn; cbv delta [tb nd fp]; try (generalize alloc_ceiling_val); clear -Hi NE NF BR N00 N01 F00 F01 TOT0 TB LD LK LOLE CEIL CV; try pose proof alloc_ceiling_val; subst N n; lia]. }
    split. { exists j4, j5. rewrite depot_total_snoc. fold n. fold n in SSC3. exact SSC3. }
    unfold kDepotNodesBlock, kStackStoreBlockBytes.
    split. { eapply mapped_mono; [exact NMAP | exact WM | unfold kHighMemBeg; plia | plia]. }
    split. { eapply mapped_mono; [exact FMAP | exact WM | unfold kHighMemBeg; plia | plia]. }
    split; [exact N0A|]. split; [exact F0A|]. split; [exact NF|]. rewrite depot_total_snoc. split; [lia|].
    rewrite length_app. cbn [length]. try (generalize alloc_ceiling_val); clear -LAY LD; try pose proof alloc_ceiling_val. lia.
  - (* [comment removed for export] *)
    intros s CF NZ a1x a2x. unfold find_st. clear MU.
    destruct (cfind_putC D k h (proj1 (NoDup_ListNoDup _) ND) eq_refl) as [_ PF]. fold b in PF. rewrite CF in PF. specialize (PF NZ).
    do 13 amz.
    eapply stk_release in FR; [| exact ST | plia]. cbn [cells_size csize Nat.add] in FR.
    change (Z.of_nat 112%nat) with 112 in FR. replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) in FR by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    (subst hotQ; apply evt_done); unfold depot_putC; fold h; rewrite PF; cbn [fst snd];
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU0]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
    split; [exact WM|]. split; [exact MI|]. split; [exact FR|].
    unfold depot_repL. cbn [al_stackStore al_depot_nodes_map1 al_theDepot al_depot_n_uniq_ids AL_pasan]. unfold TAB, NUNIQ, MAP1, SS, kDepotNodesBlock, kStackStoreBlockBytes.
    split. { intros b' Hb'. eapply rw_cells_transport; [apply RTAB; exact Hb' | exact MU0 | exact WM | cbn; try (generalize alloc_ceiling_val); clear -Hb' LOLE CEIL CV; try pose proof alloc_ceiling_val; lia]. }
    split. { first [exact RNU | eapply rw_cells_transport; [exact RNU | exact MU0 | exact WM | cbn; try (generalize alloc_ceiling_val); clear -LOLE CEIL CV; try pose proof alloc_ceiling_val; lia]]. }
    split. { first [exact RMAP | eapply ro_cells_transport; [exact RMAP0 | exact MU0 | cbn; try (generalize alloc_ceiling_val); clear -LOLE CEIL CV; try pose proof alloc_ceiling_val; lia]]. }
    split. { intros i Hi. eapply rw_cells_transport; [apply RNODES; exact Hi | exact MU0 | exact WM | cbn; try (generalize alloc_ceiling_val); clear -Hi LOLE CEIL CV N00 N01 LD; try pose proof alloc_ceiling_val; subst N; lia]. }
    split. { exists j4, j5. first [exact RSS | eapply rw_cells_transport; [exact RSS | exact MU0 | exact WM | cbn; try (generalize alloc_ceiling_val); clear -LOLE CEIL CV; try pose proof alloc_ceiling_val; lia]]. }
    split. { eapply mapped_mono; [exact NMAP | exact WM | unfold kHighMemBeg; plia | plia]. }
    split. { eapply mapped_mono; [exact FMAP | exact WM | unfold kHighMemBeg; plia | plia]. }
    split; [exact N0A|]. split; [exact F0A|]. split; [exact NF|]. split; [exact TOT0|]. exact LAY.
Qed.

End CEIL.

(* [comment removed for export] *)
Lemma ro_cells_agree_gen : forall segs (m m' : mem) a cs,
  ro_cells segs m a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (a + i)) = m (wz (a + i))) -> ro_cells segs m' a cs.
Proof.
  intros segs m m' a cs [WFc B] AG. split; [exact WFc|].
  eapply bytes_at_agree_gen; [exact B|]. rewrite cells_bytes_length by exact WFc. exact AG.
Qed.
Lemma rw_cells_agree_gen : forall segs (m m' : mem) a cs,
  rw_cells segs m a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (a + i)) = m (wz (a + i))) -> rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs [[WFc B] (W0 & W1 & W)] AG. split; [split; [exact WFc|]|].
  - eapply bytes_at_agree_gen; [exact B|]. rewrite cells_bytes_length by exact WFc. exact AG.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. unfold wview, wa in *. rewrite (AG i Hi). apply W. exact Hi.
Qed.

Lemma depot_repL_agree : forall L segs D n0 f0 (m m' : mem),
  depot_repL L segs D n0 f0 m -> (forall a, depot_foot L n0 f0 a -> m' (wz a) = m (wz a)) -> depot_repL L segs D n0 f0 m'.
Proof.
  intros L segs D n0 f0 m m' REP AG.
  (first [ dand12 REP as RTAB RNU RMAP RNODES (j4 & j5 & RSS) NMAP FMAP N0A F0A NF TOT0 LAY | destruct REP as (RTAB & RNU & RMAP & RNODES & (j4 & j5 & RSS) & NMAP & FMAP & N0A & F0A & NF & TOT0 & LAY) ]).
  unfold depot_foot, kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in *.
  assert (AG1 : forall a i, al_stackStore L <= a + i -> a + i < al_depot_nodes_map1 L + 8 * 2^15 -> m' (wz (a + i)) = m (wz (a + i)))
    by (intros a i H1 H2; apply AG; left; lia).
  unfold depot_repL. unfold kDepotNodesBlock, kStackStoreBlockBytes.
  split. { intros b Hb. eapply rw_cells_agree_gen; [apply RTAB; exact Hb|]. cbn. intros i Hi. apply AG1; lia. }
  split. { eapply rw_cells_agree_gen; [exact RNU|]. cbn. intros i Hi. apply AG1; lia. }
  split. { eapply ro_cells_agree_gen; [exact RMAP|]. cbn. intros i Hi. apply AG1; lia. }
  split. { intros j Hj. eapply rw_cells_agree_gen; [apply RNODES; exact Hj|]. cbn. intros i Hi. apply AG. right; left. lia. }
  split. { exists j4, j5. eapply rw_cells_agree_gen; [exact RSS|]. cbn. intros i Hi. apply AG1; lia. }
  split. { eapply mapped_agree_gen; [exact NMAP|]. intros i Hi. apply AG. right; left. lia. }
  split. { eapply mapped_agree_gen; [exact FMAP|]. intros i Hi. apply AG. right; right. lia. }
  tauto.
Qed.

#[global] Instance DepotRepL : DepotRep := {| depot_rep := depot_repL; depot_rep_agree := depot_repL_agree |}.
