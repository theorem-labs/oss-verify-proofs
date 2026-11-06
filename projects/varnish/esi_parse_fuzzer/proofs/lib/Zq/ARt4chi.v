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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtSoqz ARtSnjd ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.

Module AFreePB.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSnjd ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition qput_recret : Z := 0x3b528.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition qput_pre_big_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto p n qmax cmax sb lo : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto -> a4 = wz (p + -16) -> a5 = wz n ->
    0 <= q -> q + 88 <= kHighMemBeg -> 0 <= cache < 2^64 -> 0 <= sto < 2^64 -> 0 <= c < 2^64 ->
    0 <= p + -16 -> p < 2^64 -> 0 <= n < 2^64 ->
    cmax <> 0 -> 0 <= cmax < 2^64 -> 0 <= qmax < n -> 0 <= sb -> sb + 2^37 < 2^64 ->
    (p + -16 < sb \/ sb + 2^37 <= p + -16) ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax)] -> ro_cells rsegs m (q + 80) [C8 (wz cmax)] ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    (forall (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -80) [C8 (wz cache); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 80) ->
        evt rsegs Q (MS (mkR (wz qput_recret) (wz (bv_unsigned sp + -80)) gp tp t0 t1 t2 (wz q) (wz c)
                            (wz (bv_unsigned sp + -80)) (wz (p + -16)) (wz cache) (wz sto) (wz (p + -16)) (wz n) a6 a7
                            s2 s3 s4 s5 (wz cmax) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz cbrec_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz qput_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition qput_tailB_stmt : Prop :=
  forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (s0v s1v s2v s3v s4v s5v s6v ra0 f0 f8 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv q c cmax nb fb lb qb lo : Z) (s2 s3 s4 s5 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (spv - 80) -> lo <= spv - 80 -> 0 <= spv - 80 -> spv <= 2^64 ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> 0 <= cmax < 2^64 -> 0 <= qb <= cmax ->     (* [comment removed for export] *)
    rw_cells rsegs m (spv + -80) [C8 f0; C8 f8; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (stk rsegs m lo spv ->
        evt rsegs Q (MS (mkR ra0 (wz spv) gp tp t0 t1 t2 s0v s1v (wz qb) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz qput_recret) (wz (spv + -80)) gp tp t0 t1 t2 (wz q) (wz c) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz cmax) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz qput_recret) fc None m (seg_rom rsegs)).

End CEIL.

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem qput_pre_big_ok : qput_pre_big_stmt.
Proof.
  unfold qput_pre_big_stmt. intros until Q.
  intros MI ST LOLE CEIL A0 A1 A2 A3 A4 A5 Q0 Q1 CAR STR CR PLO PHI NR CM0 CMR QMR SB0 SBH POUT QMX CMX CSB K.
  pose proof alloc_ceiling_val as CV.
  unfold qput_entry, cbrec_entry, qput_recret, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  subst a0 a1 a2 a3 a4 a5. lit_addrs.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 80%nat ST.
  do 12 amz. (* [comment removed for export] *)
  amz. amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  destruct POUT as [PLT | PGE].
  - amz. br_taken. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    eapply K; try eassumption.
  - amz. br_not_taken.
    amz. amz. amz. rewrite ?unsigned_lit by lia. (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    amz. amz. amz.
    eapply K; try eassumption.
Qed.

Theorem qput_tailB_ok : qput_tailB_stmt.
Proof.
  unfold qput_tailB_stmt. intros until Q. intros MI ST LOLE S0 S1 CLO CHI CMR QBR FR CC K.
  pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, qput_recret in *. aobj_lin_all.
  replace (spv - 80) with (spv + -80) in ST by lia.
  pose proof (munch_refl [(spv - 80, spv)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. (* [comment removed for export] *)
  amz. br_taken. (* [comment removed for export] *)
  do 10 amz.
  eapply stk_release in FR; [| exact ST | plia]. cbn [cells_size csize Nat.add] in FR.
  lazymatch type of FR with stk _ _ _ ?h => replace h with spv in FR by (cbn; lia) end.
  apply K. exact FR.
Qed.

End CEIL2.
End AFreePB.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].

Ltac qdrain_lock LCK q hi rl :=
  apply (hdr4_join _ _ 0 rl hi) in LCK; [| lia | lia | lia | cbn; tauto]; replace (0 + 256 * rl + 65536 * hi) with (256 * rl + 65536 * hi) in LCK by lia.

(* [comment removed for export] *)
Ltac drain_lock LCK q hi QM4 :=
  do 6 amz;
  amz; amz; amz; rewrite (land_m4 (q + 152)) by first [exact QM4 | plia]; amz;
  qdrain_lock LCK q hi 0;
  amz; rewrite sx32_small by lia;
  amz; amz; amz; amz; replace (0 + 65536 * hi) with (256 * (256 * hi)) by lia; rewrite (cas_set_low0 1 (256 * hi)) by lia;
  replace (1 + 256 * (256 * hi)) with (1 + 256 * 0 + 65536 * hi) by lia;
  scstep; zsimp;
  amz; if_false;
  amz; rewrite (land255_low0 (256 * hi)) by lia;
  amz; if_false;
  replace (256 * 0 + 65536 * hi) with (0 + 256 * 0 + 65536 * hi) in LCK by lia;
  apply (hdr4_split _ _ 1 0 hi) in LCK; [| lia | lia | lia | cbn; tauto].

Lemma land_m4_1 : forall q, (q + 152) mod 4 = 0 -> 0 <= q -> q + 156 <= 2^64 -> Z.land (q + 153) 18446744073709551612 = q + 152.
Proof.
  intros q H Hq Hb. change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia. change (2^2) with 4.
  replace (q + 153) with ((q + 152) + 1) by lia. rewrite Z.add_mod, H, Z.add_0_l, (Z.mod_small 1 4), Z.mod_small by lia. lia.
Qed.
Lemma land3_1 : forall q, (q + 152) mod 4 = 0 -> 0 <= q -> Z.land (q + 153) 3 = 1.
Proof.
  intros q H Hq. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4.
  replace (q + 153) with ((q + 152) + 1) by lia. rewrite Z.add_mod, H by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac drain_trylock LCK q hi QM4 :=
  amz; amz; amz; (* [comment removed for export] *)
  amz; rewrite (land_m4_1 q QM4) by lia; (* [comment removed for export] *)
  amz; rewrite (land3_1 q QM4) by lia; (* [comment removed for export] *)
  amz; amz; amz; (* [comment removed for export] *)
  change (bv_swrap 32 256) with 256; change (bv_swrap 32 65280) with 65280;
  apply (hdr4_join _ _ 0 0 hi) in LCK; [| lia | lia | lia | cbn; tauto];
  replace (0 + 256 * 0 + 65536 * hi) with (65536 * hi) in LCK by lia;
  amz; rewrite sx32_small by lia; (* [comment removed for export] *)
  amz; amz; amz; amz; (* [comment removed for export] *)
  replace (Z.lxor (65536 * hi) (Z.land (Z.lxor (65536 * hi) 256) 65280)) with (256 * 1 + 65536 * hi)
    by (pose proof (cas_set_byte1 hi 0 1) as E; rewrite Z.mul_0_r, Z.add_0_l, Z.mul_1_r in E; symmetry; apply E; lia);
  scstep; zsimp;
  amz; if_false; (* [comment removed for export] *)
  amz; amz; rewrite (srlw8_byte (65536 * hi)) by lia; (* [comment removed for export] *)
  replace (65536 * hi / 256) with (hi * 256) by (apply Z.div_unique_exact; lia); rewrite Z_mod_mult;
  amz; if_true; (* [comment removed for export] *)
  replace (256 * 1 + 65536 * hi) with (0 + 256 * 1 + 65536 * hi) in LCK by lia;
  apply (hdr4_split _ _ 0 1 hi) in LCK; [| lia | lia | lia | cbn; tauto].

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem qdrainR0_ok : qdrainR0_stmt.
Proof.
  unfold qdrainR0_stmt. intros until Q.
  intros MI ST LOLE CEIL A0 A1 A2 A3 Q0 Q1 QAL CLO CHI HIR GQ0 QB0 QMR QM0 QMN NB NBR FBR LBR LCK QMX GL CC K.
  pose proof alloc_ceiling_val as CV.
  unfold qdrain_entry, recycle_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3.
  set (qq := q / 8) in *. assert (QQ : q = 8 * qq) by (subst qq; rewrite (Z_div_mod_eq_full q 8) at 1; rewrite QAL; lia). clearbody qq.
  assert (QM4 : (q + 152) mod 4 = 0) by (rewrite QQ; replace (8 * qq + 152) with ((2 * qq + 38) * 4) by lia; apply Z_mod_mult).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  drain_lock LCK q hi QM4.
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz.
  amz. amz. amz.
  amz. amz. amz. amz. amz.
  amz. amz. (* [comment removed for export] *)
  amz. amz. amz. br_not_taken. (* [comment removed for export] *)
  drain_trylock LCK q hi QM4.
  amz. (* [comment removed for export] *)
  do 6 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  eapply K; [exact MU | exact WM | assumption | exact ST | exact LCK | exact GL | exact CC].
Qed.

Theorem qdrainRA_ok : qdrainRA_stmt.
Proof.
  unfold qdrainRA_stmt. intros until Q.
  intros MI ST LOLE CEIL A0 A1 A2 A3 Q0 Q1 QAL CLO CHI GLO GHI DJ HIR GQ0 QB0 QMR QM0 QMN NB NBR GN GN0 GNR FBR LBR LCK QMX GL CC GLN K.
  pose proof alloc_ceiling_val as CV.
  unfold qdrain_entry, recycle_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3.
  set (qq := q / 8) in *. assert (QQ : q = 8 * qq) by (subst qq; rewrite (Z_div_mod_eq_full q 8) at 1; rewrite QAL; lia). clearbody qq.
  assert (QM4 : (q + 152) mod 4 = 0) by (rewrite QQ; replace (8 * qq + 152) with ((2 * qq + 38) * 4) by lia; apply Z_mod_mult).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32); (gl, gl + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  drain_lock LCK q hi QM4.
  amz. amz. br_not_taken.
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz.
  amz.
  amz. (* [comment removed for export] *)
  amz. amz.
  amz. (* [comment removed for export] *)
  amz. amz. amz.
  amz. amz. amz. amz. amz.
  amz. amz.
  amz. amz. amz. br_not_taken. (* [comment removed for export] *)
  drain_trylock LCK q hi QM4.
  amz.
  do 6 amz.
  amz.
  release_frame FR ST (bv_unsigned sp).
  eapply K; [exact MU | exact WM | assumption | exact ST | exact LCK | exact GL | exact CC | exact GLN].
Qed.

End CEIL.
