(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflA_Check2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma arm_LENGTH_run : forall s c r,
  (is_wrap s = 5 \/ is_wrap s = 1) -> is_flags s = 0 ->
  arm_LENGTH (mkW s c r) = ALeave (mkW (iset_mode s DONE) c (irset_ret r Z_STREAM_END)).
Proof.
  intros s c r Hw Hf. unfold arm_LENGTH. mstep1 (@gs_eq inflate_state). rewrite (wrap15_eqb0 _ Hw), Hf. change (negb false && negb (0 =? 0)) with false.
  mstep1 (@aret_eq bool). mstep1 set_mode_eq. unfold arm_DONE. mstep1 ur_eq. rewrite aleave_eq. reflexivity.
Qed.

Theorem arm_LENGTH_sim : arm_stmt LENGTH.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LENGTH) with arm_LENGTH.
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  arm_begin C HM HRC HX HF HV HP.
  assert (Hf : is_flags s = 0) by (destruct Xflags as [X0 | (_ & XM & _)]; [exact X0 | exfalso; rewrite Hmode in XM; destruct XM as [E|E]; cbv in E; discriminate]).
  rewrite (arm_LENGTH_run s c r Xwrap Hf).
  assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
  assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
  assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
  pose proof (is6_wrap _ _ _ _ Msc) as C16. pose proof (wrap15_range _ Xwrap) as Hwr. pose proof (wrap15_ne0 _ Xwrap) as Hw0.
  pose proof (is6_flags _ _ _ _ Msc) as C24. rewrite Hf in C24.
  change (arm6_pc LENGTH) with 0x1d374.
  arm_symex ilK 16%nat [false; true] [RVal (EVar 45%nat); RVal (ELit 0)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals F0
    (mkst R (Z_to_bv 64 0x1d374) M s6_rom) R' HR' Hfr Hms.
  all: try arm_side.
  set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16208)) in *.
  set (r' := irset_ret r Z_STREAM_END).
  assert (HM1 : LMEM v (mkW (iset_mode s DONE) c r') M1).
  { apply (LMEM_regs v (iset_mode s DONE) c r c r'); [| subst r'; reflexivity ..].
    apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
    apply (is6_upd_mode M (cv_S v) _ s DONE Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
  exists R', M1, pc6_leave. split; [subst M1; by_run Hms|].
  cbn [arm_post]. split; [reflexivity|]. split.
  2:{ subst M1 r'. cbn [ir_put irset_ret]. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
  split; [exact HM1|]. split.
  { apply (LX_step0 v s c r _ c r' HX NH NB); subst r'; try reflexivity; [live_mode_tac | cbn; unfold Z_STREAM_END; lia | exact Xmsg]. }
  split; [apply same_blocks_mode|].
  symex_reg HR' (9%bv : reg) as G8'. symex_reg HR' (27%bv : reg) as G26'.
  unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret].
  regs_via Hfr; first [exact G8' | exact G26'].
Qed.
End FXG.
