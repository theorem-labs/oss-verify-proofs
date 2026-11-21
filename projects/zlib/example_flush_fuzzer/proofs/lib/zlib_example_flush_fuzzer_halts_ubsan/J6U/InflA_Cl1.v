(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflMem2.

Module InflArmLib6e.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma le2_eqm : forall a b, a mod 2 ^ 16 = b mod 2 ^ 16 -> Z_to_le_bytes 2 a = Z_to_le_bytes 2 b.
Proof.
  intros a b H. rewrite <- (SymExec.Z_to_le_bytes_mod 2 a), <- (SymExec.Z_to_le_bytes_mod 2 b). change (8 * Z.of_nat 2) with 16. rewrite H. reflexivity.
Qed.
Lemma le2_wrap16 : forall a, Z_to_le_bytes 2 a = Z_to_le_bytes 2 (wrap16 a).
Proof. intros a. apply le2_eqm. rewrite wrap16_mod. rewrite Z.mod_mod by lia. reflexivity. Qed.

Section S.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma LMEM_store_lens : forall s c r M i val b,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    0 <= i < 320 -> arr_len (is_lens s) = 320 -> Z_to_le_bytes 2 val = Z_to_le_bytes 2 (wrap16 b) ->
    LMEM v (mkW (iset_lens s (arr_set (is_lens s) i (wrap16 b))) c r) (wbytes M (zw (cv_S v + 168 + 2 * i)) (Z_to_le_bytes 2 val)).
  Proof.
    intros s c r M i val b HM Hput Hi Hlen Hvb.
    open_ictx C. open_lmem HM. rewrite Hvb.
    constructor; cbn [w_s w_c w_r].
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoS. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoS Hi CS. cbn. lia.
    - replace (is6_scalars _ _ _ (iset_lens s _)) with (is6_scalars (wbytes M (zw (cv_S v + 168 + 2 * i)) (Z_to_le_bytes 2 (wrap16 b))) (cv_S v) (ISP (cv_ZP v) (cv_WB v)) s)
        by (destruct s; reflexivity).
      apply (is6_scalars_lens_cell M (cv_S v) _ s i (wrap16 b) Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia | exact Hi].
    - replace (is_lens (iset_lens s _)) with (arr_set (is_lens s) i (wrap16 b)) by (destruct s; reflexivity).
      intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite Hlen.
      replace ((0 <=? i) && (i <? 320)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Bool.andb_true_r.
      pose proof (cells_write_cell s6u_segs M (cv_S v + 168) 2 2%nat 320 (arr_get (is_lens s)) i (wrap16 b) Mlens ltac:(cbn; lia) Hi ltac:(clear - CS; lia) ltac:(clear - CS; lia) j Hj) as X.
      cbv beta in X. rewrite Z.eqb_sym. destruct (j =? i); exact X.
    - replace (is_work (iset_lens s _)) with (is_work s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | cbn; lia].
    - replace (is_codes (iset_lens s _)) with (is_codes s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | cbn; lia].
    - replace (is_window (iset_lens s _)) with (is_window s) by (destruct s; reflexivity).
      intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CSW. cbn. clear - CSW Hi CS CWB Hwn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. specialize (CSI ltac:(lia)). unfold sep in CSI. cbn. clear - CSI Hi CS CI0. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. specialize (CSP ltac:(lia)). unfold sep in CSP. cbn. clear - CSP Hi CS CP0 Hput. lia.
    - apply (izs6_other v C); [exact Mzs | lia | cbn; lia | unfold sep in CZS; cbn; clear - CZS Hi CS CZP; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfS; cbn; clear - CfS Hi CS Csp; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfS; cbn; clear - CfS Hi CS Csp; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfS; cbn; clear - CfS Hi CS Csp; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.
End S.
End FXG.
End InflArmLib6e.
Export InflArmLib6e.

Module InflNeed6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Section NeedLoopS.
  Variable v : icv.
  Variable s : inflate_state.
  Variables (n pcH pcE : Z).
  Variables (JS JE : icall -> iregs -> bvmap 5 word -> Prop).
  Local Abbreviation NI := (cv_NI v). Local Abbreviation NO := (cv_NO v).

  Hypothesis C : ictx v.
  Hypothesis Hn : 0 < n <= 56.
  Hypothesis STEP_H : forall c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pcH) M s6u_rom)
               /\ JS c (pull1 c r) R1.
  Hypothesis STEP_E : forall c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pcE) M s6u_rom)
               /\ JE c (pull1 c r) R1.
  Hypothesis DRY : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.

  Lemma need_loop_s : forall k c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> n <= ir_bits r + 8 * Z.of_nat k ->
    match NEEDBITS_k k n (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pcE) M s6u_rom)
        /\ JE c r1 R1 /\ RINV NI NO r1 /\ same5 r r1 /\ n <= ir_bits r1 < n + 8
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
        /\ LREG_leave v (mkW s c r1) R1 /\ RINV NI NO r1 /\ same5 r r1 /\ ir_have r1 = 0 /\ ir_bits r1 < n
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ARet _ _ => False
    end.
  Proof.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    induction k as [|k IH]; intros c r R M HM HRC HJ HR HC Hb Hk.
    { exfalso. cbn in Hk. lia. }
    rewrite NEEDBITS_k_S. replace (ir_bits r <? n) with true by (symmetry; apply Z.ltb_lt; exact Hb).
    pose proof HR as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11').
    destruct (Z.eqb_spec (ir_have r) 0) as [Hz|Hz].
    - destruct (DRY c r R M HM HRC HJ HR HC Hb Hz) as (R1 & Hms & HL).
      exists r, R1. split; [reflexivity|]. split; [exact Hms|]. split; [exact HL|]. split; [exact HR|].
      split; [apply same5_refl|]. split; [exact Hz|]. split; [exact Hb|]. split; [exact HM | exact HRC].
    - destruct (pull1_RINV NI NO s c r ltac:(lia) ltac:(lia) HR HC ltac:(lia) ltac:(lia)) as [Ep HR1].
      rewrite Ep.
      assert (HM1 : LMEM v (mkW s c (pull1 c r)) M) by (apply (LMEM_regs v s c r c (pull1 c r) M HM); reflexivity).
      assert (HRC1 : RETC v (mkW s c (pull1 c r)) M) by (eapply RETC_regs; [exact HRC | reflexivity]).
      assert (S5 : same5 r (pull1 c r)) by (repeat split; reflexivity).
      destruct (Z_lt_le_dec (ir_bits r + 8) n) as [LT|GE].
      + destruct (STEP_H c r R M HM HJ HR HC LT ltac:(lia)) as (R1 & Hms1 & HJ1).
        specialize (IH c (pull1 c r) R1 M HM1 HRC1 HJ1 HR1 HC ltac:(cbn; lia) ltac:(cbn; cbn in Hk; lia)).
        destruct (NEEDBITS_k k n (mkW s c (pull1 c r))) as [[] w2 | w2 | rc w2]; [| | exact IH].
        * destruct IH as (r2 & R2 & -> & Hms2 & HJ2 & HR2 & S2 & B2 & HM2 & HRC2). exists r2, R2.
          split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HJ2|]. split; [exact HR2|].
          split; [exact (same5_trans _ _ _ S5 S2)|]. split; [exact B2|]. split; [exact HM2 | exact HRC2].
        * destruct IH as (r2 & R2 & -> & Hms2 & HL2 & HR2 & S2 & Z2 & B2 & HM2 & HRC2). exists r2, R2.
          split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HL2|]. split; [exact HR2|].
          split; [exact (same5_trans _ _ _ S5 S2)|]. split; [exact Z2|]. split; [exact B2|]. split; [exact HM2 | exact HRC2].
      + destruct (STEP_E c r R M HM HJ HR HC Hb GE ltac:(lia)) as (R1 & Hms1 & HJ1).
        rewrite NEEDBITS_k_done by (cbn; lia).
        exists (pull1 c r), R1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HJ1|]. split; [exact HR1|].
        split; [exact S5|]. split; [cbn; lia|]. split; [exact HM1 | exact HRC1].
  Qed.
End NeedLoopS.
End FXG.
End InflNeed6b.
Export InflNeed6b.


Module InflA_Codelens1.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition ilC1 : cfg := ilSx [0x1f96c; 0x1f9d8] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section CodeL1.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 : Z).
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.
  Variable ext : Z.
  Hypothesis TD : tab_ok CODES (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_lencode s).
  Hypothesis Hofs : cofs_ok (is_lencode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.
  Hypothesis Hhv : 0 <= is_have s < 2 ^ 32.
  Hypothesis Hnd : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31.

  Local Abbreviation db := (is_lenbits s).
  Local Abbreviation A := (ctab6 v (is_lencode s)).
  Definition cent1 (h : Z) : Z := cat (is_codes s) (is_lencode s) (BITSv h db).

  Definition CK (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 16 = zw (is_have s) /\ getr R 11 = zw (is_nlen s + is_ndist s) /\ getr R 12 = zw (is_nlen s) /\ getr R 13 = zw db
    /\ getr R 19 = zw b0 /\ getr R 31 = zw h0 /\ getr R 17 = zw (cv_I0 v + n0) /\ getr R 22 = zw (h0 * 2 ^ 32)
    /\ getr R 15 = zw (Z.ones db) /\ getr R 14 = zw A /\ getr R 21 = zw 1.
  Definition CJS (r : iregs) (R : bvmap 5 word) : Prop :=
    CK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 23 = zw (ir_have r) /\ getr R 6 = zw (ir_have r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 28 = zw (cv_I0 v + ir_next r)
    /\ getr R 5 = zw (ir_bits r) /\ getr R 7 = zw (ir_bits r) /\ getr R 20 = zw (- ir_bits r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition CJE (r : iregs) (R : bvmap 5 word) : Prop :=
    CK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 23 = zw (ir_have r) /\ getr R 6 = zw (ir_have r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 28 = zw (cv_I0 v + ir_next r)
    /\ getr R 5 = zw (ir_bits r) /\ getr R 7 = zw (ir_bits r) /\ getr R 20 = zw (- ir_bits r)
    /\ getr R 24 = zw (cent (cent1 (ir_hold r))) /\ getr R 29 = zw (cent (cent1 (ir_hold r)) / 2 ^ 8) /\ getr R 30 = zw (code_bits (cent1 (ir_hold r))).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold CJS, CK in X;
    destruct X as ((HF & G9 & G16 & G11 & G12 & G13 & G18 & G31 & G17 & G21 & G15 & G14 & G20) & G22 & G24 & G6 & G25 & G28 & G5 & G7 & G19 & Ib & In & Ih); open_fixc HF.

  Definition cpins1 : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (16, EVar 51%nat); (11, EVar 52%nat); (12, EVar 53%nat); (13, EVar 54%nat);
     (19, EVar 47%nat); (31, EVar 48%nat); (17, EAdd (EVar 43%nat) (EVar 49%nat)); (22, EShl (EVar 48%nat) 32);
     (15, EVar 45%nat); (14, EVar 46%nat); (21, ELit 1);
     (25, EVar 40%nat); (23, EVar 36%nat); (6, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (28, EAdd (EVar 43%nat) (EVar 44%nat));
     (5, EVar 41%nat); (7, EVar 41%nat); (20, ESub (ELit 0) (EVar 41%nat))].
  Definition cvb1 : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 65536);
     (51%nat, 2 ^ 32); (52%nat, 2 ^ 32); (53%nat, 2 ^ 31); (54%nat, 16); (55%nat, 65536)].

  Ltac c1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext :=
    cbn [famA]; rewrite ?bmod_get by exact Hby;
    rewrite ?idx1_exec by (first [exact Rhold | exact Hby | clear - Rbits Hb64 Rt1; lia]);
    rewrite ?cent_reasm, ?cent_bits;
    lazymatch goal with
    | |- exists bs, rdn _ _ _ _ = Some bs /\ _ => match goal with |- context [BITSv ?h ?n] => tab_read2 TAB (BITSv h n); pose proof (BITSv_bound h n ltac:(lia)); lia end
    | |- 0 <= _ /\ _ <= 2 ^ 64 => match goal with |- context [BITSv ?h ?n] => generalize (BITSv_bound h n ltac:(lia)); clear - HA0 HA1 Hext Rt2; intro; lia end
    | |- context [if _ <? _ then 1 else 0] => match goal with |- context [BITSv ?h ?n] => pose proof (BITSv_bound h n ltac:(lia)); ub_ptr_side end
    | |- exists _, _ => idtac
    | |- _ => first [ assumption | match goal with |- context [BITSv ?h ?n] => pose proof (BITSv_bound h n ltac:(lia)); lia end | idtac ]
    end.

  Ltac cj_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 :=
    let Q22 := fresh in let Q24 := fresh in let Q6 := fresh in let Q25 := fresh in let Q28 := fresh in
    let Q5 := fresh in let Q7 := fresh in let Q19 := fresh in let Q23 := fresh in let Q29 := fresh in let Q30 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (23%bv : reg) as Q24; symex_reg HR (6%bv : reg) as Q6; symex_reg HR (26%bv : reg) as Q25;
    symex_reg HR (28%bv : reg) as Q28; symex_reg HR (5%bv : reg) as Q5; symex_reg HR (7%bv : reg) as Q7; symex_reg HR (20%bv : reg) as Q19;
    symex_reg HR (24%bv : reg) as Q23; symex_reg HR (29%bv : reg) as Q29; symex_reg HR (30%bv : reg) as Q30;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite ?cent_reasm in Q23; rewrite ?cent_reasm in Q29; rewrite ?cent_reasm, ?cent_bits in Q30;
    unfold CJS, CJE, CK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q24; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q25; f_equal; lia
          | rewrite Q28; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q7; f_equal; lia
          | rewrite Q19; f_equal; lia
          | rewrite Q23; f_equal; f_equal; f_equal; lia
          | rewrite Q29; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q30; f_equal; f_equal; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "CJ LEFT" G end ].

  Ltac c1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones :=
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3);
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1];
    pose proof (ctab6_cells v s c _ _ (is_lencode s) C HM Hofs) as TAB;
    pose proof (ones_range15 db Rt1) as Hones.

  Lemma cl_step_H : forall r R M,
    LMEM v (mkW s c r) M -> CJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < code_bits (cent1 (ir_hold (pull1 c r))) ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f96c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f96c) M s6u_rom)
               /\ CJS (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    c1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (cent1 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (cent1 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (cent1 (ir_hold (pull1 c r)))) as Hclo.
    unfold cent1 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilC1 34%nat [true; true; true; true; true; false] [RVal (EVar 50%nat); RVal (EVar 55%nat)] cpins1 cvb1 v r
      [Z.ones db; A; b0; h0; n0;
       code_val (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db));
       is_have s; is_nlen s + is_ndist s; is_nlen s; db;
       clo (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f96c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: c1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTC1H" G end.
    exists R1. split; [by_run Hms|].
    cj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma cl_step_E : forall r R M,
    LMEM v (mkW s c r) M -> CJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    code_bits (cent1 (ir_hold (pull1 c r))) <= ir_bits r + 8 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f96c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f9d8) M s6u_rom)
               /\ CJE (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    c1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (cent1 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (cent1 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (cent1 (ir_hold (pull1 c r)))) as Hclo.
    unfold cent1 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilC1 34%nat [true; true; true; true; true; true] [RVal (EVar 50%nat); RVal (EVar 55%nat)] cpins1 cvb1 v r
      [Z.ones db; A; b0; h0; n0;
       code_val (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db));
       is_have s; is_nlen s + is_ndist s; is_nlen s; db;
       clo (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f96c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: c1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTC1E" G end.
    exists R1. split; [by_run Hms|].
    cj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma cl_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> CJS r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f96c) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    c1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilC1 14%nat [false] [RVal (EVar 50%nat); RVal (EVar 35%nat)] cpins1
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 2 ^ 64);
       (51%nat, 2 ^ 32); (52%nat, 2 ^ 32); (53%nat, 2 ^ 31); (54%nat, 16)] v r
      [Z.ones db; A; b0; h0; n0; ir_ret r mod 2 ^ 64; is_have s; is_nlen s + is_ndist s; is_nlen s; db] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f96c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTC1D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite (Hfr (23%bv : reg) eq_refl); rewrite G24; rewrite Hh; reflexivity
               | rewrite G18'; f_equal; clear - Ib Hh; lia
               | rewrite G25'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite G26'; apply zw_neg_mod
               | exact G13' | exact G11'
               | lazymatch goal with |- getr _ ?n = _ => let G := fresh in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | rewrite Hh; reflexivity] end
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End CodeL1.
End FXG.
End InflA_Codelens1.
Export InflA_Codelens1.

Module InflA_Codelens2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition ilCN : cfg := ilSx [0x1fa68; 0x1fac0; 0x1fb18; 0x1fb6c; 0x1fba0; 0x1fc04] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section NeedLoops.
  Variable v : icv.
  Variables (s : inflate_state).
  Hypothesis C : ictx v.
  Variables (n hb chi h0 n0 : Z).
  Hypothesis Hn : 0 < n <= 56.
  Hypothesis Hhb : 0 <= hb <= 15.
  Hypothesis Hchi : 0 <= chi < 2 ^ 24.
  Hypothesis Hn0 : 0 <= n0.

  Definition NK (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 16 = zw (is_have s) /\ getr R 11 = zw (is_nlen s + is_ndist s) /\ getr R 12 = zw (is_nlen s) /\ getr R 13 = zw (is_lenbits s)
    /\ getr R 15 = zw (Z.ones (is_lenbits s)) /\ getr R 14 = zw (ctab6 v (is_lencode s)) /\ getr R 21 = zw 1
    /\ getr R 30 = zw hb /\ getr R 31 = zw n /\ getr R 29 = zw chi
    /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 6 = zw h0.
  Definition NJS (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    NK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 5 = zw (ir_bits r) /\ getr R 7 = zw (ir_bits r)
    /\ getr R 23 = zw (ir_have r) /\ getr R 19 = zw (cv_I0 v + ir_next r) /\ getr R 28 = zw (cv_I0 v + ir_next r)
    /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition NJE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    NK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 5 = zw (ir_bits r)
    /\ getr R 23 = zw (ir_have r) /\ getr R 17 = zw (cv_I0 v + ir_next r).

  Ltac open_njs HJ :=
    let X := fresh in pose proof HJ as X; unfold NJS, NK in X;
    destruct X as ((HF & G9 & G16 & G11 & G12 & G13 & G15 & G14 & G20 & G30 & G31 & G29 & G25 & G6) & G22 & G5 & G7 & G24 & G18 & G28 & In & Ih); open_fixc HF.

  Definition npins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (16, EVar 45%nat); (11, EVar 46%nat); (12, EVar 47%nat); (13, EVar 48%nat); (15, EVar 49%nat); (14, EVar 50%nat); (21, ELit 1);
     (30, EVar 51%nat); (31, EVar 52%nat); (29, EVar 53%nat); (26, EAdd (EVar 43%nat) (EVar 55%nat)); (6, EVar 54%nat);
     (25, EVar 40%nat); (5, EVar 41%nat); (7, EVar 41%nat); (23, EVar 36%nat);
     (19, EAdd (EVar 43%nat) (EVar 44%nat)); (28, EAdd (EVar 43%nat) (EVar 44%nat))].
  Definition nvb : list (nat * Z) :=
    [(45%nat, 2 ^ 32); (46%nat, 2 ^ 32); (47%nat, 2 ^ 31); (48%nat, 16); (49%nat, 2 ^ 15); (50%nat, 2 ^ 63); (51%nat, 16); (52%nat, 64);
     (53%nat, 2 ^ 24); (54%nat, 2 ^ 31); (55%nat, 2 ^ 31)].

  Hypothesis Hhv : 0 <= is_have s < 2 ^ 32.
  Hypothesis Hnd : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31.
  Hypothesis Hlb : 1 <= is_lenbits s <= 15.
  Hypothesis HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63.

  Ltac njs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let Q24 := fresh in let Q22 := fresh in let Q5 := fresh in let Q7 := fresh in let Q18 := fresh in let Q28 := fresh in let Q17 := fresh in
    symex_reg HR (23%bv : reg) as Q24; symex_reg HR (25%bv : reg) as Q22; symex_reg HR (5%bv : reg) as Q5; symex_reg HR (7%bv : reg) as Q7;
    symex_reg HR (19%bv : reg) as Q18; symex_reg HR (28%bv : reg) as Q28; symex_reg HR (17%bv : reg) as Q17;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold NJS, NJE, NK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?k = _ => rewrite (Hfr k eq_refl); assumption end
          | rewrite Q24; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q22; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q7; f_equal; lia
          | rewrite Q18; f_equal; lia
          | rewrite Q28; f_equal; lia
          | rewrite Q17; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "NJS LEFT" G end ].

  Lemma cn17_step_H : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa68) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fa68) M s6u_rom) /\ NJS c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 17%nat [true; true; true; true] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fa68) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTNH" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn17_step_E : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa68) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fb6c) M s6u_rom) /\ NJE c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 18%nat [true; true; true; false] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fa68) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTNE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn17_dry : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa68) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones. open_retc HRC.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 11%nat [false] [RVal (EVar 56%nat); RVal (EVar 35%nat)] npins
      (nvb ++ [(56%nat, 2 ^ 64)]) v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fa68) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTND" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr;
      first [ rewrite (Hfr (23%bv : reg) eq_refl); rewrite G24; rewrite Hh; reflexivity
            | exact G18'
            | rewrite G25'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
            | rewrite G26'; apply zw_neg_mod
            | exact G13' | exact G11'
            | assumption
            | match goal with |- ?G => idtac "NDRY LEFT" G end ].
  Qed.

  Lemma cn16_step_H : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fac0) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fac0) M s6u_rom) /\ NJS c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 17%nat [true; true; true; true] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fac0) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTNH" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn16_step_E : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fac0) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fba0) M s6u_rom) /\ NJE c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 18%nat [true; true; true; false] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fac0) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTNE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn16_dry : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fac0) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones. open_retc HRC.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 11%nat [false] [RVal (EVar 56%nat); RVal (EVar 35%nat)] npins
      (nvb ++ [(56%nat, 2 ^ 64)]) v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fac0) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTND" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr;
      first [ rewrite (Hfr (23%bv : reg) eq_refl); rewrite G24; rewrite Hh; reflexivity
            | exact G18'
            | rewrite G25'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
            | rewrite G26'; apply zw_neg_mod
            | exact G13' | exact G11'
            | assumption
            | match goal with |- ?G => idtac "NDRY LEFT" G end ].
  Qed.

  Lemma cn18_step_H : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fb18) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fb18) M s6u_rom) /\ NJS c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 17%nat [true; true; true; true] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fb18) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTNH" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn18_step_E : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fb18) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fc04) M s6u_rom) /\ NJE c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 18%nat [true; true; true; false] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fb18) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTNE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn18_dry : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1fb18) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones. open_retc HRC.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilCN 11%nat [false] [RVal (EVar 56%nat); RVal (EVar 35%nat)] npins
      (nvb ++ [(56%nat, 2 ^ 64)]) v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; chi; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fb18) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTND" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr;
      first [ rewrite (Hfr (23%bv : reg) eq_refl); rewrite G24; rewrite Hh; reflexivity
            | exact G18'
            | rewrite G25'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
            | rewrite G26'; apply zw_neg_mod
            | exact G13' | exact G11'
            | assumption
            | match goal with |- ?G => idtac "NDRY LEFT" G end ].
  Qed.
End NeedLoops.
End FXG.
End InflA_Codelens2.
Export InflA_Codelens2.

Module InflA_Codelens3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Lemma le8_eqm : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_le_bytes 8 a = Z_to_le_bytes 8 b.
Proof.
  intros a b H. rewrite <- (SymExec.Z_to_le_bytes_mod 8 a), <- (SymExec.Z_to_le_bytes_mod 8 b). change (8 * Z.of_nat 8) with 64. rewrite H. reflexivity.
Qed.
Lemma cell_nlens : forall M (a S : Z), cell s6u_segs M a 8 (- (S + 169)) -> cell s6u_segs M a 8 (18446744073709551447 - S).
Proof.
  intros M a S H. unfold cell in *. rewrite H. f_equal. apply le8_eqm.
  replace (18446744073709551447 - S) with (- (S + 169) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition ilCF : cfg := ilSx [0x1fc48; 0x1fc78; 0x1f8f0; 0x1fc88] [].

Section Fill.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma cl_fill : forall k s c r R M h tgt len,
    Z.of_nat k = tgt - h -> 0 < tgt - h -> 0 <= h -> tgt <= 320 -> 0 <= len < 65536 -> arr_len (is_lens s) = 320 ->
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    getr R 2 = zw (cv_sp v - 256) -> getr R 8 = zw (cv_S v) ->
    getr R 16 = zw h -> getr R 5 = zw (tgt - h) -> getr R 6 = zw len -> getr R 7 = zw 320 ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fc48) M s6u_rom) (mkst R' (Z_to_bv 64 0x1fc78) M' s6u_rom)
      /\ LMEM v (mkW (iset_lens s (fillk (is_lens s) h k len)) c r) M'
      /\ getr R' 16 = zw tgt
      /\ (forall rg, reg_in rg [5; 16; 28; 29]%bv = false -> getr R' rg = getr R rg)
      /\ MFRAME v (ir_put r) (ir_put r) M M'
      /\ (forall w0, RETC v w0 M -> RETC v w0 M').
  Proof.
    induction k as [|k IH]; intros s c r R M h tgt len Hk Hpos Hh Htgt Hlen Halen HM Hput G2 G27 G16 G5 G6 G7; [lia|].
    open_ictx C. open_lmem HM. open_frame Mfr. unfold mapped in *.
    pose proof (cell_nlens _ _ _ Fnlens) as Fnl. clear Fnlens.
    destruct (Z.eq_dec (h + 1) tgt) as [Elast|Nlast].
    -
      assert (K0 : k = 0%nat) by lia. subst k.
      symex s6u_segs ilCF 12%nat [true; true; false] [RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        [(2, EVar 32%nat); (8, EVar 33%nat); (16, EVar 34%nat); (5, ESub (EVar 35%nat) (EVar 34%nat)); (6, EVar 36%nat); (7, ELit 320)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 512); (35%nat, 512); (36%nat, 65536)]
        NoRegions [cv_sp v - 256; cv_S v; h; tgt; len] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1fc48) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTF1" G end.
      set (M1 := wbytes M (zw (cv_S v + h * 2 ^ 1 + 168)) (Z_to_le_bytes 2 len)) in *.
      assert (HM1 : LMEM v (mkW (iset_lens s (arr_set (is_lens s) h (wrap16 len))) c r) M1).
      { subst M1. replace (zw (cv_S v + h * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * h)) by (f_equal; lia).
        apply (LMEM_store_lens v C s c r M h len len HM Hput); [lia | exact Halen | apply le2_wrap16]. }
      exists R', M1. split; [subst M1; by_run Hms|].
      split; [cbn [fillk]; exact HM1|].
      symex_reg HR' (16%bv : reg) as Q16. split; [rewrite Q16; rewrite ?szwrap32_small by lia; f_equal; lia|]. split; [fr_weak Hfr|].
      subst M1. split.
      { apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS Hh; lia | clear - CS Hh Htgt Hpos; cbn; lia | right; left; clear - Hh Htgt Hpos; cbn; lia]. }
      intros w0 H0. apply (RETC_other v C); [exact H0 | clear - CS Hh; lia | clear - CS Hh Htgt Hpos; cbn; lia | unfold sep in CfS; clear - CfS CS Hh Htgt Hpos; cbn; lia].
    -
      symex s6u_segs ilCF 12%nat [true; true; true] [RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        [(2, EVar 32%nat); (8, EVar 33%nat); (16, EVar 34%nat); (5, ESub (EVar 35%nat) (EVar 34%nat)); (6, EVar 36%nat); (7, ELit 320)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 512); (35%nat, 512); (36%nat, 65536)]
        NoRegions [cv_sp v - 256; cv_S v; h; tgt; len] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1fc48) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTF2" G end.
      set (M1 := wbytes M (zw (cv_S v + h * 2 ^ 1 + 168)) (Z_to_le_bytes 2 len)) in *.
      set (s1 := iset_lens s (arr_set (is_lens s) h (wrap16 len))).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { subst M1 s1. replace (zw (cv_S v + h * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * h)) by (f_equal; lia).
        apply (LMEM_store_lens v C s c r M h len len HM Hput); [lia | exact Halen | apply le2_wrap16]. }
      symex_reg HR1 (16%bv : reg) as Q16. rewrite ?szwrap32_small in Q16 by lia.
      symex_reg HR1 (5%bv : reg) as Q5. rewrite ?szwrap32_small in Q5 by lia.
      destruct (IH s1 c r R1 M1 (h + 1) tgt len ltac:(lia) ltac:(lia) ltac:(lia) Htgt Hlen ltac:(subst s1; cbn; rewrite arr_len_set; exact Halen) HM1 Hput
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G27)
                  ltac:(rewrite Q16; f_equal; lia) ltac:(rewrite Q5; f_equal; lia) ltac:(rewrite (Hfr1 (6%bv : reg) eq_refl); exact G6) ltac:(rewrite (Hfr1 (7%bv : reg) eq_refl); exact G7))
        as (R' & M' & Hms2 & HM' & Q16' & Hfr' & MF' & RC').
      exists R', M'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      split; [subst s1; cbn [fillk]; replace (is_lens (iset_lens s (arr_set (is_lens s) h (wrap16 len)))) with (arr_set (is_lens s) h (wrap16 len)) in HM' by (destruct s; reflexivity);
              replace (iset_lens (iset_lens s (arr_set (is_lens s) h (wrap16 len))) (fillk (arr_set (is_lens s) h (wrap16 len)) (h + 1) k len))
                with (iset_lens s (fillk (arr_set (is_lens s) h (wrap16 len)) (h + 1) k len)) in HM' by (destruct s; reflexivity); exact HM'|].
      split; [exact Q16'|]. split.
      { intros rg Hrg. rewrite (Hfr' rg Hrg). apply Hfr1. exact Hrg. }
      subst M1. split.
      { apply (MFRAME_trans v (ir_put r) (ir_put r) (ir_put r) M (wbytes M (zw (cv_S v + h * 2 ^ 1 + 168)) (Z_to_le_bytes 2 len)) M'); [| exact MF'].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS Hh; lia | clear - CS Hh Htgt Hpos; cbn; lia | right; left; clear - Hh Htgt Hpos; cbn; lia]. }
      intros w0 H0. apply RC'. apply (RETC_other v C); [exact H0 | clear - CS Hh; lia | clear - CS Hh Htgt Hpos; cbn; lia | unfold sep in CfS; clear - CfS CS Hh Htgt Hpos; cbn; lia].
  Qed.
End Fill.


Section BodyRegs.
  Variable v : icv.
  Definition BKc (s : inflate_state) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 11 = zw (is_nlen s + is_ndist s) /\ getr R 12 = zw (is_nlen s) /\ getr R 13 = zw (is_lenbits s)
    /\ getr R 15 = zw (Z.ones (is_lenbits s)) /\ getr R 14 = zw (ctab6 v (is_lencode s)).
  Definition KREG (s : inflate_state) (r : iregs) (len copy : Z) (R : bvmap 5 word) : Prop :=
    BKc s r R /\ getr R 16 = zw (is_have s) /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r) /\ getr R 23 = zw (ir_have r)
    /\ getr R 17 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw len /\ getr R 5 = zw copy.
  Definition WREG (s : inflate_state) (r : iregs) (R : bvmap 5 word) : Prop :=
    BKc s r R /\ getr R 16 = zw (is_have s) /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r) /\ getr R 23 = zw (ir_have r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 17 = zw (cv_I0 v + ir_next r) /\ getr R 31 = zw (ir_have r).

  Definition foot_pc (s : inflate_state) : Z := if is_have s <? is_nlen s + is_ndist s then 0x1f8f0 else 0x1fc88.

  Definition body_post (w : iw) (M : word -> option byte) (res : ares bool) (R' : bvmap 5 word) (M' : word -> option byte) (pc' : Z) : Prop :=
    match res with
    | ARun true w' => pc' = foot_pc (w_s w') /\ WREG (w_s w') (w_r w') R' /\ LMEM v w' M' /\ RETC v w' M' /\ LX v w'
                      /\ same_blocks (w_s w) (w_s w') /\ MFRAME v (ir_put (w_r w)) (ir_put (w_r w')) M M'
    | ARun false w' => arm_post v w M (ARun tt w') R' M' pc' /\ is_mode (w_s w') = BAD
    | ALeave w' => arm_post v w M (ALeave w') R' M' pc'
    | ARet _ _ => False
    end.
End BodyRegs.

Section Tail.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition kpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (19, EVar 41%nat); (23, EVar 36%nat); (17, EAdd (EVar 43%nat) (EVar 44%nat));
     (11, EVar 46%nat); (12, EVar 47%nat); (13, EVar 48%nat); (15, EVar 49%nat); (14, EVar 50%nat);
     (16, EVar 45%nat); (6, EVar 51%nat); (5, EVar 52%nat)].
  Definition kvb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 2 ^ 32); (47%nat, 2 ^ 31); (48%nat, 16); (49%nat, 2 ^ 15); (50%nat, 2 ^ 63); (51%nat, 65536); (52%nat, 256)].

  Lemma cl_tail : forall s c r R M len copy,
    is_mode s = CODELENS -> KREG v s r len copy R ->
    0 <= is_have s <= is_nlen s + is_ndist s -> 0 <= is_nlen s /\ 0 <= is_ndist s /\ is_nlen s + is_ndist s <= 320 -> arr_len (is_lens s) = 320 ->
    1 <= copy <= 138 -> 0 <= len < 65536 -> 1 <= is_lenbits s <= 15 -> 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63 ->
    RINV (cv_NI v) (cv_NO v) r -> LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fc2c) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ body_post v (mkW s c r) M (cb_fin s c r len copy) R' M' pc'.
  Proof.
    intros s c r R M len copy Hmode HK Hh0 Hnd Halen Hcopy Hlen Hlb HA RI HM HRC HX.
    destruct HK as ((HF & G9 & G11 & G12 & G13 & G15 & G14) & G16 & G22 & G18 & G24 & G17 & G6 & G5). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G24 as P24.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    unfold cb_fin.
    destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + copy)) as [BAD'|OK].
    -
      arm_symexP (@nil (Z * expr)) ilCF 14%nat [false] [RVal (EVar 35%nat)] kpins kvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); len; copy] NoVals F0
        (mkst R (Z_to_bv 64 0x1fc2c) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTT1" G end.
      set (c' := icset_msg c MSG_invalid_bit_length_repeat) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66234)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (HM1 : LMEM v (mkW s c' r) M1) by (exact (LMEM_store_msg v C s c r M MSG_invalid_bit_length_repeat HM Hput)).
      assert (HM2 : LMEM v (mkW s' c' r) M2).
      { apply (LMEM_store_scalar v C s c' r _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_bit_length_repeat) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      arm_disp C HM2 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode s')). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms1|].
      cbn [body_post arm_post]. split; [| subst s'; reflexivity]. split; [subst s'; reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r s' c' r HX NH NB); subst s' c'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_bit_length_repeat; lia | bk_side].
        * symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (11%bv : reg) as Q11.
          unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1|]. split; [| intros _; exact G26'].
          unfold LVARS; cbn [w_r]. regs_via2 Hfr2 Hfr1; first [exact Q25 | match goal with |- ?G => idtac "T LV LEFT" G end].
      + cbn [w_r]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    -
      rewrite abind_run. rewrite (lens_repeat_fill (Z.to_nat copy)) by lia. rewrite aret_eq.
      arm_symexP (@nil (Z * expr)) ilCF 8%nat [true; false] (@nil (option expr)) kpins kvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); len; copy] NoVals F0
        (mkst R (Z_to_bv 64 0x1fc2c) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTT2" G end.
      symex_reg HR1 (7%bv : reg) as Q7.
      destruct (cl_fill v C (Z.to_nat copy) s c r R1 M (is_have s) (is_have s + copy) len ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hlen Halen HM Hput
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G27)
                  ltac:(rewrite (Hfr1 (16%bv : reg) eq_refl); exact G16) ltac:(rewrite (Hfr1 (5%bv : reg) eq_refl); rewrite G5; f_equal; lia) ltac:(rewrite (Hfr1 (6%bv : reg) eq_refl); exact G6) Q7)
        as (R2 & M2 & Hms2 & HM2 & Q16' & Hfr2 & MF2 & RC2).
      set (sL := iset_lens s (fillk (is_lens s) (is_have s) (Z.to_nat copy) len)) in *.
      clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mleftc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W. open_lmem HM2. unfold mapped in *.
      assert (P16 : getr R2 16 = zw (is_have s + copy)) by exact Q16'.
      assert (P11 : getr R2 11 = zw (is_nlen s + is_ndist s)) by (rewrite (Hfr2 (11%bv : reg) eq_refl), (Hfr1 (11%bv : reg) eq_refl); exact G11).
      destruct (Z.ltb_spec (is_have s + copy) (is_nlen s + is_ndist s)) as [MORE|DONE].
      + arm_symexP (@nil (Z * expr)) ilCF 6%nat [true] (@nil (option expr))
          [(2, EVar 32%nat); (8, EVar 33%nat); (16, EVar 45%nat); (11, EVar 46%nat); (17, EAdd (EVar 43%nat) (EVar 44%nat)); (23, EVar 36%nat)]
          [(45%nat, 512); (46%nat, 2 ^ 32)] v r [is_have s + copy; is_nlen s + is_ndist s] NoVals F0
          (mkst R2 (Z_to_bv 64 0x1fc78) M2 s6u_rom) R3 HR3 Hfr3 Hms3.
        all: try (lazymatch goal with |- getr _ ?n = zw _ => first [exact P16 | exact P11 | rewrite (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption] end).
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTT3" G end.
        all: cycle 1.
        set (M3 := wbytes M2 (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + copy))) in *.
        set (s3 := iset_have sL (is_have s + copy)) in *.
        assert (HM3 : LMEM v (mkW s3 c r) M3).
        { apply (LMEM_store_scalar v C sL c r _ M2 156 _ HM2); [lia | cbn; lia | exact Hput | | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity].
          apply (is6_upd_have M2 (cv_S v) _ sL _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R3, M3, 0x1f8f0. split.
        { eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | subst M3; by_run Hms3]]. by_run Hms1. }
        cbn [body_post w_s w_r w_c]. split; [subst s3 sL; unfold foot_pc; destruct s; cbn in MORE |- *; replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; exact MORE); reflexivity|].
        assert (HRC3 : RETC v (mkW s3 c r) M3).
        { subst M3. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
          apply (RETC_regs v (mkW s c r)); [exact (RC2 _ HRC) | reflexivity]. }
        assert (HX3 : LX v (mkW s3 c r)) by (apply (LX_step0 v s c r s3 c r HX NH NB); subst s3 sL; try (destruct s; reflexivity); [destruct s; cbn in Hmode |- *; rewrite Hmode; live_mode_tac | exact Xret | exact Xmsg | destruct s; cbn in Hmode |- *; bk_side]).
        split; [| split; [exact HM3 | split; [exact HRC3 | split; [exact HX3 | split; [subst s3 sL; destruct s; split; [reflexivity | split; reflexivity] |]]]]].
        * symex_reg HR3 (26%bv : reg) as Q25. symex_reg HR3 (31%bv : reg) as Q31.
          unfold WREG, BKc. subst s3 sL. cbn -[zw Z.add Z.mul Z.ones ctab6 getr cv_P0 cv_I0 cv_S cv_sp Z.sub Z.pow Z.opp].
          repeat match goal with |- _ /\ _ => split end;
            first [ exact Q25 | exact Q31
                  | lazymatch goal with |- LFIXc _ _ => unfold LFIXc, INF_FRAME; repeat match goal with |- _ /\ _ => split end;
                        (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl), (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption end) end
                  | rewrite (Hfr3 (16%bv : reg) eq_refl); rewrite P16; destruct s; reflexivity
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl), (Hfr2 n eq_refl), (Hfr1 n eq_refl); first [assumption | destruct s; assumption] end
                  | match goal with |- ?G => idtac "WREG LEFT" G end ].
        * subst M3. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M2); [exact MF2 | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      + arm_symexP (@nil (Z * expr)) ilCF 6%nat [false] (@nil (option expr))
          [(2, EVar 32%nat); (8, EVar 33%nat); (16, EVar 45%nat); (11, EVar 46%nat); (17, EAdd (EVar 43%nat) (EVar 44%nat)); (23, EVar 36%nat)]
          [(45%nat, 512); (46%nat, 2 ^ 32)] v r [is_have s + copy; is_nlen s + is_ndist s] NoVals F0
          (mkst R2 (Z_to_bv 64 0x1fc78) M2 s6u_rom) R3 HR3 Hfr3 Hms3.
        all: try (lazymatch goal with |- getr _ ?n = zw _ => first [exact P16 | exact P11 | rewrite (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption] end).
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTT4" G end.
        set (M3 := wbytes M2 (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + copy))) in *.
        set (s3 := iset_have sL (is_have s + copy)) in *.
        assert (HM3 : LMEM v (mkW s3 c r) M3).
        { apply (LMEM_store_scalar v C sL c r _ M2 156 _ HM2); [lia | cbn; lia | exact Hput | | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity].
          apply (is6_upd_have M2 (cv_S v) _ sL _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R3, M3, 0x1fc88. split.
        { eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | subst M3; by_run Hms3]]. by_run Hms1. }
        cbn [body_post w_s w_r w_c]. split; [subst s3 sL; unfold foot_pc; destruct s; cbn in DONE |- *; replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; exact DONE); reflexivity|].
        assert (HRC3 : RETC v (mkW s3 c r) M3).
        { subst M3. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
          apply (RETC_regs v (mkW s c r)); [exact (RC2 _ HRC) | reflexivity]. }
        assert (HX3 : LX v (mkW s3 c r)) by (apply (LX_step0 v s c r s3 c r HX NH NB); subst s3 sL; try (destruct s; reflexivity); [destruct s; cbn in Hmode |- *; rewrite Hmode; live_mode_tac | exact Xret | exact Xmsg | destruct s; cbn in Hmode |- *; bk_side]).
        split; [| split; [exact HM3 | split; [exact HRC3 | split; [exact HX3 | split; [subst s3 sL; destruct s; split; [reflexivity | split; reflexivity] |]]]]].
        * symex_reg HR3 (26%bv : reg) as Q25. symex_reg HR3 (31%bv : reg) as Q31.
          unfold WREG, BKc. subst s3 sL. cbn -[zw Z.add Z.mul Z.ones ctab6 getr cv_P0 cv_I0 cv_S cv_sp Z.sub Z.pow Z.opp].
          repeat match goal with |- _ /\ _ => split end;
            first [ exact Q25 | exact Q31
                  | lazymatch goal with |- LFIXc _ _ => unfold LFIXc, INF_FRAME; repeat match goal with |- _ /\ _ => split end;
                        (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl), (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption end) end
                  | rewrite (Hfr3 (16%bv : reg) eq_refl); rewrite P16; destruct s; reflexivity
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl), (Hfr2 n eq_refl), (Hfr1 n eq_refl); first [assumption | destruct s; assumption] end
                  | match goal with |- ?G => idtac "WREG LEFT" G end ].
        * subst M3. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M2); [exact MF2 | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End Tail.
End FXG.
End InflA_Codelens3.
Export InflA_Codelens3.


