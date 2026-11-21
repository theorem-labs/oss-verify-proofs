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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Len3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflMem2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InffastSafe IfSpec IfSpec6 InflA_LenF.

Module InflArmLib6e.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

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
      pose proof (cells_write_cell s6_segs M (cv_S v + 168) 2 2%nat 320 (arr_get (is_lens s)) i (wrap16 b) Mlens ltac:(cbn; lia) Hi ltac:(clear - CS; lia) ltac:(clear - CS; lia) j Hj) as X.
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
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


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
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pcH) M s6_rom)
               /\ JS c (pull1 c r) R1.
  Hypothesis STEP_E : forall c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pcE) M s6_rom)
               /\ JE c (pull1 c r) R1.
  Hypothesis DRY : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.

  Lemma need_loop_s : forall k c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV NI NO r -> CINV NI NO c ->
    ir_bits r < n -> n <= ir_bits r + 8 * Z.of_nat k ->
    match NEEDBITS_k k n (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pcE) M s6_rom)
        /\ JE c r1 R1 /\ RINV NI NO r1 /\ same5 r r1 /\ n <= ir_bits r1 < n + 8
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 pcH) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
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
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilC1 : cfg := ilSx [0x1d760; 0x1d7b0] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

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
    (getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 10 = zw (cv_ZP v) /\ getr R 11 = zw (cv_flush v)
     /\ getr R 22 = zw (cv_S v + 168) /\ getr R 31 = zw (-16180) /\ getr R 20 = zw 16209 /\ getr R 25 = zw A6_JTAB
     /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4)
    /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 13 = zw (is_have s) /\ getr R 14 = zw (is_nlen s + is_ndist s) /\ getr R 12 = zw (is_nlen s)
    /\ getr R 24 = zw b0 /\ getr R 6 = zw h0 /\ getr R 7 = zw (cv_I0 v + n0)
    /\ getr R 16 = zw (Z.ones db) /\ getr R 15 = zw A.
  Definition CJS (r : iregs) (R : bvmap 5 word) : Prop :=
    CK r R /\ getr R 23 = zw (ir_hold r) /\ getr R 18 = zw (ir_have r) /\ getr R 30 = zw (cv_I0 v + ir_next r) /\ getr R 27 = zw (cv_I0 v + ir_next r)
    /\ getr R 29 = zw (ir_bits r) /\ getr R 17 = zw (ir_bits r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition CJE (r : iregs) (R : bvmap 5 word) : Prop :=
    CK r R /\ getr R 23 = zw (ir_hold r) /\ getr R 18 = zw (ir_have r) /\ getr R 27 = zw (cv_I0 v + ir_next r)
    /\ getr R 17 = zw (ir_bits r) /\ getr R 29 = zw 30
    /\ getr R 28 = zw (BITSv (ir_hold r) db) /\ getr R 5 = zw (code_bits (cent1 (ir_hold r))).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold CJS, CK in X;
    destruct X as (((G2 & G25 & G10 & G11 & G21 & G31 & G19 & G24 & G3 & G4) & G18 & G1 & G13 & G14 & G12 & G23 & G6 & G7 & G16 & G15) & G22 & G9 & G30 & G26 & G29 & G17 & Ib & In & Ih);
    unfold INF_FRAME in G2.

  Definition cpins1 : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (20, ELit 16209); (25, ELit 0x12510);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (18, EVar 36%nat); (30, EAdd (EVar 43%nat) (EVar 44%nat)); (27, EAdd (EVar 43%nat) (EVar 44%nat)); (29, EVar 41%nat); (17, EVar 41%nat);
     (16, EVar 45%nat); (15, EVar 46%nat);
     (24, EVar 47%nat); (6, EVar 48%nat); (7, EAdd (EVar 43%nat) (EVar 49%nat));
     (13, EVar 51%nat); (14, EVar 52%nat); (12, EVar 53%nat)].
  Definition cvb1 : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 256); (51%nat, 2 ^ 32); (52%nat, 2 ^ 32); (53%nat, 2 ^ 32)].

  Ltac c1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext :=
    cbn [famA]; rewrite ?bmod_get by exact Hby;
    rewrite ?idx1_exec by (first [exact Rhold | exact Hby | clear - Rbits Hb64 Rt1; lia]);
    lazymatch goal with
    | |- exists bs, rdn _ _ _ _ = Some bs /\ _ => match goal with |- context [BITSv ?h ?n] => tab_read TAB (BITSv h n); pose proof (BITSv_bound h n ltac:(lia)); lia end
    | |- 0 <= _ /\ _ <= 2 ^ 64 => match goal with |- context [BITSv ?h ?n] => generalize (BITSv_bound h n ltac:(lia)); clear - HA0 HA1 Hext Rt2; intro; lia end
    | |- _ => idtac
    end.

  Ltac cj_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 :=
    let Q23 := fresh in let Q24 := fresh in let Q30 := fresh in let Q26 := fresh in let Q29 := fresh in let Q17 := fresh in
    let Q28 := fresh in let Q5 := fresh in
    symex_reg HR (23%bv : reg) as Q23; symex_reg HR (18%bv : reg) as Q24; symex_reg HR (30%bv : reg) as Q30; symex_reg HR (27%bv : reg) as Q26;
    symex_reg HR (29%bv : reg) as Q29; symex_reg HR (17%bv : reg) as Q17; symex_reg HR (28%bv : reg) as Q28; symex_reg HR (5%bv : reg) as Q5;
    cbn [famA] in Q23, Q28; rewrite ?bmod_get in Q23, Q28 by exact Hby;
    unfold CJS, CJE, CK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q23; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q24; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q30; f_equal; lia
          | rewrite Q26; f_equal; lia
          | rewrite Q29; f_equal; lia
          | rewrite Q17; rewrite ?szwrap32_small by (clear - Rbits Hb64; lia); f_equal; lia
          | rewrite Q28; rewrite idx1_exec; [f_equal; lia | clear - Rbits; lia | clear - Hb64; lia | exact Rhold | exact Hby | lia]
          | rewrite Q5; reflexivity
          | lia
          | match goal with |- ?G => idtac "CJ LEFT" G end ].

  Lemma cl_step_H : forall r R M,
    LMEM v (mkW s c r) M -> CJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < code_bits (cent1 (ir_hold (pull1 c r))) ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d760) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d760) M s6_rom)
               /\ CJS (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hofs) as TAB.
    pose proof (ones_range15 db Rt1) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (cent1 (ir_hold (pull1 c r)))) as Hcb.
    unfold cent1 in Hb, Hcb |- *. cbn [ir_hold pull1] in Hb, Hcb |- *.
    arm_symexP (@nil (Z * expr)) ilC1 16%nat [true; true] [RVal (EVar 50%nat)] cpins1 cvb1 v r
      [Z.ones db; A; b0; h0; n0; code_bits (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db)); is_have s; is_nlen s + is_ndist s; is_nlen s]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d760) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: c1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTC1H" G end.
    exists R1. split; [by_run Hms|].
    cj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma cl_step_E : forall r R M,
    LMEM v (mkW s c r) M -> CJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    code_bits (cent1 (ir_hold (pull1 c r))) <= ir_bits r + 8 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d760) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d7b0) M s6_rom)
               /\ CJE (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_lencode s) C HM Hofs) as TAB.
    pose proof (ones_range15 db Rt1) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (cent1 (ir_hold (pull1 c r)))) as Hcb.
    unfold cent1 in Hb, Hcb |- *. cbn [ir_hold pull1] in Hb, Hcb |- *.
    arm_symexP (@nil (Z * expr)) ilC1 20%nat [true; false] [RVal (EVar 50%nat); RVal (ELit 75024)] cpins1 cvb1 v r
      [Z.ones db; A; b0; h0; n0; code_bits (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db)); is_have s; is_nlen s + is_ndist s; is_nlen s]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d760) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: c1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTC1E" G end.
    exists R1. split; [by_run Hms|].
    cj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma cl_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> CJS r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d760) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 db Rt1) as Hones.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilC1 14%nat [false] [RVal (EVar 50%nat)] cpins1
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 2 ^ 64); (51%nat, 2 ^ 32); (52%nat, 2 ^ 32); (53%nat, 2 ^ 32)] v r
      [Z.ones db; A; b0; h0; n0; ir_ret r mod 2 ^ 64; is_have s; is_nlen s + is_ndist s; is_nlen s] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d760) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTC1D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'. symex_reg HR1 (18%bv : reg) as G9'. symex_reg HR1 (27%bv : reg) as G26'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite G9'; rewrite Hh; reflexivity
               | rewrite (Hfr (18%bv : reg) eq_refl), G9, Hh; reflexivity
               | rewrite G23'; f_equal; clear - Ib Hh; lia
               | rewrite G26'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite G8'; apply zw_neg_mod
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End CodeL1.
End FXG.
End InflA_Codelens1.
Export InflA_Codelens1.

Module InflA_Codelens2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilCN : cfg := ilSx [0x1d804; 0x1d840; 0x1d87c; 0x1d8b0; 0x1d8d4; 0x1d910] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section NeedLoops.
  Variable v : icv.
  Variables (s : inflate_state).
  Hypothesis C : ictx v.
  Variables (n hb : Z).
  Hypothesis Hn : 0 < n <= 56.
  Hypothesis Hhb : 0 <= hb <= 15.

  Definition NK (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 13 = zw (is_have s) /\ getr R 14 = zw (is_nlen s + is_ndist s) /\ getr R 12 = zw (is_nlen s)
    /\ getr R 16 = zw (Z.ones (is_lenbits s)) /\ getr R 15 = zw (ctab6 v (is_lencode s))
    /\ getr R 5 = zw hb /\ getr R 6 = zw n.
  Definition NJS (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    NK r R /\ getr R 23 = zw (ir_hold r) /\ getr R 7 = zw (ir_bits r) /\ getr R 17 = zw (ir_bits r)
    /\ getr R 18 = zw (ir_have r) /\ getr R 27 = zw (cv_I0 v + ir_next r).
  Definition NJE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    NK r R /\ getr R 23 = zw (ir_hold r) /\ getr R 17 = zw (ir_bits r)
    /\ getr R 18 = zw (ir_have r) /\ getr R 27 = zw (cv_I0 v + ir_next r) /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Ltac open_njs HJ :=
    let X := fresh in pose proof HJ as X; unfold NJS, NK in X;
    destruct X as ((HF & G18 & G1 & G13 & G14 & G12 & G16 & G15 & G5 & G6) & G22 & G7 & G17 & G9 & G26); open_fix HF.

  Definition npins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (7, EVar 41%nat); (17, EVar 41%nat); (18, EVar 36%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat));
     (13, EVar 45%nat); (14, EVar 46%nat); (12, EVar 47%nat); (16, EVar 48%nat); (15, EVar 49%nat); (5, EVar 50%nat); (6, EVar 51%nat)].
  Definition nvb : list (nat * Z) :=
    [(45%nat, 2 ^ 32); (46%nat, 2 ^ 32); (47%nat, 2 ^ 32); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 64)].

  Hypothesis Hhv : 0 <= is_have s < 2 ^ 32.
  Hypothesis Hnd : 0 <= is_nlen s < 2 ^ 31 /\ 0 <= is_ndist s < 2 ^ 31.
  Hypothesis Hlb : 1 <= is_lenbits s <= 15.
  Hypothesis HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63.

  Ltac njs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let G9 := fresh in let G22 := fresh in let G7 := fresh in let G17 := fresh in let G26 := fresh in let G27 := fresh in
    symex_reg HR (18%bv : reg) as G9; symex_reg HR (23%bv : reg) as G22; symex_reg HR (7%bv : reg) as G7;
    symex_reg HR (17%bv : reg) as G17; symex_reg HR (27%bv : reg) as G26; symex_reg HR (26%bv : reg) as G27;
    cbn [famA] in G22; rewrite bmod_get in G22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold NJS, NJE, NK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ apply (LFIX_frame v _ _ _ HF Hfr); reflexivity
          | lazymatch goal with |- getr _ ?k = _ => rewrite (Hfr k eq_refl); assumption end
          | rewrite G9; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite G22; f_equal; lia
          | rewrite G7; f_equal; lia
          | rewrite G17; f_equal; lia
          | rewrite G26; f_equal; lia
          | rewrite G27; f_equal; lia
          | match goal with |- ?G => idtac "NJS LEFT" G end ].

  Lemma cn17_step_H : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d804) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d804) M s6_rom) /\ NJS c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilCN 14%nat [true; true] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d804) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn17_step_E : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d804) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d8b0) M s6_rom) /\ NJE c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilCN 14%nat [true; false] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d804) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn17_dry : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d804) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones. open_retc HRC.
    arm_symexP (@nil (Z * expr)) ilCN 10%nat [false] [RVal (EVar 52%nat)] npins
      [(45%nat, 2 ^ 32); (46%nat, 2 ^ 32); (47%nat, 2 ^ 32); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 64); (52%nat, 2 ^ 64)] v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d804) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr; first [exact G23' | rewrite G8'; apply zw_neg_mod | assumption | match goal with |- ?G => idtac "NDRY LEFT" G end].
  Qed.

  Lemma cn16_step_H : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d840) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d840) M s6_rom) /\ NJS c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilCN 14%nat [true; true] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d840) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn16_step_E : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d840) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d8d4) M s6_rom) /\ NJE c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilCN 14%nat [true; false] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d840) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn16_dry : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d840) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones. open_retc HRC.
    arm_symexP (@nil (Z * expr)) ilCN 10%nat [false] [RVal (EVar 52%nat)] npins
      [(45%nat, 2 ^ 32); (46%nat, 2 ^ 32); (47%nat, 2 ^ 32); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 64); (52%nat, 2 ^ 64)] v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d840) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr; first [exact G23' | rewrite G8'; apply zw_neg_mod | assumption | match goal with |- ?G => idtac "NDRY LEFT" G end].
  Qed.

  Lemma cn18_step_H : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < n -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d87c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d87c) M s6_rom) /\ NJS c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilCN 14%nat [true; true] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d87c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn18_step_E : forall c r R M,
    LMEM v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> n <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d87c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d910) M s6_rom) /\ NJE c (pull1 c r) R1.
  Proof.
    intros c r R M HM HJ RI CI Hb Hb8 Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilCN 14%nat [true; false] (@nil (option expr)) npins nvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d87c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb Hn; lia).
    njs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.
  Lemma cn18_dry : forall c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> NJS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < n -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d87c) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros c r R M HM HRC HJ RI CI Hb Hh. open_njs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones. open_retc HRC.
    arm_symexP (@nil (Z * expr)) ilCN 10%nat [false] [RVal (EVar 52%nat)] npins
      [(45%nat, 2 ^ 32); (46%nat, 2 ^ 32); (47%nat, 2 ^ 32); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 64); (52%nat, 2 ^ 64)] v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; n; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d87c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (24%bv : reg) as G23'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr; first [exact G23' | rewrite G8'; apply zw_neg_mod | assumption | match goal with |- ?G => idtac "NDRY LEFT" G end].
  Qed.
End NeedLoops.
End FXG.
End InflA_Codelens2.
Export InflA_Codelens2.

Module InflA_Codelens3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma sll32_srl31 : forall h, 0 <= h < 2 ^ 31 -> (h * 2 ^ 32) mod 2 ^ 64 / 2 ^ 31 = 2 * h.
Proof.
  intros h Hh. rewrite Z.mod_small by (change (2 ^ 64) with (2 ^ 31 * 2 * 2 ^ 32); lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Definition ilCF : cfg := ilSx [0x1d938; 0x1d950; 0x1d958] [].

Section Fill.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma cl_fill : forall k s c r R M h tgt len,
    Z.of_nat k = tgt - h -> 0 < tgt - h -> 0 <= h -> tgt <= 320 -> 0 <= len < 65536 -> arr_len (is_lens s) = 320 ->
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    getr R 2 = zw (cv_sp v - 224) -> getr R 8 = zw (cv_S v) -> getr R 22 = zw (cv_S v + 168) ->
    getr R 13 = zw h -> getr R 17 = zw tgt -> getr R 6 = zw len ->
    exists R' M',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d938) M s6_rom) (mkst R' (Z_to_bv 64 0x1d950) M' s6_rom)
      /\ LMEM v (mkW (iset_lens s (fillk (is_lens s) h k len)) c r) M'
      /\ getr R' 13 = zw tgt
      /\ (forall rg, reg_in rg [5; 13]%bv = false -> getr R' rg = getr R rg)
      /\ MFRAME v (ir_put r) (ir_put r) M M'
      /\ (forall w0, RETC v w0 M -> RETC v w0 M').
  Proof.
    induction k as [|k IH]; intros s c r R M h tgt len Hk Hpos Hh Htgt Hlen Halen HM Hput G2 G25 G21 G13 G17 G6; [lia|].
    open_ictx C. open_lmem HM. unfold mapped in *.
    assert (E2h : (h * 2 ^ 32) mod 2 ^ 64 / 2 ^ 31 = 2 * h) by (apply sll32_srl31; lia).
    destruct (Z.eq_dec (h + 1) tgt) as [Elast|Nlast].
    -
      assert (K0 : k = 0%nat) by lia. subst k.
      symex s6_segs ilCF 8%nat [false] (@nil (option expr))
        [(2, EVar 32%nat); (8, EVar 33%nat); (22, EAdd (EVar 33%nat) (ELit 168)); (13, EVar 34%nat); (17, EVar 35%nat); (6, EVar 36%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 512); (35%nat, 512); (36%nat, 65536)]
        NoRegions [cv_sp v - 224; cv_S v; h; tgt; len] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1d938) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_S v + h * 2 ^ 1 + 168)) (Z_to_le_bytes 2 len)) in *.
      assert (HM1 : LMEM v (mkW (iset_lens s (arr_set (is_lens s) h (wrap16 len))) c r) M1).
      { subst M1. replace (zw (cv_S v + h * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * h)) by (f_equal; lia).
        apply (LMEM_store_lens v C s c r M h len len HM Hput); [lia | exact Halen | apply le2_wrap16]. }
      exists R', M1. split; [subst M1; by_run Hms|].
      split; [cbn [fillk]; exact HM1|].
      symex_reg HR' (13%bv : reg) as Q13. split; [rewrite Q13; f_equal; lia|]. split; [fr_weak Hfr|].
      subst M1. split.
      { apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS Hh; lia | clear - CS Hh Htgt Hpos; cbn; lia | right; left; clear - Hh Htgt Hpos; cbn; lia]. }
      intros w0 H0. apply (RETC_other v C); [exact H0 | clear - CS Hh; lia | clear - CS Hh Htgt Hpos; cbn; lia | unfold sep in CfS; clear - CfS CS Hh Htgt Hpos; cbn; lia].
    -
      symex s6_segs ilCF 8%nat [true] (@nil (option expr))
        [(2, EVar 32%nat); (8, EVar 33%nat); (22, EAdd (EVar 33%nat) (ELit 168)); (13, EVar 34%nat); (17, EVar 35%nat); (6, EVar 36%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 512); (35%nat, 512); (36%nat, 65536)]
        NoRegions [cv_sp v - 224; cv_S v; h; tgt; len] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1d938) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_S v + h * 2 ^ 1 + 168)) (Z_to_le_bytes 2 len)) in *.
      set (s1 := iset_lens s (arr_set (is_lens s) h (wrap16 len))).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { subst M1 s1. replace (zw (cv_S v + h * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * h)) by (f_equal; lia).
        apply (LMEM_store_lens v C s c r M h len len HM Hput); [lia | exact Halen | apply le2_wrap16]. }
      symex_reg HR1 (13%bv : reg) as Q13.
      destruct (IH s1 c r R1 M1 (h + 1) tgt len ltac:(lia) ltac:(lia) ltac:(lia) Htgt Hlen ltac:(subst s1; cbn; rewrite arr_len_set; exact Halen) HM1 Hput
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G25) ltac:(rewrite (Hfr1 (22%bv : reg) eq_refl); exact G21)
                  Q13 ltac:(rewrite (Hfr1 (17%bv : reg) eq_refl); exact G17) ltac:(rewrite (Hfr1 (6%bv : reg) eq_refl); exact G6))
        as (R' & M' & Hms2 & HM' & Q13' & Hfr' & MF' & RC').
      exists R', M'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      split; [subst s1; cbn [fillk]; replace (is_lens (iset_lens s (arr_set (is_lens s) h (wrap16 len)))) with (arr_set (is_lens s) h (wrap16 len)) in HM' by (destruct s; reflexivity);
              replace (iset_lens (iset_lens s (arr_set (is_lens s) h (wrap16 len))) (fillk (arr_set (is_lens s) h (wrap16 len)) (h + 1) k len))
                with (iset_lens s (fillk (arr_set (is_lens s) h (wrap16 len)) (h + 1) k len)) in HM' by (destruct s; reflexivity); exact HM'|].
      split; [exact Q13'|]. split.
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
    LFIX v R /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 14 = zw (is_nlen s + is_ndist s) /\ getr R 12 = zw (is_nlen s)
    /\ getr R 16 = zw (Z.ones (is_lenbits s)) /\ getr R 15 = zw (ctab6 v (is_lencode s)).
  Definition KREG (s : inflate_state) (r : iregs) (len copy : Z) (R : bvmap 5 word) : Prop :=
    BKc s r R /\ getr R 13 = zw (is_have s) /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r) /\ getr R 18 = zw (ir_have r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw len /\ getr R 17 = zw copy.
  Definition WREG (s : inflate_state) (r : iregs) (R : bvmap 5 word) : Prop :=
    BKc s r R /\ getr R 13 = zw (is_have s) /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r) /\ getr R 18 = zw (ir_have r)
    /\ getr R 27 = zw (cv_I0 v + ir_next r).

  Definition body_post (w : iw) (M : word -> option byte) (res : ares bool) (R' : bvmap 5 word) (M' : word -> option byte) (pc' : Z) : Prop :=
    match res with
    | ARun true w' => pc' = 0x1d958 /\ WREG (w_s w') (w_r w') R' /\ LMEM v w' M' /\ RETC v w' M' /\ LX v w'
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
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat); (24, EVar 41%nat);
     (18, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat));
     (13, EVar 45%nat); (14, EVar 46%nat); (12, EVar 47%nat); (16, EVar 48%nat); (15, EVar 49%nat); (6, EVar 50%nat); (17, EVar 51%nat)].
  Definition kvb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 65536); (51%nat, 256)].

  Lemma cl_tail : forall s c r R M len copy,
    is_mode s = CODELENS -> KREG v s r len copy R ->
    0 <= is_have s <= is_nlen s + is_ndist s -> 0 <= is_nlen s /\ 0 <= is_ndist s /\ is_nlen s + is_ndist s <= 320 -> arr_len (is_lens s) = 320 ->
    1 <= copy <= 138 -> 0 <= len < 65536 -> 1 <= is_lenbits s <= 15 -> 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63 ->
    RINV (cv_NI v) (cv_NO v) r -> LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d92c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (cb_fin s c r len copy) R' M' pc'.
  Proof.
    intros s c r R M len copy Hmode HK Hh0 Hnd Halen Hcopy Hlen Hlb HA RI HM HRC HX.
    destruct HK as ((HF & G18 & G1 & G14 & G12 & G16 & G15) & G13 & G22 & G23 & G9 & G27 & G6 & G17). open_fix HF.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    unfold cb_fin.
    destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + copy)) as [BAD'|OK].
    -
      arm_symexP (@nil (Z * expr)) ilCF 30%nat [false; true] [RVal (ELit (JT BAD))] kpins kvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); len; copy] NoVals F0
        (mkst R (Z_to_bv 64 0x1d92c) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (c' := icset_msg c MSG_invalid_bit_length_repeat) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66234)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (HM1 : LMEM v (mkW s c' r) M1) by (exact (LMEM_store_msg v C s c r M MSG_invalid_bit_length_repeat HM Hput)).
      assert (HM2 : LMEM v (mkW s' c' r) M2).
      { apply (LMEM_store_scalar v C s c' r _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_bit_length_repeat) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      exists R1, M2, (arm6_pc BAD). split; [subst M2 M1; by_run Hms1|].
      cbn [body_post arm_post]. split; [| subst s'; reflexivity]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r s' c' r HX NH NB); subst s' c'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_bit_length_repeat; lia].
        * symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (27%bv : reg) as G26'. unfold LREG_arm. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [| intros _; exact G8'].
          unfold LVARS; cbn [w_r]. regs_via Hfr1; first [exact G26' | match goal with |- ?G => idtac "T LV LEFT" G end].
      + cbn [w_r]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    -
      rewrite abind_run. rewrite (lens_repeat_fill (Z.to_nat copy)) by lia. rewrite aret_eq.
      arm_symexP (@nil (Z * expr)) ilCF 4%nat [true] (@nil (option expr)) kpins kvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); len; copy] NoVals F0
        (mkst R (Z_to_bv 64 0x1d92c) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTT2" G end.
      symex_reg HR1 (17%bv : reg) as Q17. rewrite ?szwrap32_small in Q17 by lia.
      destruct (cl_fill v C (Z.to_nat copy) s c r R1 M (is_have s) (is_have s + copy) len ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hlen Halen HM Hput
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); unfold INF_FRAME in G2; exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G25) ltac:(rewrite (Hfr1 (22%bv : reg) eq_refl); exact G21)
                  ltac:(rewrite (Hfr1 (13%bv : reg) eq_refl); exact G13) ltac:(rewrite Q17; f_equal; lia) ltac:(rewrite (Hfr1 (6%bv : reg) eq_refl); exact G6))
        as (R2 & M2 & Hms2 & HM2 & Q13' & Hfr2 & MF2 & RC2).
      set (sL := iset_lens s (fillk (is_lens s) (is_have s) (Z.to_nat copy) len)) in *.
      clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W. open_lmem HM2. unfold mapped in *.
      arm_symexP (@nil (Z * expr)) ilCF 4%nat (@nil bool) (@nil (option expr))
        [(2, EVar 32%nat); (8, EVar 33%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (13, EVar 45%nat)]
        [(45%nat, 512)] v r [is_have s + copy] NoVals F0
        (mkst R2 (Z_to_bv 64 0x1d950) M2 s6_rom) R3 HR3 Hfr3 Hms3.
      all: try (lazymatch goal with |- getr _ ?n = zw _ => first [exact Q13' | rewrite (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption] end).
      all: try arm_side.
      set (M3 := wbytes M2 (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + copy))) in *.
      set (s3 := iset_have sL (is_have s + copy)) in *.
      assert (HM3 : LMEM v (mkW s3 c r) M3).
      { apply (LMEM_store_scalar v C sL c r _ M2 156 _ HM2); [lia | cbn; lia | exact Hput | | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity | subst s3 sL; destruct s; reflexivity].
        apply (is6_upd_have M2 (cv_S v) _ sL _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R3, M3, 0x1d958. split.
      { eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | subst M3; by_run Hms3]]. by_run Hms1. }
      cbn [body_post w_s w_r w_c]. split; [reflexivity|].
      assert (HRC3 : RETC v (mkW s3 c r) M3).
      { subst M3. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        apply (RETC_regs v (mkW s c r)); [exact (RC2 _ HRC) | reflexivity]. }
      assert (HX3 : LX v (mkW s3 c r)) by (apply (LX_step0 v s c r s3 c r HX NH NB); subst s3 sL; try (destruct s; reflexivity); [destruct s; cbn in Hmode |- *; rewrite Hmode; live_mode_tac | exact Xret | exact Xmsg]).
      split; [| split; [exact HM3 | split; [exact HRC3 | split; [exact HX3 | split; [subst s3 sL; destruct s; split; [reflexivity | split; reflexivity] |]]]]].
      + symex_reg HR3 (27%bv : reg) as Q26.
        unfold WREG, BKc. subst s3 sL. cbn -[zw Z.add Z.mul Z.ones ctab6 getr cv_P0 cv_I0 cv_S cv_sp Z.sub Z.pow Z.opp].
        repeat match goal with |- _ /\ _ => split end;
          first [ exact Q26
                | lazymatch goal with |- LFIX _ _ => unfold LFIX, INF_FRAME, A6_JTAB; repeat match goal with |- _ /\ _ => split end;
                      (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl), (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption end) end
                | rewrite (Hfr3 (13%bv : reg) eq_refl); rewrite Q13'; destruct s; reflexivity
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl), (Hfr2 n eq_refl), (Hfr1 n eq_refl); first [assumption | destruct s; assumption] end
                | match goal with |- ?G => idtac "WREG LEFT" G end ].
      + subst M3. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M2); [exact MF2 | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End Tail.
End FXG.
End InflA_Codelens3.
Export InflA_Codelens3.

Module InflA_Codelens4.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Dist3.
Import InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Codelens2.
Import InflA_Codelens3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilCV : cfg := ilSx [0x1d7e8; 0x1d804; 0x1d840; 0x1d87c; 0x1d8b0; 0x1d8d4; 0x1d910; 0x1d958] [].

Section Split.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition JREG (s : inflate_state) (r : iregs) (idx hb : Z) (R : bvmap 5 word) : Prop :=
    BKc v s r R /\ getr R 13 = zw (is_have s) /\ getr R 23 = zw (ir_hold r) /\ getr R 18 = zw (ir_have r) /\ getr R 27 = zw (cv_I0 v + ir_next r)
    /\ getr R 17 = zw (ir_bits r) /\ getr R 28 = zw idx /\ getr R 5 = zw hb.
  Definition VREG (s : inflate_state) (r : iregs) (hb val : Z) (R : bvmap 5 word) : Prop :=
    BKc v s r R /\ getr R 13 = zw (is_have s) /\ getr R 23 = zw (ir_hold r) /\ getr R 18 = zw (ir_have r) /\ getr R 27 = zw (cv_I0 v + ir_next r)
    /\ getr R 17 = zw (ir_bits r) /\ getr R 5 = zw hb /\ getr R 6 = zw val.

  Ltac open_jreg HJ :=
    destruct HJ as ((HF & G18 & G1 & G14 & G12 & G16 & G15) & G13 & G22 & G9 & G26 & G17 & G28 & G5); open_fix HF.
  Ltac open_vreg HJ :=
    destruct HJ as ((HF & G18 & G1 & G14 & G12 & G16 & G15) & G13 & G22 & G9 & G26 & G17 & G5 & G6); open_fix HF.

  Definition jpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (18, EVar 36%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EVar 41%nat);
     (13, EVar 45%nat); (14, EVar 46%nat); (12, EVar 47%nat); (16, EVar 48%nat); (15, EVar 49%nat); (5, EVar 50%nat)].
  Definition jvb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 2 ^ 15); (52%nat, 65536)].

  Definition cb_facts (v : icv) (s : inflate_state) : Prop :=
    0 <= is_have s < is_nlen s + is_ndist s /\ 0 <= is_nlen s /\ 0 <= is_ndist s /\ is_nlen s + is_ndist s <= 320
    /\ arr_len (is_lens s) = 320 /\ 1 <= is_lenbits s <= 15 /\ is_lencode s = CDyn 0
    /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens s) i < 65536).

  Lemma cl_lit : forall s c r R M idx here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r ->
    cells s6_segs M (ctab6 v (is_lencode s)) 4 4 (cext (is_lencode s)) (cat (is_codes s) (is_lencode s)) ->
    0 <= idx < cext (is_lencode s) -> here = cat (is_codes s) (is_lencode s) idx ->
    code_bits here <= ir_bits r -> code_bits here <= 15 -> code_val here < 16 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> JREG s r idx (code_bits here) R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d7b0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ body_post v (mkW s c r) M (ARun true (mkW (cb_lit_s s here) c (cdrop r (code_bits here)))) R' M' pc'.
  Proof.
    intros s c r R M idx here Hmode HB RI TAB Hidx Ehere Hhb Hb15 Hval HM HRC HX HJ.
    destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_jreg HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 * cext (is_lencode s) < 2 ^ 63 /\ cext (is_lencode s) = 1444) by (rewrite ELC; cbn [ctab6 codeptr_addr cext]; clear - CS; lia).
    destruct HA as (HA0 & HA1 & HX1444).
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    pose proof (code_val_range here) as Hvr. pose proof (code_bits_range here) as Hcb.
    arm_symexP (@nil (Z * expr)) ilCV 16%nat [false] [RVal (EVar 52%nat)] (jpins ++ [(28, EVar 51%nat)]) jvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); code_bits here; idx; code_val here] NoVals F0
      (mkst R (Z_to_bv 64 0x1d7b0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: try (subst here; tab_read TAB idx; clear - Hidx; lia).
    set (M1 := wbytes M (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + 1))) in *.
    set (M2 := wbytes M1 (zw (cv_S v + is_have s * 2 ^ 1 + 168)) (Z_to_le_bytes 2 (code_val here))) in *.
    set (s1 := iset_have s (is_have s + 1)). set (s2 := iset_lens s1 (arr_set (is_lens s1) (is_have s) (wrap16 (code_val here)))).
    set (r' := cdrop r (code_bits here)) in *.
    assert (Es2 : cb_lit_s s here = s2) by (subst s2 s1; unfold cb_lit_s; rewrite wrap32_id by lia; destruct s; reflexivity).
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 156 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_have M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2' : LMEM v (mkW s2 c r) M2).
    { subst M2 s2. replace (zw (cv_S v + is_have s * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * is_have s)) by (f_equal; lia).
      apply (LMEM_store_lens v C s1 c r M1 (is_have s) (code_val here) (code_val here) HM1 Hput); [lia | subst s1; destruct s; exact Halen | apply le2_wrap16]. }
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits here) RI0 ltac:(clear - Hhb Hcb; lia)) as [EW RI'].
    assert (Er' : r' = irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)) by (subst r'; unfold cdrop; rewrite EW; reflexivity).
    assert (HM2 : LMEM v (mkW s2 c r') M2) by (apply (LMEM_regs v s2 c r c r' M2 HM2'); rewrite ?Er'; reflexivity).
    exists R1, M2, 0x1d958. split; [subst M2 M1; by_run Hms1|].
    rewrite Es2. cbn [body_post w_s w_r w_c]. split; [reflexivity|].
    assert (HRC2 : RETC v (mkW s2 c r') M2).
    { subst M2 M1. apply (RETC_regs v (mkW s c r)); [| cbn [w_r]; rewrite Er'; reflexivity].
      apply (RETC_other v C); [| clear - CS Hhv; lia | clear - CS Hhv Htot; cbn; lia | unfold sep in CfS; clear - CfS CS Hhv Htot; cbn; lia].
      retc_tower C HRC. }
    assert (HX2 : LX v (mkW s2 c r')) by (apply (LX_step0 v s c r s2 c r' HX NH NB); subst s2 s1; rewrite ?Er'; try (destruct s; reflexivity); try reflexivity; [destruct s; cbn in Hmode |- *; rewrite Hmode; live_mode_tac | exact Xret | exact Xmsg]).
    split; [| split; [exact HM2 | split; [exact HRC2 | split; [exact HX2 | split; [subst s2 s1; destruct s; split; [reflexivity | split; reflexivity] |]]]]].
    + symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8.
      rewrite zalu_srl_small in Q23 by (clear - Rhold64 Hhb Hcb Rbits; lia). rewrite szwrap32_small in Q8 by (clear - Hhb Hcb Rbits; lia).
      unfold WREG, BKc. rewrite Er'. subst s2 s1. cbn -[zw Z.add Z.mul Z.ones ctab6 getr cv_P0 cv_I0 cv_S cv_sp Z.sub Z.pow Z.opp Z.shiftr Z.div].
      repeat match goal with |- _ /\ _ => split end;
        first [ lazymatch goal with |- LFIX _ _ => apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity end
              | rewrite Q13; destruct s; reflexivity
              | rewrite Q23; rewrite Z.shiftr_div_pow2 by (clear - Hcb; lia); reflexivity
              | exact Q8
              | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); first [assumption | destruct s; assumption] end
              | match goal with |- ?G => idtac "WREGL LEFT" G end ].
    + rewrite Er'. cbn [ir_put irset_bits irset_hold]. subst M2 M1.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS Hhv; lia | clear - CS Hhv Htot; cbn; lia | right; left; clear - Hhv Htot; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.

  Lemma cl_rep_pre : forall s c r R M idx here,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r ->
    cells s6_segs M (ctab6 v (is_lencode s)) 4 4 (cext (is_lencode s)) (cat (is_codes s) (is_lencode s)) ->
    0 <= idx < cext (is_lencode s) -> here = cat (is_codes s) (is_lencode s) idx -> code_bits here <= 15 -> 16 <= code_val here ->
    LMEM v (mkW s c r) M -> JREG s r idx (code_bits here) R ->
    exists R1,
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d7b0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d7e8) M s6_rom)
      /\ VREG s r (code_bits here) (code_val here) R1.
  Proof.
    intros s c r R M idx here HB RI TAB Hidx Ehere Hb15 Hval HM HJ.
    destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_jreg HJ.
    open_ictx C. open_lmem HM. open_rinv RI. unfold mapped in *.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 * cext (is_lencode s) < 2 ^ 63 /\ cext (is_lencode s) = 1444) by (rewrite ELC; cbn [ctab6 codeptr_addr cext]; clear - CS; lia).
    destruct HA as (HA0 & HA1 & HX1444).
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    pose proof (code_val_range here) as Hvr. pose proof (code_bits_range here) as Hcb.
    arm_symexP (@nil (Z * expr)) ilCV 8%nat [true] [RVal (EVar 52%nat)] (jpins ++ [(28, EVar 51%nat)]) jvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); code_bits here; idx; code_val here] NoVals F0
      (mkst R (Z_to_bv 64 0x1d7b0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: try (subst here; tab_read TAB idx; clear - Hidx; lia).
    all: match goal with |- ?G => idtac "LEFTP" G end.
    exists R1. split; [by_run Hms1|].
    symex_reg HR1 (6%bv : reg) as Q6.
    unfold VREG, BKc. repeat match goal with |- _ /\ _ => split end;
      first [ apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity
            | exact Q6
            | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
            | match goal with |- ?G => idtac "VREG LEFT" G end ].
  Qed.

  Ltac split_close HR Hfr HF :=
    unfold NJS, NJE, NK; repeat match goal with |- _ /\ _ => split end;
    first [ apply (LFIX_frame v _ _ _ HF Hfr); reflexivity
          | lazymatch goal with |- getr _ ?n = _ => first [ rewrite (Hfr n eq_refl); assumption
                                                          | let Q := fresh in symex_reg HR (n : reg) as Q; rewrite Q; first [reflexivity | f_equal; lia] ] end
          | match goal with |- ?G => idtac "SPLIT LEFT" G end ].

  Lemma cl_split16 : forall s c r R M hb,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> VREG s r hb 16 R ->
    exists R1,
      if hb + 2 <=? ir_bits r
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d8d4) M s6_rom) /\ NJE v s (hb + 2) hb c r R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d840) M s6_rom) /\ NJS v s (hb + 2) hb c r R1.
  Proof.
    intros s c r R M hb HB RI Hhb HV. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_vreg HV.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.leb_spec (hb + 2) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCV 8%nat [true; true] (@nil (option expr)) (jpins ++ [(6, EVar 51%nat)]) jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; 16] NoVals F0
        (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1 HF.
    - arm_symexP (@nil (Z * expr)) ilCV 8%nat [true; false] (@nil (option expr)) (jpins ++ [(6, EVar 51%nat)]) jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; 16] NoVals F0
        (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1 HF.
  Qed.

  Lemma cl_split17 : forall s c r R M hb,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> VREG s r hb 17 R ->
    exists R1,
      if hb + 3 <=? ir_bits r
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d8b0) M s6_rom) /\ NJE v s (hb + 3) hb c r R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d804) M s6_rom) /\ NJS v s (hb + 3) hb c r R1.
  Proof.
    intros s c r R M hb HB RI Hhb HV. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_vreg HV.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.leb_spec (hb + 3) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; false; true] (@nil (option expr)) (jpins ++ [(6, EVar 51%nat)]) jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; 17] NoVals F0
        (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1 HF.
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; false; false] (@nil (option expr)) (jpins ++ [(6, EVar 51%nat)]) jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; 17] NoVals F0
        (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1 HF.
  Qed.

  Lemma cl_split18 : forall s c r R M hb val,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> 16 <= val < 65536 -> val <> 16 -> val <> 17 -> VREG s r hb val R ->
    exists R1,
      if hb + 7 <=? ir_bits r
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d910) M s6_rom) /\ NJE v s (hb + 7) hb c r R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d87c) M s6_rom) /\ NJS v s (hb + 7) hb c r R1.
  Proof.
    intros s c r R M hb val HB RI Hhb Hval N16 N17 HV. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_vreg HV.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.leb_spec (hb + 7) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; true; true] (@nil (option expr)) (jpins ++ [(6, EVar 51%nat)])
        [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 65536)] v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; val] NoVals F0
        (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1 HF.
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; true; false] (@nil (option expr)) (jpins ++ [(6, EVar 51%nat)])
        [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 65536)] v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; val] NoVals F0
        (mkst R (Z_to_bv 64 0x1d7e8) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1 HF.
  Qed.
End Split.
End FXG.
End InflA_Codelens4.
Export InflA_Codelens4.

Module InflA_Codelens4b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Dist3.
Import InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Codelens2.
Import InflA_Codelens3.
Import InflA_Codelens4.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilCR : cfg := ilSx [0x1d92c] [].

Lemma bits_after_drop : forall h hb k, 0 <= h -> 0 <= hb -> 0 <= k <= 32 ->
  (h / 2 ^ hb) mod 2 ^ k = BITSv (Z.shiftr h hb) k.
Proof. intros h hb k Hh Hhb Hk. rewrite BITSv_land, Z.land_ones, Z.shiftr_div_pow2 by (try apply Z.shiftr_nonneg; lia). reflexivity. Qed.
Lemma drop_drop : forall h hb k, 0 <= hb -> 0 <= k -> h / 2 ^ hb / 2 ^ k = Z.shiftr (Z.shiftr h hb) k.
Proof. intros. rewrite !Z.shiftr_div_pow2 by (try apply Z.shiftr_nonneg; lia). reflexivity. Qed.

Lemma sll32_srl31_m1 : forall h, 1 <= h < 2 ^ 31 -> (h * 2 ^ 32 + -4294967296) mod 2 ^ 64 / 2 ^ 31 = 2 * (h - 1).
Proof.
  intros h Hh. replace (h * 2 ^ 32 + -4294967296) with ((h - 1) * 2 ^ 32) by lia. apply sll32_srl31. lia.
Qed.

Section Reps.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_nje HJ :=
    let X := fresh in pose proof HJ as X; unfold NJE, NK in X;
    destruct X as ((HF & G18 & G1 & G13 & G14 & G12 & G16 & G15 & G5 & G6) & G22 & G17 & G9 & G26 & G27); open_fix HF.

  Definition epins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (17, EVar 41%nat); (18, EVar 36%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat)); (26, EAdd (EVar 43%nat) (EVar 44%nat));
     (13, EVar 45%nat); (14, EVar 46%nat); (12, EVar 47%nat); (16, EVar 48%nat); (15, EVar 49%nat); (5, EVar 50%nat); (6, EVar 51%nat)].
  Definition evb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 2 ^ 15); (49%nat, 2 ^ 63); (50%nat, 16); (51%nat, 64); (52%nat, 65536)].

  Ltac kreg_close HR Hfr HF :=
    unfold KREG, BKc; repeat match goal with |- _ /\ _ => split end;
    first [ apply (LFIX_frame v _ _ _ HF Hfr); reflexivity
          | lazymatch goal with |- getr _ ?n = _ => first [ rewrite (Hfr n eq_refl); assumption
                                                          | let Q := fresh in symex_reg HR (n : reg) as Q; rewrite Q;
                                                            rewrite ?zalu_srl_small by lia; rewrite ?szwrap32_small by lia;
                                                            rewrite ?wrap32_id by lia; rewrite ?bits_after_drop, ?drop_drop by lia;
                                                            first [reflexivity | f_equal; lia] ] end
          | match goal with |- ?G => idtac "KREG LEFT" G end ].

  Lemma cl_r17 : forall s c r R M hb,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> hb + 3 <= ir_bits r -> NJE v s (hb + 3) hb c r R ->
    exists R1,
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d8b0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d92c) M s6_rom)
      /\ KREG v s (cdrop (cdrop r hb) 3) 0 (3 + BITSv (ir_hold (cdrop r hb)) 3) R1.
  Proof.
    intros s c r R M hb HB RI Hhb Hn HJ. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_nje HJ.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    arm_symexP (@nil (Z * expr)) ilCR 10%nat (@nil bool) (@nil (option expr)) epins evb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; hb + 3] NoVals F0
      (mkst R (Z_to_bv 64 0x1d8b0) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTR17" G end.
    exists R1. split; [by_run Hms1|].
    unfold cdrop. cbn [ir_hold ir_bits ir_have ir_next ir_put ir_left ir_out irset_bits irset_hold].
    kreg_close HR1 Hfr1 HF.
  Qed.

  Lemma cl_r18 : forall s c r R M hb,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> hb + 7 <= ir_bits r -> NJE v s (hb + 7) hb c r R ->
    exists R1,
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d910) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d92c) M s6_rom)
      /\ KREG v s (cdrop (cdrop r hb) 7) 0 (11 + BITSv (ir_hold (cdrop r hb)) 7) R1.
  Proof.
    intros s c r R M hb HB RI Hhb Hn HJ. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_nje HJ.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    arm_symexP (@nil (Z * expr)) ilCR 10%nat (@nil bool) (@nil (option expr)) epins evb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; hb + 7] NoVals F0
      (mkst R (Z_to_bv 64 0x1d910) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTR18" G end.
    exists R1. split; [by_run Hms1|].
    unfold cdrop. cbn [ir_hold ir_bits ir_have ir_next ir_put ir_left ir_out irset_bits irset_hold].
    kreg_close HR1 Hfr1 HF.
  Qed.

  Lemma cl_r16 : forall s c r R M hb,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> hb + 2 <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> NJE v s (hb + 2) hb c r R ->
    exists R1 M1 pc1,
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d8d4) M s6_rom) (mkst R1 (Z_to_bv 64 pc1) M1 s6_rom)
      /\ if is_have s =? 0
         then body_post v (mkW s c r) M (ARun false (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_bit_length_repeat) (cdrop r hb))) R1 M1 pc1
         else pc1 = 0x1d92c /\ M1 = M
              /\ KREG v s (cdrop (cdrop r hb) 2) (arr_get (is_lens s) (is_have s - 1)) (3 + BITSv (ir_hold (cdrop r hb)) 2) R1.
  Proof.
    intros s c r R M hb Hmode HB RI Hhb Hn HM HRC HX HJ. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_nje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.eqb_spec (is_have s) 0) as [H0|H0].
    -
      arm_symexP (@nil (Z * expr)) ilCR 30%nat [false; true] [RVal (ELit (JT BAD))] epins evb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; hb + 2] NoVals F0
        (mkst R (Z_to_bv 64 0x1d8d4) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (c' := icset_msg c MSG_invalid_bit_length_repeat) in *. set (s' := iset_mode s BAD) in *. set (r' := cdrop r hb) in *.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66234)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r hb RI0 ltac:(clear - Hhb Hn; lia)) as [EW RI'].
      assert (Er' : r' = irset_bits (irset_hold r (Z.shiftr (ir_hold r) hb)) (ir_bits r - hb)) by (subst r'; unfold cdrop; rewrite EW; reflexivity).
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (rewrite Er'; exact Hput).
      assert (HM0 : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); rewrite ?Er'; reflexivity).
      assert (HM1 : LMEM v (mkW s c' r') M1) by (exact (LMEM_store_msg v C s c r' M MSG_invalid_bit_length_repeat HM0 Hput')).
      assert (HM2 : LMEM v (mkW s' c' r') M2).
      { apply (LMEM_store_scalar v C s c' r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_bit_length_repeat) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      exists R1, M2, (arm6_pc BAD). split; [subst M2 M1; by_run Hms1|].
      cbn [body_post arm_post]. split; [| subst s'; reflexivity]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | cbn [w_r]; rewrite Er'; reflexivity]|]. split.
        * apply (LX_step0 v s c r s' c' r' HX NH NB); subst s' c'; rewrite ?Er'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_bit_length_repeat; lia].
        * symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (23%bv : reg) as G22'. symex_reg HR1 (24%bv : reg) as G23'.
          rewrite zalu_srl_small in G22' by (clear - Rhold64 Hhb; lia). rewrite szwrap32_small in G23' by (clear - Hhb Hn Rbits; lia).
          unfold LREG_arm. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [| intros _; exact G8'].
          unfold LVARS; cbn [w_r]. rewrite Er'. cbn. rewrite Z.shiftr_div_pow2 by lia.
          regs_via Hfr1; first [exact G26' | exact G22' | exact G23' | match goal with |- ?G => idtac "R16 LV LEFT" G end].
      + cbn [w_r]. rewrite Er'. cbn [ir_put irset_bits irset_hold]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    - pose proof (Mlens (is_have s - 1) ltac:(lia)) as Cprev. pose proof (Blens (is_have s - 1) ltac:(lia)) as Bprev.
      arm_symexP (@nil (Z * expr)) ilCR 16%nat [true] [RVal (EVar 52%nat)] epins evb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb; hb + 2; arr_get (is_lens s) (is_have s - 1)] NoVals F0
        (mkst R (Z_to_bv 64 0x1d8d4) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: rewrite ?sll32_srl31_m1 by (clear - H0 Hhv Htot; lia).
      1: { replace (cv_S v + 2 * (is_have s - 1) + 168) with (cv_S v + 168 + 2 * (is_have s - 1)) by lia. apply (cell_read_small s6_segs M _ 2%nat _ Cprev). cbn. clear - Bprev. lia. }
      1: { clear - CS Hhv Htot H0. lia. }
      all: match goal with |- ?G => idtac "LEFTR16b" G end.
      exists R1, M, 0x1d92c. split; [by_run Hms1|]. split; [reflexivity|]. split; [reflexivity|].
      unfold cdrop. cbn [ir_hold ir_bits ir_have ir_next ir_put ir_left ir_out irset_bits irset_hold].
      kreg_close HR1 Hfr1 HF.
  Qed.
End Reps.
End FXG.
End InflA_Codelens4b.
Export InflA_Codelens4b.

Module InflA_Codelens5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Segs6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S.Callee6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilCD : cfg := CFG [] [] arm_rets (pc6_disp :: arm_stops) [].

Definition cl_pinv_stmt : Prop := forall (NI NO WN TOT0 : Z) s c r,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = CODELENS -> is_nlen s + is_ndist s <= is_have s -> ir_ret r = 0 ->
  arr_get (is_lens s) 256 <> 0 -> it_ret (cd_call1 s) = 0 -> it_ret (cd_call2 (cd_S1 s (cd_call1 s))) = 0 ->
  pinv NI NO WN TOT0 (mkW (iset_mode (cd_S2 (cd_S1 s (cd_call1 s)) (cd_call2 (cd_S1 s (cd_call1 s)))) LEN_) c (irset_ret r 0)).

Section SegC.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.

  Definition CREG (s : inflate_state) (c : icall) (r : iregs) (ret : Z) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 20 = zw 16209
    /\ getr R 22 = zw (cv_S v + 168) /\ getr R 25 = zw A6_JTAB
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4
    /\ LVARK v (mkW s c r) R /\ getr R 10 = zw ret /\ getr R 26 = zw 6.

  Definition cpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (20, ELit 16209); (22, EAdd (EVar 33%nat) (ELit 168)); (25, ELit 0x12510);
     (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (9, EVar 39%nat); (23, EVar 40%nat); (24, EVar 41%nat);
     (27, EAdd (EVar 43%nat) (EVar 44%nat)); (10, EVar 45%nat); (26, ELit 6)].

  Lemma codelens_segC : forall s c r R M ret,
    is_mode s = CODELENS -> (ret = 0 -> len_facts v s c) -> RINV (cv_NI v) (cv_NO v) r -> (ret = 0 \/ ret = 1 \/ ret = -1) ->
    (ret = 0 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode s LEN_) c (irset_ret r 0))) ->
    LMEM v (mkW s c r) M -> LX v (mkW s c r) -> CREG s c r ret R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1dbe0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (cdC_res (cv_flush v) s c r ret) R' M' pc'.
  Proof.
    intros s c r R M ret Hmode HLF RI Hret HPL HM HX HR.
    destruct HR as (G2 & G25 & G19 & G21 & G24 & G3 & G4 & HV & G10 & G27). unfold INF_FRAME in G2. unfold A6_JTAB in G24.
    pose proof HV as X; unfold LVARK in X; cbn [w_r] in X; destruct X as (G9 & G18 & G8 & G22 & G23 & G26).
    open_ictx C. open_lmem HM. open_lx HX. pose proof RI as RI0. open_rinv RI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hrm : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    rewrite <- (zw_mod ret) in G10.
    unfold cdC_res. replace (cv_flush v =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; clear - Cflush; lia).
    destruct (Z.eq_dec ret 0) as [R0|R0].
    -
      subst ret. cbn [Z.eqb negb]. change (0 mod 2 ^ 64) with 0 in G10.
      (* 1.4: the ok path (0x1e314) reloads strm (sp + 96) before flush (sp + 104) *)
      arm_symexP (@nil (Z * expr)) ilS 20%nat [true; false]
        [RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 18446744073709535436)]
        cpins [(45%nat, 1)] v r [0] NoVals F0
        (mkst R (Z_to_bv 64 0x1dbe0) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_sp v - 224 + 64)) (Z_to_le_bytes 8 0)) in *.
      set (M2 := wbytes M1 (zw (cv_sp v - 224 + 64)) (Z_to_le_bytes 8 0)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16199)) in *.
      set (r' := irset_ret r 0) in *. set (s' := iset_mode s LEN_) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ (LMEM_regs v s c r c r' M HM eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW s c r') M2) by (apply (LMEM_store_fscratch v C s c r' M1 64 _ HM1 Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM3 : LMEM v (mkW s' c r') M3).
      { apply (LMEM_store_scalar v C s c r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s LEN_ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c r') M3).
      { subst M3. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        subst M2. apply (RETC_regs v (mkW s c r')); [exact (RETC_store v C s c r' M1) | reflexivity]. }
      assert (HX3 : LX v (mkW s' c r')) by (apply (LX_step0 v s c r s' c r' HX NH NB); subst s' r'; try reflexivity; [live_mode_tac | cbn; lia | exact Xmsg]).
      assert (RI' : RINV (cv_NI v) (cv_NO v) r') by (subst r'; unfold RINV in *; cbn; exact RI0).
      symex_reg HR1 (31%bv : reg) as Q31. change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31. rewrite zw_neg_mod in Q31.
      symex_reg HR1 (1%bv : reg) as Q1. symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11.
      symex_reg HR1 (29%bv : reg) as Q29.
      assert (HF3 : LFIX v R1).
      { unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr1; first [exact Q1 | exact Q10 | exact Q11 | exact Q31 | exact Q29 | match goal with |- ?G => idtac "LFIX LEFT" G end]. }
      assert (HV3 : LVARS v (mkW s' c r') R1) by (unfold LVARS; cbn [w_r]; subst r'; cbn; regs_via Hfr1; first [exact Q1 | match goal with |- ?G => idtac "LVARS3 LEFT" G end]).
      destruct (len__core v C IFAST FFOK FASTOK GFOB FFRAME s' c r' R1 M3 (HPL eq_refl) ltac:(reflexivity) (len_facts_mode v s c LEN_ (HLF eq_refl)) RI' HM3 HRC3 HX3 HF3 HV3)
        as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
      apply (arm_post_rebase v s c r c r'); [subst r'; reflexivity|].
      apply (arm_post_chain v (mkW s c r') (mkW s' c r') M M3); [subst s'; apply same_blocks_mode | | exact HPOST].
      cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia]).
      apply MFRAME_refl.
    -
      replace (negb (ret =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact R0).
      assert (Hrm0 : ret mod 2 ^ 64 <> 0).
      { intros E. apply R0. destruct Hret as [H|[H|H]]; subst ret; [reflexivity | discriminate E | discriminate E]. }
      arm_symexP (@nil (Z * expr)) ilCD 20%nat [false]
        [RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 18446744073709535436)]
        cpins [(45%nat, 2 ^ 64)] v r [ret mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1dbe0) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      rewrite le8_mod64 in Hms1.
      set (r' := irset_ret r ret) in *. set (c' := icset_msg c MSG_invalid_distances_set) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_sp v - 224 + 64)) (Z_to_le_bytes 8 ret)) in *.
      set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66936)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ (LMEM_regs v s c r c r' M HM eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW s c' r') M2) by (exact (LMEM_store_msg v C s c r' M1 MSG_invalid_distances_set HM1 Hput')).
      assert (HM3 : LMEM v (mkW s' c' r') M3).
      { apply (LMEM_store_scalar v C s c' r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c' r') M3).
      { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        apply (RETC_other v C); [| clear - CZP; lia | clear - CZP; cbn; lia | unfold sep in CfZ; clear - CfZ CZP; cbn; lia].
        exact (RETC_store v C s c r' M). }
      pose proof (icset_msg_facts c MSG_invalid_distances_set) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      assert (HX3 : LX v (mkW s' c' r')).
      { apply (LX_step0 v s c r s' c' r' HX NH NB); subst s' c' r'; try reflexivity; [live_mode_tac | cbn; clear - Hret; lia | rewrite K11; unfold MSG_invalid_distances_set; lia]. }
      pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM3)) as C8'. cbn [w_s] in C8'. replace (is_mode s') with BAD in C8' by (subst s'; destruct s; reflexivity).
      pose proof (lm_rod _ _ _ HM3) as Mrod3.
      symex_reg HR1 (31%bv : reg) as W31. change 18446744073709535436 with ((-16180) mod 2 ^ 64) in W31. rewrite zw_neg_mod in W31.
      symex_reg HR1 (1%bv : reg) as W1. symex_reg HR1 (10%bv : reg) as W10. symex_reg HR1 (11%bv : reg) as W11.
      symex_reg HR1 (29%bv : reg) as W29. symex_reg HR1 (26%bv : reg) as W27.
      j1011_symex ilS 12%nat [true] [RVal (ELit 16209); RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
        (mkst R1 (Z_to_bv 64 pc6_disp) M3 s6_rom) R' HR' Hfr Hms.
      all: try (lazymatch goal with |- getr _ ?n = zw _ => first [assumption | rewrite (Hfr1 n eq_refl); assumption] end).
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTC3" G end.
      exists R', M3, (arm6_pc BAD). split.
      { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 pc6_disp) M3 s6_rom)); subst M3 M2 M1; [by_run Hms1 | by_run Hms]. }
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM3|]. split; [exact HRC3|]. split; [exact HX3|].
        symex_reg HR' (9%bv : reg) as G8'.
        unfold LREG_arm. split; [| split; [| intros _; exact G8']].
        * unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr; first [exact W1 | exact W10 | exact W11 | exact W31 | exact W29
             | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl), (Hfr1 n eq_refl); assumption end | match goal with |- ?G => idtac "LFIX2 LEFT" G end].
        * unfold LVARS; cbn [w_r]. subst r'. cbn. regs_via Hfr; first [exact W1 | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl), (Hfr1 n eq_refl); assumption end
             | symex_reg HR' (27%bv : reg) as G26'; exact G26' | match goal with |- ?G => idtac "LVARS2 LEFT" G end].
      + cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.
End SegC.
End FXG.
End InflA_Codelens5.
Export InflA_Codelens5.

