(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateArms RefInflateSafeS2 RefInflateSafeOK3 RefInflate_runA DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LV_WIN : Z := 0x1ee40.
Definition PC_LV_TAIL : Z := 0x1ee98.

Definition lv_w (w : iw) : iw :=
  mkW (fst (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w)))
      (snd (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w))) (w_r w).

Definition IMEMLW (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  iframeL X (w_r w) m
  /\ stk psegs m (ix_lo X) (bv_unsigned (ix_sp X) + -224)
  /\ IREP m (ix_L X) (w_s w) (w_c w)
  /\ iin m X
  /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv psegs m /\ munch W (ix_m0 X) m /\ wmono psegs (ix_m0 X) m.
Lemma IMEMLW_of_IMEML : forall X w m, IMEML X w m -> IMEMLW (ix_W X) X w m.
Proof. intros X w m H. exact H. Qed.

Definition ix_WF (X : ictx) : list ivl := ix_W X ++ [(il_Aw (ix_L X), il_Aw (ix_L X) + 32768)].

Definition ILVT (W : list ivl) (X : ictx) (w : iw) (pc : Z) (x10 x12 x15 x19 x25 : word) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x13 x14 x16 x17 x18 x21 x22 x23 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 x25
                 (wz (ir_ret (w_r w))) x10 (wz (ix_flush X)) x12 x13 x14 x15 x16 x17
                 (wz (ir_have (w_r w))) x18 x19 (wz (ir_in (w_r w))) x21 x22 x23 (wz (ir_out (w_r w))) x27 x26 x28 x29 x30 x31)
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEMLW W X w m.

Lemma ILVT_intro : forall W X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X -> x8 = wz (ir_ret (w_r w)) ->
  x9 = wz (ir_have (w_r w)) -> x11 = wz (ix_flush X) -> x20 = wz (ir_in (w_r w)) -> x24 = wz (ir_out (w_r w)) -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  ILVT W X w pc x10 x12 x15 x19 x25 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                 F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILVT. do 18 eexists. split; [reflexivity| assumption]. Qed.

Definition IMEMF (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  stk psegs m (ix_lo X) (bv_unsigned (ix_sp X))
  /\ IREP m (ix_L X) (w_s w) (w_c w) /\ iin m X /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv psegs m /\ munch W (ix_m0 X) m /\ wmono psegs (ix_m0 X) m.

Definition IFIN (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
    ms = MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz rc) a1 a2 a3 a4 a5 a6 a7
                 (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
            (ix_F X) (ret_pc (ix_ra X)) (ix_fc X) None m (seg_rom psegs)
    /\ IMEMF W X w m.

Definition IRETW (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17
                 x9 x18 x19 (wz rc) x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
            (ix_F X) (wz PC_EPILOGUE) (ix_fc X) None m (seg_rom psegs)
    /\ IMEMLW W X w m.
Lemma IRETW_of_IRET : forall X rc w ms, IRET X rc w ms -> IRETW (ix_W X) X rc w ms.
Proof.
  intros X rc w ms (x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & E & HM & _).
  unfold IRETW. do 28 eexists. split; [exact E| exact HM].
Qed.
Lemma IRETW_intro : forall W X rc w x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X -> x20 = wz rc -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  IRETW W X rc w (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                  F (wz PC_EPILOGUE) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold IRETW. do 28 eexists. split; [reflexivity| assumption]. Qed.

Lemma epilogue_gen : forall W X rc w ms, IRETW W X rc w ms -> ix_ok X -> evt psegs (IFIN W X rc w) ms.
Proof.
  intros W X rc [s c r] ms HL XO.
  destruct HL as (x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m
                  & -> & (retw & jf & FRM) & STK & HREP & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM. cbn [w_s w_c w_r] in *. ix_open XO.
  unfold PC_EPILOGUE. do 15 zs.
  release_frame FRM STK (bv_unsigned (ix_sp X)).
  zs.
  apply evt_done. unfold IFIN. do 15 eexists. split; [reflexivity|].
  unfold IMEMF. cbn [w_s w_c w_r]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma epilogue_spec : forall X rc w ms, IRET X rc w ms -> ix_ok X -> evt psegs (IFIN (ix_W X) X rc w) ms.
Proof. intros X rc w ms H XO. exact (epilogue_gen _ X rc w ms (IRETW_of_IRET _ _ _ _ H) XO). Qed.

Lemma leave_tail : forall W X w x10 x12 x15 x19 x25 ms,
  ILVT W X w PC_LV_TAIL x10 x12 x15 x19 x25 ms -> ix_ok X ->
  0 <= ix_flush X <= 4 -> 0 <= ir_in (w_r w) < 2^32 -> 0 <= ir_have (w_r w) < 2^32 -> 0 <= ir_out (w_r w) < 2^32 -> 0 <= ir_left (w_r w) < 2^32 ->
  - 2^31 <= ir_ret (w_r w) < 2^31 ->
  evt psegs (IFIN W X (ret_model (ix_flush X) (wrap32 (ir_in (w_r w) - ir_have (w_r w))) (wrap32 (ir_out (w_r w) - ir_left (w_r w))) (w_r w)) w) ms.
Proof.
  intros W X [s c r] x10 x12 x15 x19 x25 ms HL XO RF RI RH RO RL RR. cbn [w_s w_c w_r] in *.
  eapply evt_cut; [| intros ms1 H1; exact (epilogue_gen W X _ _ ms1 H1 XO)].
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x16 & x17 & x18 & x21 & x22 & x23 & x26 & x27 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  cbn [w_r]. unfold PC_LV_TAIL. do 9 zs. rewrite bufrule_clang by lia.
  unfold ret_model. change Z_FINISH with 4. change Z_OK with 0.
  destruct ((((wrap32 (ir_in r - ir_have r) =? 0) && (wrap32 (ir_out r - ir_left r) =? 0)) || (ix_flush X =? 4)) && (ir_ret r =? 0))%bool; cbn [Z.b2z].
  - zs. br_false. do 2 zs. apply evt_done. eapply IRETW_intro; try reflexivity. exact HMEM.
  - zs. br_true. do 1 zs. apply evt_done. eapply IRETW_intro; try reflexivity. exact HMEM.
Qed.
