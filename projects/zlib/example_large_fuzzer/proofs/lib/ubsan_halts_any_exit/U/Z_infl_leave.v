(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateArms RefInflateSafeS2 RefInflateSafeOK3 RefInflate_runA DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_LV_WIN : Z := 0x219b4.
Definition PC_LV_TAIL : Z := 0x21a10.
Definition lv_w (w : iw) : iw :=
  mkW (fst (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w)))
      (snd (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w))) (w_r w).
Definition IMEMLW (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  iframeL X (w_r w) m
  /\ stk usegs m (ix_lo X) (bv_unsigned (ix_sp X) + -256)
  /\ IREP m (ix_L X) (w_s w) (w_c w)
  /\ iin m X
  /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv usegs m /\ munch W (ix_m0 X) m /\ wmono usegs (ix_m0 X) m.
Lemma IMEMLW_of_IMEML : forall X w m, IMEML X w m -> IMEMLW (ix_W X) X w m.
Proof. intros X w m H. exact H. Qed.
Definition ix_WF (X : ictx) : list ivl := ix_W X ++ [(il_Aw (ix_L X), il_Aw (ix_L X) + 32768)].
Definition ILVT (W : list ivl) (X : ictx) (w : iw) (pc : Z) (x10 x12 x13 x14 x19 : word) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x15 x16 x17 x18 x20 x21 x22 x23 x25 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X))) (wz (il_NO (ix_L X) + ir_put (w_r w))) x10 (wz (ix_flush X)) x12 x13 x14 x15 x16 x17 (wz (il_S (ix_L X))) x18 x19 x20 x21 (wz (ir_have (w_r w))) x23 x22 x25 (wz (ir_ret (w_r w))) x28 x29 x30 x31)
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom usegs)
    /\ IMEMLW W X w m.
Lemma ILVT_intro : forall W X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -256) -> x3 = ix_gp X -> x4 = ix_tp X -> x18 = wz (il_S (ix_L X)) ->
  x9 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x11 = wz (ix_flush X) -> x23 = wz (ir_have (w_r w)) ->
  x27 = wz (ir_ret (w_r w)) -> x8 = wz (il_As (ix_L X)) -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  ILVT W X w pc x10 x12 x13 x14 x20 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold ILVT. do 18 eexists. split; [reflexivity| assumption]. Qed.
Lemma b2z_shl : forall b n, 0 <= n -> Z.shiftl (Z.b2z b) n = Z.b2z b * 2^n.
Proof. intros b n Hn. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma lor_b2z : forall a b, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b).
Proof. intros [|] [|]; reflexivity. Qed.
Ltac lv_dt :=
  do 3 zs;
  lazymatch goal with |- context [Z.b2z ?b] => pose proof (zb_b2z_range b) end;
  zs; rewrite (b2z_shl _ 6) by lia; change (2^6) with 64;
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF;
  do 6 zs;
  lazymatch goal with |- context [Z.b2z (Z.lxor ?m ?k <? 1)] => pose proof (zb_b2z_range (Z.lxor m k <? 1)) end;
  zs; rewrite (b2z_shl _ 7) by lia; change (2^7) with 128;
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF;
  do 8 zs; rewrite lor_b2z;
  lazymatch goal with |- context [Z.b2z (?a || ?b)] => pose proof (zb_b2z_range (a || b)) end;
  zs; rewrite (b2z_shl _ 8) by lia; change (2^8) with 256;
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF;
  do 2 zs.
Definition IMEMF (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  stk usegs m (ix_lo X) (bv_unsigned (ix_sp X))
  /\ IREP m (ix_L X) (w_s w) (w_c w) /\ iin m X /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv usegs m /\ munch W (ix_m0 X) m /\ wmono usegs (ix_m0 X) m.
Definition IFIN (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
    ms = MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz rc) a1 a2 a3 a4 a5 a6 a7
                 (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
            (ix_F X) (ret_pc (ix_ra X)) (ix_fc X) None m (seg_rom usegs)
    /\ IMEMF W X w m.
Definition IRETW (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) x5 x6 x7 x8 x9 (wz rc) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            (ix_F X) (wz PC_EPILOGUE) (ix_fc X) None m (seg_rom usegs)
    /\ IMEMLW W X w m.
Lemma IRETW_of_IRET : forall X rc w ms, IRET X rc w ms -> IRETW (ix_W X) X rc w ms.
Proof.
  intros X rc w ms (x1 & x5 & x6 & x7 & x8 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & E & HM & _).
  unfold IRETW. do 28 eexists. split; [exact E| exact HM].
Qed.
Lemma IRETW_intro : forall W X rc w x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -256) -> x3 = ix_gp X -> x4 = ix_tp X -> x10 = wz rc -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  IRETW W X rc w (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz PC_EPILOGUE) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold IRETW. do 28 eexists. split; [reflexivity| assumption]. Qed.
Lemma epilogue_gen : forall W X rc w ms, IRETW W X rc w ms -> ix_ok X -> evt usegs (IFIN W X rc w) ms.
Proof.
  intros W X rc [s c r] ms HL XO.
  destruct HL as (x1 & x5 & x6 & x7 & x8 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m
                  & -> & (retw & j0 & jf & FRM) & STK & HREP & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM. cbn [w_s w_c w_r] in *. ix_open XO.
  unfold PC_EPILOGUE. do 14 zs.
  release_frame FRM STK (bv_unsigned (ix_sp X)).
  zs.
  apply evt_done. unfold IFIN. do 15 eexists. split; [reflexivity|].
  unfold IMEMF. cbn [w_s w_c w_r]. repeat (split; [eassumption|]). assumption.
Qed.
Lemma epilogue_spec : forall X rc w ms, IRET X rc w ms -> ix_ok X -> evt usegs (IFIN (ix_W X) X rc w) ms.
Proof. intros X rc w ms H XO. exact (epilogue_gen _ X rc w ms (IRETW_of_IRET _ _ _ _ H) XO). Qed.
Lemma leave_tail : forall W X w x10 x12 x13 x14 x19 ms,
  ILVT W X w PC_LV_TAIL x10 x12 x13 x14 x19 ms -> ix_ok X ->
  0 <= ix_flush X <= 4 -> 0 <= ir_in (w_r w) < 2^32 -> 0 <= ir_have (w_r w) < 2^32 -> 0 <= ir_out (w_r w) < 2^32 -> 0 <= ir_left (w_r w) < 2^32 ->
  - 2^31 <= ir_ret (w_r w) < 2^31 ->
  evt usegs (IFIN W X (ret_model (ix_flush X) (wrap32 (ir_in (w_r w) - ir_have (w_r w))) (wrap32 (ir_out (w_r w) - ir_left (w_r w))) (w_r w)) w) ms.
Proof.
  intros W X [s c r] x10 x12 x13 x14 x19 ms HL XO RF RI RH RO RL RR. cbn [w_s w_c w_r] in *.
  eapply evt_cut; [| intros ms1 H1; exact (epilogue_gen W X _ _ ms1 H1 XO)].
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x23 & x25 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as ((retw & j0 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_r] in *. ix_open XO.
  unfold PC_LV_TAIL. do 12 zs. rewrite bufrule_clang by lia.
  unfold ret_model. change Z_FINISH with 4. change Z_OK with 0.
  destruct ((((wrap32 (ir_in r - ir_have r) =? 0) && (wrap32 (ir_out r - ir_left r) =? 0)) || (ix_flush X =? 4)) && (ir_ret r =? 0))%bool; cbn [Z.b2z].
  - zs. br_false. do 2 zs. apply evt_done. eapply IRETW_intro; try reflexivity. exact HMEM.
  - zs. br_true. do 1 zs. apply evt_done. eapply IRETW_intro; try reflexivity. exact HMEM.
Qed.
