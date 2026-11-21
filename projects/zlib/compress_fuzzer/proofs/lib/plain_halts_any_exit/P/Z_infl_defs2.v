(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Record iscr : Type := mkSC {
  sc5 : word; sc6 : word; sc7 : word; sc8 : word; sc12 : word; sc13 : word; sc14 : word; sc15 : word; sc16 : word; sc17 : word;
  sc26 : word; sc27 : word; sc28 : word; sc30 : word }.

Definition ILOOPg (X : ictx) (w : iw) (pc : Z) (q : iscr) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) (sc5 q) (sc6 q) (sc7 q) (wz (il_As (ix_L X)))
                 (sc8 q) (wz (il_S (ix_L X))) (wz (ix_flush X)) (sc12 q) (sc13 q) (sc14 q) (sc15 q) (sc16 q) (sc17 q)
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 75040)
                 (sc27 q) (sc26 q) (sc28 q) (wz 30) (sc30 q) (wz (-16180)))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOPg_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 75040 -> x25 = wz (il_As (ix_L X)) ->
  x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPg X w pc (mkSC x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOPg. eexists. split; [reflexivity| assumption]. Qed.

Ltac iarm_openg HL :=
  let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *.

Definition NBJg (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (n : Z) (pcj : Z) (Q : iregs -> iscr -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, NEEDBITS n (mkW s c r) = ARun tt (mkW s c r1)
                  /\ ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8))
                  /\ ILOOPg X (mkW s c r1) pcj q ms' /\ Q r1 q)
    \/ (exists r1, NEEDBITS n (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ r1 = pullr c r) /\ ILEAVE X (mkW s c r1) ms').

#[local] Transparent iout_bytes.
Lemma iout_bytes_nth : forall rest0 c put i, 0 <= i < put ->
  nth_error (iout_bytes rest0 c put) (Z.to_nat i) = Some (Z_to_bv 8 (arr_get (ic_outbuf c) i)).
Proof. intros rest0 c put i Hi. unfold iout_bytes. rewrite nth_error_app1 by (rewrite av8_length; lia). apply av8_nth. lia. Qed.

Lemma iout_bytes_ext : forall rest0 c' c put, ic_outbuf c' = ic_outbuf c -> iout_bytes rest0 c' put = iout_bytes rest0 c put.
Proof. intros rest0 c' c put E. unfold iout_bytes. rewrite E. reflexivity. Qed.
#[local] Opaque iout_bytes.

Lemma firstn1_skipn_nth : forall {A} (l : list A) k b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  intros A l. induction l as [|x l IH]; intros k b H; destruct k; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

