(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Record iscrh : Type := mkSH {
  h5 : word; h6 : word; h7 : word; h8 : word; h9 : word; h12 : word; h13 : word; h14 : word; h15 : word; h16 : word; h17 : word;
  h22 : word; h23 : word; h26 : word; h27 : word; h28 : word; h29 : word; h30 : word; h31 : word }.

Definition ILOOPh (X : ictx) (w : iw) (pc : Z) (q : iscrh) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) (h5 q) (h6 q) (h7 q) (wz (il_As (ix_L X)))
                 (h8 q) (wz (il_S (ix_L X))) (wz (ix_flush X)) (h12 q) (h13 q) (h14 q) (h15 q) (h16 q) (h17 q)
                 (h9 q) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (h22 q) (h23 q) (wz 75072)
                 (h27 q) (h26 q) (h28 q) (h29 q) (h30 q) (h31 q))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOPh_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x24 = wz 75072 -> x25 = wz (il_As (ix_L X)) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPh X w pc (mkSH x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOPh. eexists. split; [reflexivity| assumption]. Qed.

Lemma ILOOPh_of_ILOOP : forall X w pc x8 x12 ms, ILOOP X w pc x8 x12 ms ->
  exists q, ILOOPh X w pc q ms /\ h8 q = x8 /\ h12 q = x12 /\ h9 q = wz (ir_have (w_r w)) /\ h22 q = wz (ir_hold (w_r w))
            /\ h23 q = wz (ir_bits (w_r w)) /\ h26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) /\ h29 q = wz 30 /\ h31 q = wz (-16180).
Proof.
  intros X w pc x8 x12 ms (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HM).
  eexists (mkSH x5 x6 x7 x8 _ x12 x13 x14 x15 x16 x17 _ _ _ x27 x28 _ x30 _).
  split; [|cbn [h8 h12 h9 h22 h23 h26 h29 h31]; repeat split; reflexivity]. exists m. split; [reflexivity| exact HM].
Qed.

Lemma ILOOPh_regs : forall X s c r r' pc q ms, ILOOPh X (mkW s c r) pc q ms ->
  ir_in r' = ir_in r -> ir_out r' = ir_out r -> ir_ret r' = ir_ret r -> ir_put r' = ir_put r -> ir_left r' = ir_left r ->
  ILOOPh X (mkW s c r') pc q ms.
Proof.
  intros X s c r r' pc q ms (m & -> & HM) E1 E2 E3 E4 E5. exists m. cbn [w_r]. rewrite E4, E5. split; [reflexivity|].
  eapply IMEM_regs; [exact HM| assumption..].
Qed.

Definition NBJh (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (n : Z) (pcj : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, NEEDBITS n (mkW s c r) = ARun tt (mkW s c r1)
                  /\ ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8))
                  /\ ILOOPh X (mkW s c r) pcj q ms'
                  /\ h12 q = wz (ir_have r1) /\ h13 q = wz n /\ h14 q = wz (ir_bits r1) /\ h15 q = wz (il_NI (ix_L X) + ir_next r1)
                  /\ h22 q = wz (ir_hold r1) /\ h29 q = wz 30 /\ h31 q = wz (-16180))
    \/ (exists r1, NEEDBITS n (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ r1 = pullr c r) /\ ILEAVE X (mkW s c r1) ms').

Ltac iarm_openh HL :=
  let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU;
  cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.

Ltac iarm_openh_keep HL HMEM :=
  let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (m & -> & HMEM);
  pose proof HMEM as ((jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU;
  cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.
