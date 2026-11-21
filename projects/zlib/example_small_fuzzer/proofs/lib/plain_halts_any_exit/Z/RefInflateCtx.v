(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.

Module RefInflate1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Prologue.
End Prologue.


Section Epilogue.
End Epilogue.
End RefInflate1.

Module RefInflate2.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac sxlia := unfold szwrap; change (2 ^ (32 - 1)) with 2147483648; Z.to_euclidean_division_equations; lia.
Lemma szwrap32_congr : forall x y, (x - y) mod 2 ^ 32 = 0 -> szwrap 32 x = szwrap 32 y.
Proof. intros x y H. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations. lia. Qed.
Local Ltac sxeq := f_equal; first [ sxlia | apply szwrap32_congr; sxlia ].

Section Leave1.
End Leave1.


Section Leave2.
End Leave2.


Lemma land_small_shiftl : forall a b k, 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> Z.land a (Z.shiftl b k) = 0.
Proof.
  intros a b k Ha Hb Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z_lt_le_dec n k) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r b) by lia. apply Bool.andb_false_r.
  - destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 a n); [reflexivity | lia |].
    apply (Z.lt_le_trans _ k); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_shiftl_small : forall a b k, 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> Z.lor a (Z.shiftl b k) = a + b * 2 ^ k.
Proof.
  intros a b k Ha Hb Hk. pose proof (land_small_shiftl a b k Ha Hb Hk) as H0.
  rewrite <- Z.lxor_lor by exact H0. rewrite <- Z.add_nocarry_lxor by exact H0. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Section Leave3.

Lemma land4_zero_iff : forall w, 0 <= w -> (Z.land w 4 = 0 <-> (w / 4) mod 2 = 0).
Proof.
  intros w Hw. split; intros H.
  - destruct (Z.eq_dec ((w / 4) mod 2) 0) as [E|E]; [exact E|]. exfalso.
    assert (T : Z.testbit (Z.land w 4) 2 = true).
    { rewrite Z.land_spec. apply andb_true_intro. split; [| reflexivity]. apply Z.testbit_true; [lia|]. change (2 ^ 2) with 4. pose proof (Z.mod_pos_bound (w / 4) 2 ltac:(lia)). lia. }
    rewrite H, Z.bits_0 in T. discriminate.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec n 2) as [->|Hne].
    + rewrite (proj2 (Z.testbit_false w 2 ltac:(lia))) by (change (2 ^ 2) with 4; exact H). reflexivity.
    + replace (Z.testbit 4 n) with false; [apply Bool.andb_false_r|]. symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
End Leave3.


Lemma lor_sx_nz : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> (a <> 0 \/ b <> 0) ->
  Z.lor (szwrap 32 a) (szwrap 32 b) mod 2 ^ 64 <> 0.
Proof.
  intros a b Ha Hb Hnz E.
  assert (Ra : - 2 ^ 31 <= szwrap 32 a < 2 ^ 31 /\ (szwrap 32 a = 0 <-> a = 0)) by sxlia.
  assert (Rb : - 2 ^ 31 <= szwrap 32 b < 2 ^ 31 /\ (szwrap 32 b = 0 <-> b = 0)) by sxlia.
  set (x := szwrap 32 a) in *. set (y := szwrap 32 b) in *. clearbody x y.
  destruct (Z_lt_le_dec x 0) as [Hx|Hx]; [| destruct (Z_lt_le_dec y 0) as [Hy|Hy]].
  - assert (L : Z.lor x y < 0) by (apply Z.lor_neg; lia).
    assert (G : - 2 ^ 31 <= Z.lor x y).
    { assert (N : Z.lnot (Z.lor x y) < 2 ^ 31); [| unfold Z.lnot in N; lia].
      rewrite Z.lnot_lor. pose proof (land_upper (Z.lnot x) (Z.lnot y) ltac:(unfold Z.lnot; lia)). unfold Z.lnot in *. lia. }
    Z.to_euclidean_division_equations. lia.
  - assert (L : Z.lor x y < 0) by (apply Z.lor_neg; lia).
    assert (G : - 2 ^ 31 <= Z.lor x y).
    { assert (N : Z.lnot (Z.lor x y) < 2 ^ 31); [| unfold Z.lnot in N; lia].
      rewrite Z.lnot_lor, Z.land_comm. pose proof (land_upper (Z.lnot y) (Z.lnot x) ltac:(unfold Z.lnot; lia)). unfold Z.lnot in *. lia. }
    Z.to_euclidean_division_equations. lia.
  - pose proof (proj1 (lor_lxor_bound x y 31 ltac:(lia) ltac:(lia) ltac:(lia))) as B.
    rewrite Z.mod_small in E by lia. apply Z.lor_eq_0_iff in E. lia.
Qed.

Section Leave4.
End Leave4.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInflate2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition pc_inflate_entry : Z := 0x18fe4.
Definition pc_dispatch : Z := 0x190a4.
Definition pc_leave0 : Z := 0x195e0.
Definition pc_leave : Z := 0x195e4.
Definition pc_epilogue : Z := 0x190c8.
Definition a_jumptab : Z := 0x2e008.
Definition INF_FRAME : Z := 208.
Definition INF_SCRATCH : Z := 4096.

Definition arm_pcs : list Z :=
  [0x19b74; 0x19e90; 0x19b8c; 0x19df8; 0x19e08; 0x19978; 0x19b5c; 0x19b64; 0x19b6c; 0x19100; 0x191f0;
   0x19260; 0x1926c; 0x1a048; 0x19d44; 0x19e28; 0x19f34; 0x198f8; 0x19c7c; 0x193f8; 0x19404; 0x197cc;
   0x19e88; 0x1948c; 0x194a0; 0x1a1bc; 0x1928c; 0x194f8; 0x19e6c; 0x193ac; 0x19e80].
Definition arm_pc (mode : Z) : Z := nth (Z.to_nat (mode - HEAD)) arm_pcs 0x190c4.

Definition saved_slots : list (Z * Z) := [(1, 200); (8, 192); (9, 184); (20, 160); (21, 152); (22, 144)].
Definition lazy_regs : list Z := [3; 4; 18; 19; 23; 24; 25; 26; 27].


Definition offimg (a n : Z) : Prop := a + n <= 0x10000 \/ 0x36000 <= a.

Lemma offimg_sep : forall a n lo k, offimg a n -> 0x10000 <= lo -> lo + k <= 0x36000 -> sep a n lo k.
Proof. intros a n lo k H H1 H2. unfold offimg in H. unfold sep. lia. Qed.

Section Ctx.

  Definition noout_mode (m : Z) : Prop := m = HEAD \/ m = DICTID \/ m = DICT \/ m = MEM \/ m = SYNC.

  Definition same_blocks (s s' : inflate_state) : Prop :=
    is_self_blk s' = is_self_blk s /\ is_window_blk s' = is_window_blk s /\ is_wbits s' = is_wbits s.
  Definition stop_pc (stop : istop) : Z := match stop with SLeave => pc_leave | SRet _ => pc_epilogue end.
  Definition t2_modes (m : Z) : Prop :=
    m = HEAD \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/ m = LIT
    \/ m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/ m = MATCH.
End Ctx.


Section Checker.
  Variable arm_ok : Z -> iw -> bool.
  Variable flush : Z.

  Definition okstep (w : iw) : iw + bool :=
    if arm_ok flush w then
      match dispatch ivar_ref flush w with
      | ARun _ w' => inl w'
      | ALeave _ => inr true
      | ARet _ _ => inr true
      end
    else inr false.

  Definition loop_ok (w : iw) : bool :=
    iterZ (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64)) okstep (fun _ => false) w.
End Checker.

Section Stmts.
  Variable arm_ok : Z -> iw -> bool.
End Stmts.
