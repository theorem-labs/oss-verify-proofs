(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition pc_inflate_entry : Z := 0x18fe4.
Definition pc_dispatch : Z := 0x190a4.
Definition pc_leave0 : Z := 0x195e0.
Definition pc_leave : Z := 0x195e4.
Definition pc_epilogue : Z := 0x190c8.
Definition a_jumptab : Z := 0x2e138.
Definition INF_FRAME : Z := 208.
Definition INF_SCRATCH : Z := 4096.

Definition arm_pcs : list Z :=
  [0x19b74; 0x19f4c; 0x19b8c; 0x19eb4; 0x19ec4; 0x19978; 0x19b5c; 0x19b64; 0x19b6c; 0x19100; 0x191f0;
   0x19260; 0x1926c; 0x1a104; 0x19e00; 0x19ee4; 0x19ff0; 0x198f8; 0x19c7c; 0x193f8; 0x19404; 0x197cc;
   0x19f44; 0x1948c; 0x194a0; 0x1a278; 0x1928c; 0x194f8; 0x19f28; 0x193ac; 0x19f3c].
Definition arm_pc (mode : Z) : Z := nth (Z.to_nat (mode - HEAD)) arm_pcs 0x190c4.

Definition saved_slots : list (Z * Z) := [(1, 200); (8, 192); (9, 184); (20, 160); (21, 152); (22, 144)].

Definition lazy_regs : list Z := [3; 4; 18; 19; 23; 24; 25; 26; 27].

Definition offimg (a n : Z) : Prop := a + n <= 0x10000 \/ 0x36130 <= a.

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
