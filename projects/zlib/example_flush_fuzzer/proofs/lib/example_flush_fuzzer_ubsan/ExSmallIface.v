(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Export ZlibStmtBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section FXG. Context {fxG : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Inductive iexit : Type := IX_W | IX_E (err : Z) | IX_N.
Inductive bexit : Type := BX_F | BX_E (err : Z).

Record small_model : Type := SMALL_MODEL {
  sm_cbound    : Z -> Z;
  sm_ds_compr  : list Z -> list Z;
  sm_ia_exit   : list Z -> Z -> iexit;
  sm_ib_exit   : list Z -> Z -> bexit;
  sm_iu_N      : list Z -> Z -> list Z;
  sm_iu_F      : list Z -> Z -> list Z;
  sm_memcmp_ne : list Z -> list Z -> Z -> bool;
  sm_ia_errs   : list Z;
  sm_ib_errs   : list Z;
  sm_cbound_eq   : forall n, 0 <= n -> sm_cbound n = n + n / 4096 + n / 16384 + n / 33554432 + 13;
  sm_ds_compr_len : forall d, Z.of_nat (length (sm_ds_compr d)) = sm_cbound (Z.of_nat (length d));
  sm_iu_N_len  : forall c n, 0 <= n -> Z.of_nat (length (sm_iu_N c n)) = n;
  sm_iu_F_len  : forall c n, 0 <= n -> Z.of_nat (length (sm_iu_F c n)) = n;
  sm_ia_errs_ok : forall c n e, sm_ia_exit c n = IX_E e -> In e sm_ia_errs;
  sm_ib_errs_ok : forall c n e, sm_ib_exit c n = BX_E e -> In e sm_ib_errs
}.

Definition cbound (n : Z) : Z := n + n / 4096 + n / 16384 + n / 33554432 + 13.

Section WithSegs.
Variable RSEGS : list Segment.
Context {fx : FPState}.

Definition zbytes (bs : list byte) : list Z := map (fun b : byte => bv_unsigned b) bs.
Definition holds (m : word -> option byte) (a : Z) (zs : list Z) : Prop :=
  rdn RSEGS m (Z_to_bv 64 a) (length zs) = Some (map (fun z => Z_to_bv 8 z) zs).
Definition zeros_at (m : word -> option byte) (a n : Z) : Prop :=
  rdn RSEGS m (Z_to_bv 64 a) (Z.to_nat n) = Some (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Definition cell8 (m : word -> option byte) (a v : Z) : Prop :=
  rdn RSEGS m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 v).
Definition cell4 (m : word -> option byte) (a v : Z) : Prop :=
  rdn RSEGS m (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 v).
Definition cellw (m : word -> option byte) (a : Z) (v : word) : Prop :=
  rdn RSEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).

Definition apart (a na b nb : Z) : Prop := a + na <= b \/ b + nb <= a.

Definition blk_ok (m : word -> option byte) (img_top b sz : Z) : Prop :=
  b mod 16 = 0 /\ 0 < b /\ b + sz <= ZCEIL /\ (b + sz <= 0x10000 \/ img_top <= b) /\
  store_ok RSEGS m (Z_to_bv 64 b) (Z.to_nat sz) = true.
Definition blk_okz (m : word -> option byte) (img_top zc b sz : Z) : Prop :=
  b mod 16 = 0 /\ 0 < b /\ b + sz <= zc /\ (b + sz <= 0x10000 \/ img_top <= b) /\
  store_ok RSEGS m (Z_to_bv 64 b) (Z.to_nat sz) = true.

Fixpoint apart_from_all (a na : Z) (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (b, nb) :: t => apart a na b nb /\ apart_from_all a na t
  end.
Fixpoint all_apart (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (a, na) :: t => apart_from_all a na t /\ all_apart t
  end.

End WithSegs.

End FXG.
