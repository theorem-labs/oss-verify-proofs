(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma bignorm_b_mul_nocarry_z : forall bs k len (y : Z) (c : word),
  bignorm_b bs len -> (1 <= len)%Z -> (8 * len <= Z.of_nat (length bs))%Z -> k = (8 * (len - 1))%Z -> (0 < y < 18446744073709551616)%Z ->
  ((Z.shiftr (bv_unsigned (limbz bs k) * y) 64 +
    Z.b2z ((bv_unsigned (limbz bs k) * y + bv_unsigned c) mod 18446744073709551616 <?
           (bv_unsigned (limbz bs k) * y) mod 18446744073709551616)) mod 18446744073709551616 = 0)%Z ->
  bignorm_b (upd_bytes bs (Z.to_nat k) (le8 (Z_to_bv 64 (bv_unsigned (limbz bs k) * y + bv_unsigned c)))) len.
Proof.
  intros bs k len y c [E|NZ] H1 Hl -> HY H; [exfalso; lia|].
  apply bignorm_b_upd_top; [lia | lia | reflexivity|].
  rewrite unsigned_lit_wrap. change (2 ^ 64)%Z with 18446744073709551616%Z.
  pose proof (bv_unsigned_in_range 64 (limbz bs (8 * (len - 1)))) as RA. pose proof (bv_unsigned_in_range 64 c) as RC.
  unfold bv_modulus in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in *.
  apply small_mul_top_nz; [lia | lia | lia | exact H].
Qed.

Definition P5U_SMALL : Z := 0x1c920.
Definition p5u_small_tbl : list byte :=
  Eval vm_compute in match image_bytes usegs P5U_SMALL 216 with Some bs => bs | None => [] end.
Lemma p5u_small_len : length p5u_small_tbl = 216%nat.
Proof. reflexivity. Qed.
Lemma p5u_small_at : forall m, mem_inv usegs m -> bytes_at usegs m P5U_SMALL p5u_small_tbl.
Proof.
  intros m MI.
  assert (RO : ro_cells usegs m P5U_SMALL [CB (length p5u_small_tbl) p5u_small_tbl]).
  { apply (ro_cells_image usegs m P5U_SMALL p5u_small_tbl MI); [vm_compute; reflexivity | unfold P5U_SMALL; lia | unfold P5U_SMALL; cbn; lia]. }
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma p5u_small_nz : forall e, (0 <= e <= 26)%Z -> (0 < bv_unsigned (limbz p5u_small_tbl (8 * e)))%Z.
Proof.
  intros e H.
  assert (C : (e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5 \/ e = 6 \/ e = 7 \/ e = 8 \/ e = 9 \/ e = 10 \/ e = 11 \/ e = 12 \/ e = 13 \/
               e = 14 \/ e = 15 \/ e = 16 \/ e = 17 \/ e = 18 \/ e = 19 \/ e = 20 \/ e = 21 \/ e = 22 \/ e = 23 \/ e = 24 \/ e = 25 \/ e = 26)%Z) by lia.
  repeat (destruct C as [->|C]; [vm_compute; reflexivity|]). subst e. vm_compute. reflexivity.
Qed.
