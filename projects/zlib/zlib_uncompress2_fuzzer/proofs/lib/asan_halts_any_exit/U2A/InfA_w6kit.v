(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes Image ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AObj InfATables InfPure_table.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma zx16_small : forall e, 0 <= e < 65536 -> zx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e H. unfold zx16. rewrite unsigned_lit by lia. change (2 ^ 16) with 65536. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma shl1_2x : forall v, Z.shiftl v 1 = 2 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. lia. Qed.
Lemma land_m32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land7_mod : forall h, 0 <= h -> Z.land h 7 = h mod 8.
Proof. intros h H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at asegs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 2 * i) ->
  ov_read_bytes asegs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i)%Z with (Z.of_nat (2 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, (skipn_all2 (u16s pre)), Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, (firstn_all2 (le2 w)) by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma fws_order : fws order_f 19 = zw order_l.
Proof. vm_compute. reflexivity. Qed.

Lemma order_f_range : forall i, 0 <= i < 19 -> 0 <= order_f i < 19.
Proof.
  intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  assert (H : (Z.to_nat i < 19)%nat) by lia. revert H. generalize (Z.to_nat i). clear. intros j H.
  do 19 (destruct j as [|j]; [vm_compute; split; [discriminate| reflexivity]|]). lia.
Qed.

Lemma order_read : forall (m : word -> option byte) i a, mem_inv asegs m -> 0 <= i < 19 -> a = wa (141376 + 2 * i) ->
  ov_read_bytes asegs m a 2 = Some (le2 (Z_to_bv 64 (order_f i))).
Proof.
  intros m i a MI Hi Ea. pose proof (order_bytes m MI) as HB. rewrite <- fws_order in HB.
  eapply (u16ro_read m 141376 (fws order_f 19) i); [exact HB| | lia| exact Ea].
  rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma order_check : forall (m : word -> option byte) i,
  shadow_bytes m 2147468552 2147468556 (fun _ => 0) -> shadow_bytes m 2147468556 2147468557 (fun _ => 6) -> 0 <= i < 19 ->
  exists b : byte,
    ov_read_bytes asegs m (Z_to_bv 64 (Z.shiftr (141376 + 2 * i) 3 + 2147450880)) 1 = Some [b] /\
    (sval b = 0 \/ (0 < sval b <= 7 /\ (141376 + 2 * i) mod 8 + 2 - 1 < sval b)).
Proof.
  intros m i S0 S6 Hi.
  assert (EA : Z.shiftr (141376 + 2 * i) 3 + 2147450880 = 2147468552 + i / 4).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  rewrite EA.
  destruct (Z_lt_dec i 16) as [L|G].
  - exists (Z_to_bv 8 0). split; [| left; apply sval_zero].
    apply (ov_read1_of_shadow_bytes asegs m 2147468552 2147468556 (fun _ => 0) (2147468552 + i / 4) S0). Z.div_mod_to_equations. lia.
  - exists (Z_to_bv 8 6). split.
    + replace (2147468552 + i / 4) with 2147468556 by (Z.div_mod_to_equations; lia).
      apply (ov_read1_of_shadow_bytes asegs m 2147468556 2147468557 (fun _ => 6) 2147468556 S6). lia.
    + right. rewrite sval_lit by lia. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

End CANSEC1.
