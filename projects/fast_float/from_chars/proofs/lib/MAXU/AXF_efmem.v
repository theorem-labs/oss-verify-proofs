(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AXF_efbz.
Import ListNotations AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma wb_byte : forall m a w z j, 0 <= a -> a + Z.of_nat w <= 2^64 -> (w <= 8)%nat -> (j < w)%nat ->
  bview SEGS (wbytes m (wa a) (word_to_le_bytes w (wa z))) (a + Z.of_nat j) = Some (le_byte z w j).
Proof.
  intros m a w z j H0 H1 Hw Hj.
  rewrite (bview_some_byte SEGS _ _ (nth j (word_to_le_bytes w (wa z)) (Z_to_bv 8 0))).
  - rewrite le_byte_Z_to_le_bytes by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
    apply f_equal. apply Z.mod_small. unfold le_byte. apply Z.mod_pos_bound. lia.
  - lia.
  - apply wbytes_at_wa; [lia | unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia | unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia].
Qed.

Lemma wb_out : forall m a bs x, 0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 -> 0 <= x < 2^64 ->
  (x < a \/ a + Z.of_nat (length bs) <= x) -> bview SEGS (wbytes m (wa a) bs) x = bview SEGS m x.
Proof.
  intros m a bs x H0 H1 Hx Hd. apply bview_ext. apply MngWb.wbytes_out; rewrite ?u_wa_small by lia; first [assumption | lia].
Qed.

Lemma wb_byte' : forall m a w z j x, x = a + Z.of_nat j -> 0 <= a -> a + Z.of_nat w <= 2^64 -> (w <= 8)%nat -> (j < w)%nat ->
  bview SEGS (wbytes m (wa a) (word_to_le_bytes w (wa z))) x = Some (le_byte z w j).
Proof. intros m a w z j x -> H0 H1 H2 H3. apply wb_byte; assumption. Qed.

Section EFM.
Variables (m : word -> option byte) (idx n mem sz st off : Z).
Hypothesis Rst : 17 <= st <= 2^63 - 1.
Hypothesis Rend : st + 16 * sz <= 2^63.
Hypothesis Roff : 0 <= off <= 255.
Hypothesis Rn : 1 <= n.
Hypothesis Fit : n + 4 + 16 * off <= 16 * sz.

Ltac wout := rewrite wb_out by (unfold word_to_le_bytes; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat]; lia).

(* [comment removed for export] *)
#[using="Rst Rend Roff Rn Fit"] Lemma efb_mem_out : forall x, 0 <= x < 2^64 -> ~ (st - 3 <= x < st + 16 * sz - 4) ->
  bview SEGS (efb_mem m idx n mem sz st off) x = bview SEGS m x.
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  intros x Hx Hno. unfold efb_mem, efb_rsv, le. cbv zeta.
  wout.
  assert (TAIL : forall mm, bview SEGS mm x = bview SEGS m x ->
            bview SEGS (wbytes (wbytes mm (wa (st + 16 * off - 3)) (word_to_le_bytes 1 (wa idx)))
                                (wa (st + 16 * off - 2)) (word_to_le_bytes 2 (wa ((st + 16 * off - mem - 16) / 16)))) x = bview SEGS m x).
  { intros mm Hmm. wout. wout. exact Hmm. }
  assert (HEAD : bview SEGS (if off =? 0 then m else wbytes (wbytes (wbytes m (wa (st - 3)) (word_to_le_bytes 1 (wa 224))) (wa (st - 2)) (word_to_le_bytes 2 (wa off)))
                                (wa (st + 16 * off - 4)) (word_to_le_bytes 1 (wa 0))) x = bview SEGS m x).
  { destruct (off =? 0) eqn:Eo; [reflexivity|]. apply Z.eqb_neq in Eo. wout. wout. wout. reflexivity. }
  destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:E0.
  - apply TAIL. exact HEAD.
  - apply Z.eqb_neq in E0. destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5.
    + wout. apply TAIL. exact HEAD.
    + apply Z.ltb_ge in E5. wout. wout. wout. apply TAIL. exact HEAD.
Qed.

Definition efb_code' : Z := efb_code (efb_rsv sz n off).

Ltac wb k := apply (wb_byte' _ _ _ _ k); [cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | lia].

(* [comment removed for export] *)
#[using="Rst Rend Roff Rn Fit"] Lemma efb_mem_p3 : bview SEGS (efb_mem m idx n mem sz st off) (st + 16 * off - 3) = Some (le_byte (idx + 32 * efb_code') 1 0).
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  unfold efb_mem, efb_code', le. cbv zeta. wb 0%nat.
Qed.

(* [comment removed for export] *)
#[using="Rst Rend Roff Rn Fit"] Lemma efb_mem_p2 : forall j, (j < 2)%nat ->
  bview SEGS (efb_mem m idx n mem sz st off) (st + 16 * off - 2 + Z.of_nat j) = Some (le_byte ((st + 16 * off - mem - 16) / 16) 2 j).
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  intros j Hj. unfold efb_mem, efb_rsv, le. cbv zeta. wout.
  destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:E0.
  - wb j.
  - apply Z.eqb_neq in E0. destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5.
    + wout. wb j.
    + apply Z.ltb_ge in E5. wout. wout. wout. wb j.
Qed.

(* [comment removed for export] *)
#[using="Rst Rend Roff Rn Fit"] Lemma efb_mem_hdr : off <> 0 ->
  bview SEGS (efb_mem m idx n mem sz st off) (st - 3) = Some (le_byte 224 1 0) /\
  (forall j, (j < 2)%nat -> bview SEGS (efb_mem m idx n mem sz st off) (st - 2 + Z.of_nat j) = Some (le_byte off 2 j)) /\
  bview SEGS (efb_mem m idx n mem sz st off) (st + 16 * off - 4) = Some (le_byte 0 1 0).
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  intros Hoff. assert (Ho1 : 1 <= off) by lia.
  unfold efb_mem, efb_rsv, le. cbv zeta.
  replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hoff).
  split; [|split].
  - wout. destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:E0;
      [|apply Z.eqb_neq in E0; destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5; [|apply Z.ltb_ge in E5; wout; wout]; wout].
    all: wout; wout; wout; wout; wb 0%nat.
  - intros j Hj. wout. destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:E0;
      [|apply Z.eqb_neq in E0; destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5; [|apply Z.ltb_ge in E5; wout; wout]; wout].
    all: wout; wout; wout; wb j.
  - wout. destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:E0;
      [|apply Z.eqb_neq in E0; destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5; [|apply Z.ltb_ge in E5; wout; wout]; wout].
    all: wout; wout; wb 0%nat.
Qed.

(* [comment removed for export] *)
#[using="Rst Rend Roff Rn Fit"] Lemma efb_mem_rsv1 : efb_rsv sz n off <> 0 ->
  bview SEGS (efb_mem m idx n mem sz st off) (st + 16 * off + n) = Some (le_byte 0 1 0).
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  intros Hr. unfold efb_mem, le. cbv zeta. unfold efb_rsv in *. wout.
  replace (16 * sz - 4 - 16 * off - n =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
  destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5.
  - wb 0%nat.
  - apply Z.ltb_ge in E5. wout. destruct (Z.eq_dec (16 * sz - 4 - 16 * off - n) 5) as [E|E].
    + wb 0%nat.
    + wout. wb 0%nat.
Qed.

#[using="Rst Rend Roff Rn"] Lemma efb_mem_rsv5 : 5 <= efb_rsv sz n off ->
  bview SEGS (efb_mem m idx n mem sz st off) (st + 16 * sz - 4 - 5) = Some (le_byte 0 1 0) /\
  (forall j, (j < 4)%nat -> bview SEGS (efb_mem m idx n mem sz st off) (st + 16 * sz - 4 - 4 + Z.of_nat j) = Some (le_byte (efb_rsv sz n off) 4 j)).
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn : LiaFast.U) => LiaFast.u0).
  intros Hr. unfold efb_mem, le. cbv zeta. unfold efb_rsv in *.
  replace (16 * sz - 4 - 16 * off - n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (16 * sz - 4 - 16 * off - n <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  split.
  - wout. wout. wb 0%nat.
  - intros j Hj. wout. wb j.
Qed.

End EFM.
