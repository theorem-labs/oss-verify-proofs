(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_lkit I_lift.
From stdpp Require list_basics.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_b2bc : Z := 0x88830.          (* [comment removed for export] *)
Definition e_b2bd : Z := 0x88bf0.          (* [comment removed for export] *)
Definition e_memcmp : Z := 0x43234.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nZ_of (len : Z) : Z := len + 600 + len / 100.
Definition bs_of (len : Z) : Z := Z.min (len mod 11) 8 + 1.
Definition wf_of (len : Z) : Z := len mod 251.

Definition M100 : Z := 0x28f5c28f5c28f5c3.   (* [comment removed for export] *)
Definition M11  : Z := 0x2e8ba2e8ba2e8ba3.   (* [comment removed for export] *)
Definition M251 : Z := 0x5197f7d73404147.    (* [comment removed for export] *)

Lemma div100_magic : forall x, 0 <= x < 2 ^ 32 -> (x / 4 * M100) / 2 ^ 64 / 4 = x / 100.
Proof.
  intros x Hx. unfold M100. rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) 4) by lia.
  set (y := x / 4). assert (Hy : 0 <= y < 2 ^ 30) by (subst y; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace (x / 100) with (y / 25) by (subst y; rewrite (Zdiv.Zdiv_Zdiv x 4 25) by lia; reflexivity).
  symmetry. apply Z.div_unique_pos with (r := 11 * (y / 25) + (y mod 25) * 2951479051793528259).
  - pose proof (Z.mod_pos_bound y 25 ltac:(lia)). pose proof (Z.div_pos y 25 ltac:(lia) ltac:(lia)).
    assert (y / 25 < 2 ^ 26) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod y 25 ltac:(lia)). nia.
Qed.

Lemma div11_magic : forall x, 0 <= x < 2 ^ 32 -> (x * M11) / 2 ^ 64 / 2 = x / 11.
Proof.
  intros x Hx. unfold M11. rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) 2) by lia.
  symmetry. apply Z.div_unique_pos with (r := (x / 11) + (x mod 11) * 3353953467947191203).
  - pose proof (Z.mod_pos_bound x 11 ltac:(lia)). pose proof (Z.div_pos x 11 ltac:(lia) ltac:(lia)).
    assert (x / 11 < 2 ^ 29) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod x 11 ltac:(lia)). nia.
Qed.

Lemma div251_magic : forall x, 0 <= x < 2 ^ 32 ->
  let q0 := (x * M251) / 2 ^ 64 in ((x - q0) / 2 + q0) / 2 ^ 7 = x / 251.
Proof.
  intros x Hx. cbv zeta. unfold M251.
  set (q0 := x * 367465021388636487 / 2 ^ 64).
  assert (Q0 : 0 <= q0 <= x).
  { subst q0. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  replace ((x - q0) / 2 + q0) with ((x + q0) / 2).
  2:{ replace (x + q0) with ((x - q0) + q0 * 2) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite (Zdiv.Zdiv_Zdiv _ 2 (2 ^ 7)) by lia.
  (* [comment removed for export] *)
  replace (x + q0) with ((x * 2 ^ 64 + x * 367465021388636487) / 2 ^ 64).
  2:{ subst q0. rewrite Z.add_comm, <- Z.div_add_l by lia. f_equal. lia. }
  rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) (2 * 2 ^ 7)) by lia.
  replace (x * 2 ^ 64 + x * 367465021388636487) with (x * (2 ^ 64 + 367465021388636487)) by lia.
  symmetry. apply Z.div_unique_pos with (r := 157 * (x / 251) + (x mod 251) * (2 ^ 64 + 367465021388636487)).
  - pose proof (Z.mod_pos_bound x 251 ltac:(lia)). pose proof (Z.div_pos x 251 ltac:(lia) ltac:(lia)).
    assert (x / 251 < 2 ^ 25) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod x 251 ltac:(lia)). nia.
Qed.


(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. lia.
Qed.
Lemma land_m32_al : forall x, 0 <= x < 2^64 -> x mod 32 = 0 -> Z.land x 18446744073709551584 = x.
Proof. intros x Hx H. rewrite land_m32 by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.

(* [comment removed for export] *)
Lemma wr_at_app : forall (m : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at bsegs m a (n1 + n2) <-> wr_at bsegs m a n1 /\ wr_at bsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall (m : mem) A cs1 cs2,
  rw_cells bsegs m A (cs1 ++ cs2) <-> rw_cells bsegs m A cs1 /\ rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_head : forall (m : mem) A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c].
Proof. intros m A c cs H. exact (proj1 (proj1 (rw_cells_app m A [c] cs) H)). Qed.

Lemma rw_cells_tail : forall (m : mem) A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. pose proof (proj2 (proj1 (rw_cells_app m A [c] cs) H)) as H2. cbn [cells_size Nat.add] in H2.
  rewrite Nat.add_0_r in H2. exact H2. Qed.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at bsegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H1 H2 H3. split; [lia| split; [lia|]].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)

Section Kit.
Variable RT : rt_sig.

(* [comment removed for export] *)
Lemma aclient_mono : forall live frames sp live' frames' sp' a,
  aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
  aclient live' frames' sp' a.
Proof.
  intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
  - left. lia.
  - right; left. exact H.
  - right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
  - right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
  - right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
  intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
  split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

End Kit.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs D_kit I_lkit I_lift.
From stdpp Require list_basics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_b2bc : Z := 0x87d98.          (* [comment removed for export] *)
Definition e_b2bd : Z := 0x8814c.          (* [comment removed for export] *)
Definition e_memcmp : Z := 0x4334c.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nZ_of (len : Z) : Z := len + 600 + len / 100.
Definition bs_of (len : Z) : Z := Z.min (len mod 11) 8 + 1.
Definition wf_of (len : Z) : Z := len mod 251.

Definition M100 : Z := 0x28f5c28f5c28f5c3.   (* [comment removed for export] *)
Definition M11  : Z := 0x2e8ba2e8ba2e8ba3.   (* [comment removed for export] *)
Definition M251 : Z := 0x5197f7d73404147.    (* [comment removed for export] *)

Lemma div100_magic : forall x, 0 <= x < 2 ^ 32 -> (x / 4 * M100) / 2 ^ 64 / 4 = x / 100.
Proof.
  intros x Hx. unfold M100. rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) 4) by lia.
  set (y := x / 4). assert (Hy : 0 <= y < 2 ^ 30) by (subst y; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace (x / 100) with (y / 25) by (subst y; rewrite (Zdiv.Zdiv_Zdiv x 4 25) by lia; reflexivity).
  symmetry. apply Z.div_unique_pos with (r := 11 * (y / 25) + (y mod 25) * 2951479051793528259).
  - pose proof (Z.mod_pos_bound y 25 ltac:(lia)). pose proof (Z.div_pos y 25 ltac:(lia) ltac:(lia)).
    assert (y / 25 < 2 ^ 26) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod y 25 ltac:(lia)). nia.
Qed.

Lemma div11_magic : forall x, 0 <= x < 2 ^ 32 -> (x * M11) / 2 ^ 64 / 2 = x / 11.
Proof.
  intros x Hx. unfold M11. rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) 2) by lia.
  symmetry. apply Z.div_unique_pos with (r := (x / 11) + (x mod 11) * 3353953467947191203).
  - pose proof (Z.mod_pos_bound x 11 ltac:(lia)). pose proof (Z.div_pos x 11 ltac:(lia) ltac:(lia)).
    assert (x / 11 < 2 ^ 29) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod x 11 ltac:(lia)). nia.
Qed.

Lemma div251_magic : forall x, 0 <= x < 2 ^ 32 ->
  let q0 := (x * M251) / 2 ^ 64 in ((x - q0) / 2 + q0) / 2 ^ 7 = x / 251.
Proof.
  intros x Hx. cbv zeta. unfold M251.
  set (q0 := x * 367465021388636487 / 2 ^ 64).
  assert (Q0 : 0 <= q0 <= x).
  { subst q0. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  replace ((x - q0) / 2 + q0) with ((x + q0) / 2).
  2:{ replace (x + q0) with ((x - q0) + q0 * 2) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite (Zdiv.Zdiv_Zdiv _ 2 (2 ^ 7)) by lia.
  (* [comment removed for export] *)
  replace (x + q0) with ((x * 2 ^ 64 + x * 367465021388636487) / 2 ^ 64).
  2:{ subst q0. rewrite Z.add_comm, <- Z.div_add_l by lia. f_equal. lia. }
  rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) (2 * 2 ^ 7)) by lia.
  replace (x * 2 ^ 64 + x * 367465021388636487) with (x * (2 ^ 64 + 367465021388636487)) by lia.
  symmetry. apply Z.div_unique_pos with (r := 157 * (x / 251) + (x mod 251) * (2 ^ 64 + 367465021388636487)).
  - pose proof (Z.mod_pos_bound x 251 ltac:(lia)). pose proof (Z.div_pos x 251 ltac:(lia) ltac:(lia)).
    assert (x / 251 < 2 ^ 25) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod x 251 ltac:(lia)). nia.
Qed.


(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. lia.
Qed.
Lemma land_m32_al : forall x, 0 <= x < 2^64 -> x mod 32 = 0 -> Z.land x 18446744073709551584 = x.
Proof. intros x Hx H. rewrite land_m32 by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.

(* [comment removed for export] *)
Lemma wr_at_app : forall (m : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at asegs m a (n1 + n2) <-> wr_at asegs m a n1 /\ wr_at asegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall (m : mem) A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_head : forall (m : mem) A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. exact (proj1 (proj1 (rw_cells_app m A [c] cs) H)). Qed.

Lemma rw_cells_tail : forall (m : mem) A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. pose proof (proj2 (proj1 (rw_cells_app m A [c] cs) H)) as H2. cbn [cells_size Nat.add] in H2.
  rewrite Nat.add_0_r in H2. exact H2. Qed.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H1 H2 H3. split; [lia| split; [lia|]].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)

Section Kit.
Variable RT : rt_sig.

(* [comment removed for export] *)
Lemma aclient_mono : forall live frames sp live' frames' sp' a,
  aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
  aclient live' frames' sp' a.
Proof.
  intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
  - left. lia.
  - right; left. exact H.
  - right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
  - right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
  - right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
  intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
  split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

End Kit.
