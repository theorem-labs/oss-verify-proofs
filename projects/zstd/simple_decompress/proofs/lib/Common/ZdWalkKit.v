(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma byte_lit8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Definition sx8 (c : Z) : Z := if c <? 128 then c else c - 256.
Lemma byte_sig8 : forall c, 0 <= c < 256 -> bv_signed (Z_to_bv 8 c) = sx8 c.
Proof.
  intros c Hc. rewrite Z_to_bv_signed. unfold sx8, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  destruct (Z.ltb_spec c 128).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zd_nth_map : forall (src : list Z) i, 0 <= i < Z.of_nat (length src) ->
  nth_error (map (Z_to_bv 8) src) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i src)).
Proof.
  intros src i Hi. unfold Znth. rewrite nth_error_map.
  rewrite (nth_error_nth' src 0) by lia. reflexivity.
Qed.

Section SRC.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma zd_src_rd : forall m SRC (src : list Z) i a,
  bytes_at segs m SRC (map (Z_to_bv 8) src) -> 0 <= i < Z.of_nat (length src) -> a = SRC + i ->
  ov_read_bytes segs m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 (Znth i src)].
Proof.
  intros m SRC src i a SB Hi ->.
  eapply (u8ro_read segs m SRC _ i); [exact SB| apply zd_nth_map; exact Hi | lia | unfold wa; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma zd_src_skipn : forall m SRC (src : list Z) n,
  bytes_at segs m SRC (map (Z_to_bv 8) src) -> 0 <= n <= Z.of_nat (length src) ->
  bytes_at segs m (SRC + n) (map (Z_to_bv 8) (skipn (Z.to_nat n) src)).
Proof.
  intros m SRC src n SB Hn.
  rewrite <- (firstn_skipn (Z.to_nat n) src) in SB. rewrite map_app in SB.
  apply (proj1 (bytes_at_app segs m SRC _ _)) in SB. destruct SB as [_ SB].
  rewrite length_map, firstn_length_le in SB by lia. rewrite Z2Nat.id in SB by lia. exact SB.
Qed.
End SRC.

(* [comment removed for export] *)
Lemma rw_cells_recell : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[WF B] W] WF' E.
  assert (SZ : cells_size cs' = cells_size cs).
  { rewrite <- (cells_bytes_length cs') by exact WF'. rewrite <- (cells_bytes_length cs) by exact WF. rewrite E. reflexivity. }
  split; [split; [exact WF'| rewrite E; exact B]| rewrite SZ; exact W].
Qed.

(* [comment removed for export] *)
Lemma wr_at_app2 : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app2 by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma img_rd8 : forall segs m A v,
  mem_inv segs m -> ro_bytes_b segs A (le8 (Z_to_bv 64 v)) = true -> 0 <= A -> A + 8 <= 2^64 ->
  ov_read_bytes segs m (Z_to_bv 64 A) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros segs m A v MI RB HA HB.
  pose proof (ro_cells_image segs m A (le8 (Z_to_bv 64 v)) MI RB HA ltac:(rewrite length_le8; lia)) as RO.
  rewrite length_le8 in RO.
  rewrite (ro_cells_read_at segs m A [CB 8 (le8 (Z_to_bv 64 v))] 0%nat (CB 8 (le8 (Z_to_bv 64 v))) 8 (Z_to_bv 64 A) RO);
    [reflexivity | reflexivity | reflexivity | unfold wa; f_equal; lia].
Qed.

(* [comment removed for export] *)
Lemma byte_forall : forall (P : Z -> bool),
  forallb P (map Z.of_nat (seq 0 256)) = true -> forall b, 0 <= b < 256 -> P b = true.
Proof.
  intros P H b Hb. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.
(* [comment removed for export] *)
Ltac byte_brute_tac b :=
  pattern b;
  lazymatch goal with
  | |- (fun x => @eq Z (@?l x) (@?r x)) _ =>
      let H := fresh in
      assert (H : 0 <= b < 256) by lia;
      apply Z.eqb_eq; revert H; generalize b; intros bb Hbb;
      apply (byte_forall (fun x => Z.eqb (l x) (r x))); [vm_compute; reflexivity | exact Hbb]
  end.
Tactic Notation "byte_brute" constr(b) := byte_brute_tac b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_add_disj : forall k x y, 0 <= k -> 0 <= y < 2^k -> x mod 2^k = 0 -> Z.lor x y = x + y.
Proof.
  intros k x y Hk Hy Hx. symmetry. apply Z.add_nocarry_lor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - replace (Z.testbit x i) with false; [reflexivity|].
    symmetry. rewrite <- (Z.mod_pow2_bits_low x k i) by lia. rewrite Hx. apply Z.bits_0.
  - replace (Z.testbit y i) with false; [apply andb_false_r|].
    symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia| lia].
Qed.

(* [comment removed for export] *)
Ltac lor2add_side := first [ lia | split; lia | Z.div_mod_to_equations; lia ].
Ltac lor2add1 x y :=
  first [ rewrite (lor_add_disj 8 x y) by lor2add_side | rewrite (lor_add_disj 16 x y) by lor2add_side
        | rewrite (lor_add_disj 24 x y) by lor2add_side | rewrite (lor_add_disj 32 x y) by lor2add_side
        | rewrite (lor_add_disj 40 x y) by lor2add_side | rewrite (lor_add_disj 48 x y) by lor2add_side
        | rewrite (lor_add_disj 56 x y) by lor2add_side ].
Ltac lor2add :=
  match goal with
  | |- context [Z.lor ?x ?y] => first [ lor2add1 x y | rewrite (Z.lor_comm x y); lor2add1 y x ]
  end.

(* [comment removed for export] *)
Ltac shl2mul :=
  repeat match goal with
  | |- context [Z.shiftl ?x ?k] => is_Zlit_zb k; rewrite (Z.shiftl_mul_pow2 x k) by lia;
        let v := eval vm_compute in (2^k) in change (2^k) with v
  end.
Ltac shr2div :=
  repeat match goal with
  | |- context [Z.shiftr ?x ?k] => is_Zlit_zb k; rewrite (Z.shiftr_div_pow2 x k) by lia;
        let v := eval vm_compute in (2^k) in change (2^k) with v
  end.

(* [comment removed for export] *)
Definition zsx32 (v : Z) : Z := if v <? 2147483648 then v else v + 18446744069414584320.
Lemma sx_le32_form : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  ((sx8 b3 mod 18446744073709551616 * 16777216) mod 18446744073709551616) + b2 * 65536 + (b1 * 256 + b0)
  = zsx32 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. rewrite Z.mul_mod_idemp_l by lia. unfold zsx32, sx8.
  destruct (Z.ltb_spec b3 128).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) 2147483648); lia.
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) 2147483648); lia.
Qed.
Lemma srliw4_zsx32 : forall v, 0 <= v < 4294967296 -> bv_swrap 32 (bv_wrap 32 (zsx32 v) ≫ 4) = v / 16.
Proof.
  intros v Hv. rewrite wrap32_eq. unfold zsx32.
  assert (E : (if v <? 2147483648 then v else v + 18446744069414584320) mod 4294967296 = v).
  { destruct (Z.ltb_spec v 2147483648); [apply Z.mod_small; lia|].
    replace (v + 18446744069414584320) with (v + 4294967295 * 4294967296) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite E. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. apply swrap32_small. Z.div_mod_to_equations. lia.
Qed.
Lemma zsx32_small : forall v, 0 <= v < 2147483648 -> zsx32 v = v.
Proof. intros v Hv. unfold zsx32. destruct (Z.ltb_spec v 2147483648); lia. Qed.
Lemma zsx32_range : forall v, 0 <= v < 4294967296 -> 0 <= zsx32 v < 18446744073709551616.
Proof. intros v Hv. unfold zsx32. destruct (Z.ltb_spec v 2147483648); lia. Qed.
Lemma zsx32_eq_lit : forall v c, 0 <= v < 4294967296 -> 0 <= c < 4294967296 -> (zsx32 v = zsx32 c <-> v = c).
Proof. intros v c Hv Hc. unfold zsx32. destruct (Z.ltb_spec v 2147483648); destruct (Z.ltb_spec c 2147483648); lia. Qed.

(* [comment removed for export] *)
Lemma sx32w_small : forall z, 0 <= z < 2147483648 -> Mem.sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold Mem.sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity.
Qed.
Lemma zx32w_small : forall z, 0 <= z < 4294967296 -> Mem.zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold Mem.zx32. rewrite unsigned_lit by lia. change (2^32) with 4294967296. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac zify_lts K :=
  unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zs := zstep; shl2mul; repeat lor2add.
(* [comment removed for export] *)
Ltac zlb_tac segs SB OK i :=
  lazymatch type of SB with
  | bytes_at segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
      let RD := fresh "RD" in
      assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
        by (eapply zd_src_rd; [exact SB | lia | reflexivity]);
      first [ assert (0 <= Znth i src < 256) by assumption
            | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
      zstep; cbv beta; rewrite (byte_lit8 (Znth i src)) by assumption; clear RD; shl2mul; repeat lor2add
  end.
(* [comment removed for export] *)
Ltac zlbs_tac segs SB OK i :=
  lazymatch type of SB with
  | bytes_at segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
      let RD := fresh "RD" in
      assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
        by (eapply zd_src_rd; [exact SB | lia | reflexivity]);
      first [ assert (0 <= Znth i src < 256) by assumption
            | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
      step; unfold sxb; rewrite (byte_sig8 (Znth i src)) by assumption; clear RD
  end.

(* [comment removed for export] *)
Ltac rdb_tac segs SB OK i :=
  lazymatch type of SB with
  | bytes_at segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
      let RD := fresh "RD" in let RB := fresh "RB" in
      assert (RB : 0 <= Znth i src < 256) by (apply OK);
      assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
        by (eapply zd_src_rd; [exact SB | lia | reflexivity])
  end.

(* [comment removed for export] *)
Ltac zlb_auto SB OK i := lazymatch type of SB with bytes_at ?segs _ _ _ => zlb_tac segs SB OK i end.
Ltac zlbs_auto SB OK i := lazymatch type of SB with bytes_at ?segs _ _ _ => zlbs_tac segs SB OK i end.
Tactic Notation "zlb" constr(SB) constr(OK) constr(i) := zlb_auto SB OK i.
Tactic Notation "zlbs" constr(SB) constr(OK) constr(i) := zlbs_auto SB OK i.
