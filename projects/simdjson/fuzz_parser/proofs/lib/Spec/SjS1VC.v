(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInv SjS1Lem SjS1Bytes SjS1Ghost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ul : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z.mod_small. exact Hz. Qed.
Lemma ur : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.
Lemma w_eq : forall x y : word, bv_unsigned x = bv_unsigned y -> x = y.
Proof. intros x y H. apply bv_eq. exact H. Qed.
Lemma wz : forall x : word, x = Z_to_bv 64 (bv_unsigned x).
Proof. intros x. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma u_and : forall x y : word, bv_unsigned (alu64 ALU_AND x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof. intros x y. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.
Lemma u_addi : forall (x : word) k, bv_unsigned (v_addi x k) = (bv_unsigned x + k) mod 2^64.
Proof. intros x k. unfold v_addi. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma u_ext1 : forall x : word, bv_unsigned (ext_val false 0 1 x) = bv_unsigned x mod 256.
Proof.
  intros x. unfold ext_val, ext_Z. cbn [Z.of_nat Nat.mul]. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. change (2 ^ (8 * 1)) with 256.
  apply ul. pose proof (Z.mod_pos_bound (bv_unsigned x) 256 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma bt_eq : forall x y : word, branch_taken BC_EQ x y = true -> bv_unsigned x = bv_unsigned y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.
Lemma bt_neq : forall x y : word, branch_taken BC_EQ x y = false -> bv_unsigned x <> bv_unsigned y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_eqb in H. apply Z.eqb_neq in H. exact H. Qed.
Lemma bt_ne : forall x y : word, branch_taken BC_NE x y = true -> bv_unsigned x <> bv_unsigned y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_eqb in H. apply negb_true_iff, Z.eqb_neq in H. exact H. Qed.
Lemma bt_nne : forall x y : word, branch_taken BC_NE x y = false -> bv_unsigned x = bv_unsigned y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_eqb in H. apply negb_false_iff, Z.eqb_eq in H. exact H. Qed.
Lemma bt_ltu : forall x y : word, branch_taken BC_LTU x y = true -> bv_unsigned x < bv_unsigned y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_ltu in H. apply Z.ltb_lt in H. exact H. Qed.
Lemma bt_nltu : forall x y : word, branch_taken BC_LTU x y = false -> bv_unsigned y <= bv_unsigned x.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_ltu in H. apply Z.ltb_ge in H. exact H. Qed.
Lemma bt_geu : forall x y : word, branch_taken BC_GEU x y = true -> bv_unsigned y <= bv_unsigned x.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_ltu in H. apply negb_true_iff, Z.ltb_ge in H. exact H. Qed.
Lemma bt_ngeu : forall x y : word, branch_taken BC_GEU x y = false -> bv_unsigned x < bv_unsigned y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_ltu in H. apply negb_false_iff, Z.ltb_lt in H. exact H. Qed.
Lemma bt_lt : forall x y : word, branch_taken BC_LT x y = true -> bv_signed x < bv_signed y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_lts in H. apply Z.ltb_lt in H. exact H. Qed.
Lemma bt_nlt : forall x y : word, branch_taken BC_LT x y = false -> bv_signed y <= bv_signed x.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_lts in H. apply Z.ltb_ge in H. exact H. Qed.
Lemma bt_ge : forall x y : word, branch_taken BC_GE x y = true -> bv_signed y <= bv_signed x.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_lts in H. apply negb_true_iff, Z.ltb_ge in H. exact H. Qed.
Lemma bt_nge : forall x y : word, branch_taken BC_GE x y = false -> bv_signed x < bv_signed y.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_lts in H. apply negb_false_iff, Z.ltb_lt in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nth_s1buf : forall d i, 0 <= i < zlength d + 64 -> nth (Z.to_nat i) (s1buf d) (Z_to_bv 8 0) = Z_to_bv 8 (byte_at d i).
Proof.
  intros d i Hi. unfold s1buf. rewrite map_nth. f_equal. apply byte_at_app_zeros. lia.
Qed.
Lemma nth_ctab : forall c, 0 <= c < 256 -> nth (Z.to_nat c) ctab_bytes (Z_to_bv 8 0) = Z_to_bv 8 (ctab c).
Proof. intros c Hc. pose proof (nth_ctab_bytes c Hc) as H. apply nth_error_nth with (d := Z_to_bv 8 0) in H. exact H. Qed.

Lemma rdn1_some : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma bytes_le_to_Z_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l. apply Z.lor_0_r. Qed.
Lemma extz_byte : forall b : byte, Z_to_bv 64 (extz false 1 (bytes_le_to_Z [b])) = Z_to_bv 64 (bv_unsigned b).
Proof. intros b. cbn [extz]. rewrite bytes_le_to_Z_1. reflexivity. Qed.
Lemma extz_byte_s : forall b : byte, Z_to_bv 64 (extz true 1 (bytes_le_to_Z [b])) = Z_to_bv 64 (bv_swrap 8 (bv_unsigned b)).
Proof. intros b. cbn [extz]. rewrite bytes_le_to_Z_1. reflexivity. Qed.

Section Dec.
Variable segs : list Segment.
Variable d : list Z.
Notation len := (zlength d).

(* [comment removed for export] *)
Lemma rr_buf : forall m buf lenw (a x : word) i,
  g_buf d m buf lenw ->
  (exists bs, rdn segs m a 1 = Some bs /\ Z_to_bv 64 (extz false 1 (bytes_le_to_Z bs)) = x) ->
  bv_unsigned a = bv_unsigned buf + i -> 0 <= i < len + 64 ->
  x = Z_to_bv 64 (byte_at d i).
Proof.
  intros m buf lenw a x i (HL & H20 & HB & HD & HM) (bs & HR & HX) HA Hi.
  assert (Ma : m a = Some (Z_to_bv 8 (byte_at d i))).
  { rewrite (wz a), HA. rewrite (HM i) by (unfold s1buf; rewrite length_map, length_app, repeat_length; unfold zlength in Hi; lia).
    rewrite nth_s1buf by lia. reflexivity. }
  rewrite (rdn1_some segs m a _ Ma) in HR. injection HR as <-. rewrite <- HX, extz_byte.
  rewrite unsigned_byte by (apply byte_at_range; exact HD). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rr_buf_s : forall m buf lenw (a x : word) i,
  g_buf d m buf lenw ->
  (exists bs, rdn segs m a 1 = Some bs /\ Z_to_bv 64 (extz true 1 (bytes_le_to_Z bs)) = x) ->
  bv_unsigned a = bv_unsigned buf + i -> 0 <= i < len + 64 ->
  x = Z_to_bv 64 (bv_swrap 8 (byte_at d i)).
Proof.
  intros m buf lenw a x i (HL & H20 & HB & HD & HM) (bs & HR & HX) HA Hi.
  assert (Ma : m a = Some (Z_to_bv 8 (byte_at d i))).
  { rewrite (wz a), HA. rewrite (HM i) by (unfold s1buf; rewrite length_map, length_app, repeat_length; unfold zlength in Hi; lia).
    rewrite nth_s1buf by lia. reflexivity. }
  rewrite (rdn1_some segs m a _ Ma) in HR. injection HR as <-. rewrite <- HX, extz_byte_s.
  rewrite unsigned_byte by (apply byte_at_range; exact HD). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rr_tab : forall m sp (a x : word) c,
  g_tab m sp ->
  (exists bs, rdn segs m a 1 = Some bs /\ Z_to_bv 64 (extz false 1 (bytes_le_to_Z bs)) = x) ->
  bv_unsigned a = bv_unsigned sp - 400 + c -> 0 <= c < 256 ->
  x = Z_to_bv 64 (ctab c).
Proof.
  intros m sp a x c (H4 & HM) (bs & HR & HX) HA Hc.
  assert (Ma : m a = Some (Z_to_bv 8 (ctab c))).
  { rewrite (wz a), HA. rewrite (HM c) by (unfold ctab_bytes; rewrite length_map, length_seq; lia).
    rewrite nth_ctab by lia. reflexivity. }
  rewrite (rdn1_some segs m a _ Ma) in HR. injection HR as <-. rewrite <- HX, extz_byte.
  rewrite unsigned_byte by (pose proof (ctab_range c); lia). reflexivity.
Qed.
End Dec.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mbytes_app : forall M a bs1 bs2, mbytes M a bs1 -> mbytes M (a + Z.of_nat (length bs1)) bs2 -> mbytes M a (bs1 ++ bs2).
Proof.
  intros M a bs1 bs2 H1 H2 i Hi. rewrite length_app in Hi.
  destruct (Z_lt_dec i (Z.of_nat (length bs1))) as [L|G].
  - rewrite app_nth1 by lia. apply H1. lia.
  - rewrite app_nth2 by lia. specialize (H2 (i - Z.of_nat (length bs1)) ltac:(lia)).
    replace (a + Z.of_nat (length bs1) + (i - Z.of_nat (length bs1))) with (a + i) in H2 by lia.
    replace (Z.to_nat (i - Z.of_nat (length bs1))) with (Z.to_nat i - length bs1)%nat in H2 by lia. exact H2.
Qed.

Lemma u32bytes_snoc : forall l x, u32bytes (l ++ [x]) = u32bytes l ++ word_to_le_bytes 4 (Z_to_bv 64 x).
Proof. intros l x. rewrite u32bytes_app. cbn [u32bytes]. rewrite app_nil_r. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac uw_in H := repeat progress (rewrite ?SV.u_alu_add, ?SV.u_alu_sub, ?SV.u_mul, ?u_and, ?u_ext1, ?u_addi, ?SV.u_lit in H).
Ltac uw := repeat progress (rewrite ?SV.u_alu_add, ?SV.u_alu_sub, ?SV.u_mul, ?u_and, ?u_ext1, ?u_addi, ?SV.u_lit).
(* [comment removed for export] *)
Ltac keep_ranges :=
  repeat match goal with
  | H : ?P |- _ =>
      lazymatch P with
      | ?lo <= bv_unsigned (ev _ _) <= ?hi => fail
      | 0 <= bv_unsigned (ev _ _) < _ => fail
      | 0 <= ?x < 256 => fail
      | 0 <= ?x <= 15 => fail
      | zlength _ + 64 <= 2 ^ 20 => fail
      | bv_unsigned (ev _ _) = zlength _ => fail
      | bv_unsigned (ev _ _) + zlength _ + 64 <= 2 ^ 64 => fail
      | bv_unsigned (ev _ _) < bv_unsigned (ev _ _) => fail
      | bv_unsigned (ev _ _) + _ < bv_unsigned (ev _ _) => fail
      | bv_unsigned (ev _ _) < zlength _ => fail
      | _ => clear H
      end
  end.
Ltac rlia := keep_ranges; lia.
Ltac mods_in H :=
  repeat match type of H with
  | context [?x mod 18446744073709551616] => lazymatch x with _ - _ => fail | _ => rewrite (Z.mod_small x 18446744073709551616) in H by rlia end
  | context [?x mod 2 ^ 64] => lazymatch x with _ - _ => fail | _ => rewrite (Z.mod_small x (2 ^ 64)) in H by rlia end
  | context [?x mod 256] => rewrite (Z.mod_small x 256) in H by rlia
  end.
Ltac mods :=
  repeat match goal with
  | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by rlia
  | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by rlia
  | |- context [?x mod 256] => rewrite (Z.mod_small x 256) by rlia
  end.

(* [comment removed for export] *)
Lemma sub_mod_small : forall a b lo hi, 0 <= a < 2^62 -> 0 <= b < 2^62 -> 0 <= lo -> hi < 2^62 ->
  lo <= (a - b) mod 2^64 <= hi -> lo <= a - b <= hi.
Proof.
  intros a b lo hi Ha Hb Hlo Hhi H. destruct (Z_lt_ge_dec (a - b) 0) as [L|G].
  - replace ((a - b) mod 2^64) with (a - b + 2^64) in H; [lia|].
    rewrite <- (Z.mod_add (a - b) 1 (2^64)) by lia. rewrite Z.mod_small; lia.
  - rewrite Z.mod_small in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Ltac s1vc_ranges :=
  repeat match goal with
  | H : context [bv_unsigned (ev ?E ?n)] |- _ =>
      lazymatch goal with _ : 0 <= bv_unsigned (ev E n) < 2^64 |- _ => fail | _ => pose proof (ur (ev E n)) end
  | |- context [bv_unsigned (ev ?E ?n)] =>
      lazymatch goal with _ : 0 <= bv_unsigned (ev E n) < 2^64 |- _ => fail | _ => pose proof (ur (ev E n)) end
  end.

(* [comment removed for export] *)
Ltac s1vc_intro :=
  SV.vc_intro;
  repeat match goal with H : s1_gp _ _ _ _ |- _ => cbn [s1_gp] in H end;
  try match goal with
  | H : g_buf _ _ _ _ |- _ =>
      let GL := fresh "GL" in let G20 := fresh "G20" in let GBB := fresh "GBB" in let GDB := fresh "GDB" in let GMB := fresh "GMB" in
      pose proof H as (GL & G20 & GBB & GDB & GMB)
  end.

(* [comment removed for export] *)
Ltac s1vc_krange :=
  repeat match goal with
  | H : ?lo <= bv_unsigned ?e <= ?hi |- _ =>
      lazymatch e with ev _ _ => fail | _ => idtac end;
      uw_in H; mods_in H;
      try (lazymatch type of H with ?lo' <= (?a - ?b) mod 2 ^ 64 <= ?hi' =>
             apply sub_mod_small in H; [| rlia | rlia | rlia | rlia] end);
      revert H
  end; intros.

(* [comment removed for export] *)
Ltac s1vc_rd_idx E B off :=
  lazymatch B with
  | EVar ?j => lazymatch off with 0 => constr:(bv_unsigned (ev E j)) | _ => constr:(bv_unsigned (ev E j) + off) end
  | EAlu ALU_ADD (EVar ?j) (ELit ?c) => lazymatch off with 0 => constr:(bv_unsigned (ev E j) + c) | _ => constr:(bv_unsigned (ev E j) + c + off) end
  end.
(* [comment removed for export] *)
Ltac s1vc_reads_buf :=
  repeat match goal with
  | GB : g_buf ?d ?m (ev ?E ?nb) ?lw,
    H : exists bs, rdn ?segs ?m (adenot ?E {| a_base := EAlu ALU_ADD (EVar ?nb) ?B; a_off := ?off |}) 1 = Some bs
                   /\ Z_to_bv 64 (extz ?sx 1 (bytes_le_to_Z bs)) = ev ?E ?v |- _ =>
      let i := s1vc_rd_idx E B off in
      let A := fresh "A" in
      assert (A : bv_unsigned (adenot E {| a_base := EAlu ALU_ADD (EVar nb) B; a_off := off |}) = bv_unsigned (ev E nb) + i)
        by (unfold adenot, a_base, a_off; cbn [edenot]; uw; mods; lia);
      let R := fresh "R_" in
      lazymatch sx with
      | false => pose proof (rr_buf segs d m _ lw _ _ i GB H A ltac:(lia)) as R
      | true => pose proof (rr_buf_s segs d m _ lw _ _ i GB H A ltac:(lia)) as R
      end;
      clear H A;
      let bn := fresh "b" in set (bn := byte_at d i) in *;
      let BR := fresh "BR" in assert (BR : 0 <= bn < 256) by (apply byte_at_range; assumption)
  end.
Ltac s1vc_reads_tab :=
  repeat match goal with
  | GT : g_tab ?m (ev ?E ?ns), R : ev ?E ?vb = Z_to_bv 64 ?c, BR : 0 <= ?c < 256,
    H : exists bs, rdn ?segs ?m (adenot ?E {| a_base := EAlu ALU_ADD (EVar ?ns) (EExt false 0 1 (EVar ?vb)); a_off := -400 |}) 1 = Some bs
                   /\ Z_to_bv 64 (extz false 1 (bytes_le_to_Z bs)) = ev ?E ?v |- _ =>
      let A := fresh "A" in
      assert (A : bv_unsigned (adenot E {| a_base := EAlu ALU_ADD (EVar ns) (EExt false 0 1 (EVar vb)); a_off := -400 |})
                  = bv_unsigned (ev E ns) - 400 + c)
        by (unfold adenot, a_base, a_off; cbn [edenot]; rewrite R; uw; mods; lia);
      let T := fresh "T_" in pose proof (rr_tab segs m _ _ _ c GT H A BR) as T;
      clear H A;
      let CR := fresh "CR" in pose proof (ctab_range c) as CR
  end.
(* [comment removed for export] *)
Ltac s1vc_subst :=
  repeat match goal with
  | R : ev ?E ?v = Z_to_bv 64 _ |- _ => rewrite R in *; clear R
  end.

(* [comment removed for export] *)
Lemma sl : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. change (bv_swrap 64 (bv_wrap 64 z)) with ((bv_wrap 64 z + 2^63) mod 2^64 - 2^63).
  unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sh56_sign : forall b, 0 <= b < 256 -> (bv_signed (Z_to_bv 64 (72057594037927936 * b)) < 0 <-> 128 <= b).
Proof.
  intros b Hb. unfold bv_signed. rewrite Z_to_bv_unsigned. change (bv_swrap 64 (bv_wrap 64 (72057594037927936 * b)))
    with ((bv_wrap 64 (72057594037927936 * b) + 2^63) mod 2^64 - 2^63).
  unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Zplus_mod_idemp_l.
  destruct (Z_lt_ge_dec b 128).
  - rewrite Z.mod_small by lia. lia.
  - replace (72057594037927936 * b + 2 ^ 63) with ((72057594037927936 * b - 2^63) + 1 * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap8_small : forall b, 0 <= b < 256 -> - 128 <= bv_swrap 8 b < 128.
Proof. intros b Hb. change (bv_swrap 8 b) with ((b + 128) mod 256 - 128). pose proof (Z.mod_pos_bound (b + 128) 256 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Ltac s1vc_br :=
  repeat match goal with
  | H : branch_taken BC_EQ _ _ = true |- _ => apply bt_eq in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_EQ _ _ = false |- _ => apply bt_neq in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_NE _ _ = true |- _ => apply bt_ne in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_NE _ _ = false |- _ => apply bt_nne in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_LTU _ _ = true |- _ => apply bt_ltu in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_LTU _ _ = false |- _ => apply bt_nltu in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_GEU _ _ = true |- _ => apply bt_geu in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_GEU _ _ = false |- _ => apply bt_ngeu in H; uw_in H; mods_in H; revert H
  | H : branch_taken BC_LT _ _ = true |- _ => apply bt_lt in H; revert H
  | H : branch_taken BC_LT _ _ = false |- _ => apply bt_nlt in H; revert H
  | H : branch_taken BC_GE _ _ = true |- _ => apply bt_ge in H; revert H
  | H : branch_taken BC_GE _ _ = false |- _ => apply bt_nge in H; revert H
  end; intros.

(* [comment removed for export] *)
Ltac s1vc_renorm :=
  repeat match goal with
  | H : context [bv_unsigned (Z_to_bv 64 ?t)] |- _ => rewrite (ul t) in H by lia
  | H : context [bv_signed (Z_to_bv 64 ?t)] |- _ => rewrite (sl t) in H by (first [lia | pose proof (swrap8_small _ ltac:(lia)); lia])
  end;
  repeat match goal with H : context [?x mod 256] |- _ => rewrite (Z.mod_small x 256) in H by lia end.

(* [comment removed for export] *)
Ltac s1vc_pre := s1vc_intro; s1vc_ranges; s1vc_krange; s1vc_br; s1vc_reads_buf; s1vc_reads_tab; s1vc_subst; s1vc_renorm.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MemLog.
Variable E : env.

Lemma mbytes_log_out : forall M log a bs, log_flat E log -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> SV.outside_log E log (a + i)) ->
  mbytes M a bs -> mbytes (mem_denot E M log) a bs.
Proof.
  intros M log a bs HF H0 H1 HO H i Hi. rewrite SV.md_outside; [exact (H i Hi)| exact HF|].
  rewrite ul by lia. exact (HO i Hi).
Qed.

(* [comment removed for export] *)
Lemma mbytes_log_head : forall M a w v rest A, log_flat E (SE a w v :: rest) -> bv_unsigned (adenot E a) = A ->
  mbytes (mem_denot E M (SE a w v :: rest)) A (word_to_le_bytes w (edenot E v)).
Proof.
  intros M a w v rest A HF HA i Hi. unfold word_to_le_bytes in Hi. rewrite length_Z_to_le_bytes in Hi.
  cbn [log_flat] in HF. destruct HF as (Hw & Hfl & _).
  rewrite <- HA. replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
  apply SV.md_newest; [exact Hfl| lia].
Qed.

(* [comment removed for export] *)
Lemma mbytes_log_skip : forall M e rest A bs, log_flat E (e :: rest) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> SV.outside_log E [e] (A + i)) -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  mbytes (mem_denot E M rest) A bs -> mbytes (mem_denot E M (e :: rest)) A bs.
Proof.
  intros M [a w v] rest A bs HF HO H0 H1 H i Hi. cbn [log_flat] in HF. destruct HF as (Hw & Hfl & HF').
  rewrite SV.md_skip; [exact (H i Hi)| exact Hfl|].
  specialize (HO i Hi). cbn [SV.outside_log] in HO. destruct HO as [HO _].
  rewrite (flat_u E _ _ Hfl). rewrite ul by lia. unfold estart in HO. exact HO.
Qed.
End MemLog.

Lemma u32bytes_rev_cons : forall x acc, u32bytes (rev (x :: acc)) = u32bytes (rev acc) ++ word_to_le_bytes 4 (Z_to_bv 64 x).
Proof. intros x acc. cbn [rev]. apply u32bytes_snoc. Qed.
Lemma u32bytes_len : forall l, Z.of_nat (length (u32bytes l)) = 4 * zlength l.
Proof. intros l. rewrite u32bytes_length. unfold zlength. lia. Qed.
Lemma le4_len : forall v, Z.of_nat (length (word_to_le_bytes 4 v)) = 4.
Proof. intros v. unfold word_to_le_bytes. rewrite length_Z_to_le_bytes. reflexivity. Qed.
Lemma zlength_rev' : forall (l : list Z), zlength (rev l) = zlength l.
Proof. intros l. unfold zlength. rewrite length_rev. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ctab_3 : forall c, Z.land (ctab c) 3 = (if is_space c then 1 else 0) + (if is_op c then 2 else 0).
Proof. intros c. unfold ctab. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); reflexivity. Qed.
Lemma ctab_12_0 : forall c, Z.land (ctab c) 12 = 0 -> is_ascii_stop c = false.
Proof. intros c H. apply ctab_stop. exact H. Qed.
Lemma ctab_12_n0 : forall c, Z.land (ctab c) 12 <> 0 -> is_ascii_stop c = true.
Proof. intros c H. destruct (is_ascii_stop c) eqn:E; [reflexivity|]. apply ctab_stop in E. contradiction. Qed.
Lemma ctab_12_bound : forall c, 0 <= Z.land (ctab c) 12 <= 12.
Proof. intros c. unfold ctab. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); vm_compute; split; discriminate. Qed.

Ltac s1vc_cls1 H c f lem :=
  lazymatch goal with
  | E : f c = _ |- _ => rewrite lem, E in H; cbn iota in H
  | _ => rewrite lem in H; let E := fresh "C" in destruct (f c) eqn:E; cbn iota in H
  end.
Ltac s1vc_cls :=
  repeat match goal with
  | H : context [Z.land (ctab ?c) 1] |- _ => s1vc_cls1 H c is_space ctab_space; try (exfalso; lia)
  | H : context [Z.land (ctab ?c) 2] |- _ => s1vc_cls1 H c is_op ctab_op; try (exfalso; lia)
  | H : context [Z.land (ctab ?c) 3] |- _ =>
      rewrite ctab_3 in H;
      lazymatch goal with E : is_space c = _ |- _ => rewrite E in H | _ => let E := fresh "C" in destruct (is_space c) eqn:E end;
      lazymatch goal with E : is_op c = _ |- _ => rewrite E in H | _ => let E := fresh "C" in destruct (is_op c) eqn:E end;
      cbn iota in H; try (exfalso; lia)
  | H : Z.land (ctab ?c) 12 = 0 |- _ => apply ctab_12_0 in H
  | H : Z.land (ctab ?c) 12 <> 0 |- _ => apply ctab_12_n0 in H
  | H : ?lo <= Z.land (ctab ?c) 12 <= ?hi |- _ =>
      first [ assert (Z.land (ctab c) 12 = 0) by lia; clear H | assert (Z.land (ctab c) 12 <> 0) by lia; clear H ]
  end; try discriminate.

(* [comment removed for export] *)
Ltac s1vc_names :=
  repeat match goal with
  | H : g_main _ _ _ _ _ _ |- _ => let G := fresh "GM" in rename H into G; revert G
  | H : g_str _ _ _ _ _ _ _ |- _ => let G := fresh "GS" in rename H into G; revert G
  | H : g_prim _ _ _ _ _ _ _ |- _ => let G := fresh "GP" in rename H into G; revert G
  end; intros.

(* [comment removed for export] *)
Ltac s1vc_tgt1 := split; [constructor; [| constructor]; cbn [map ST.g_id ST.g_args edenot s1_gp] | constructor].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gm_push_mem : forall E M a1 dd acc (a : saddr) (v : expr),
  mbytes M a1 (u32bytes (rev acc)) -> 4 * zlength acc = dd -> 0 <= a1 -> a1 + dd + 4 <= 2^64 ->
  log_flat E [SE a 4 v] -> bv_unsigned (adenot E a) = a1 + dd ->
  mbytes (mem_denot E M [SE a 4 v]) a1 (u32bytes (rev (bv_unsigned (edenot E v) :: acc))).
Proof.
  intros E M a1 dd acc a v HM HD H0 H1 HF HA.
  rewrite u32bytes_rev_cons. apply mbytes_app.
  - apply mbytes_log_out; [exact HF| exact H0| rewrite u32bytes_len, zlength_rev'; lia| |exact HM].
    intros i Hi. rewrite u32bytes_len, zlength_rev' in Hi. cbn [SV.outside_log]. split; [|exact I].
    left. cbn [log_flat] in HF. destruct HF as (_ & Hfl & _). rewrite <- (flat_u E _ _ Hfl), HA. lia.
  - rewrite u32bytes_len, zlength_rev', HD. rewrite Z_to_bv_bv_unsigned. apply mbytes_log_head; [exact HF| exact HA].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Steps.
Variable d : list Z.
Notation len := (zlength d).
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma gm_same : forall M a1 j j' dd er er',
  g_main d M a1 j dd er -> (forall acc, S1C d (u j) acc (errb er) = S1C d (u j') acc (errb er')) -> g_main d M a1 j' dd er'.
Proof. intros M a1 j j' dd er er' (acc & H1 & H2 & H3 & H4) HS. exists acc. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. rewrite H4. apply HS. Qed.

(* [comment removed for export] *)
Lemma gm_push : forall E M a1 j dd er (a : saddr) (v : expr) j' dd' er',
  g_main d M a1 j dd er -> log_flat E [SE a 4 v] -> u (adenot E a) = u a1 + u dd ->
  u a1 + u dd + 4 < 2^64 -> u dd' = u dd + 4 ->
  (forall acc, S1C d (u j) acc (errb er) = S1C d (u j') (u (edenot E v) :: acc) (errb er')) ->
  g_main d (mem_denot E M [SE a 4 v]) a1 j' dd' er'.
Proof.
  intros E M a1 j dd er a v j' dd' er' (acc & H1 & H2 & H3 & H4) HF HA HB HD HS.
  exists (u (edenot E v) :: acc). split; [rewrite zlength_cons; lia|]. split; [lia|]. split.
  - apply gm_push_mem with (dd := u dd); [exact H3| lia| pose proof (ur a1); lia| lia| exact HF| exact HA].
  - rewrite H4. apply HS.
Qed.

(* [comment removed for export] *)
Lemma gm_to_str : forall E M a1 j dd er (a : saddr) (v : expr) i k er',
  g_main d M a1 j dd er -> log_flat E [SE a 4 v] -> u (adenot E a) = u a1 + u dd -> u a1 + u dd + 4 < 2^64 ->
  u i = u (edenot E v) ->
  (forall acc, S1C d (u j) acc (errb er) = SRES d (u i) acc (VSC d (u k) (errb er'))) ->
  g_str d (mem_denot E M [SE a 4 v]) a1 i k dd er'.
Proof.
  intros E M a1 j dd er a v i k er' (acc & H1 & H2 & H3 & H4) HF HA HB HI HS.
  exists acc. split; [exact H1|]. split; [lia|]. split.
  - rewrite HI. apply gm_push_mem with (dd := u dd); [exact H3| lia| pose proof (ur a1); lia| lia| exact HF| exact HA].
  - rewrite H4. apply HS.
Qed.

(* [comment removed for export] *)
Lemma gm_to_prim : forall E M a1 j dd er (a : saddr) (v : expr) i k er',
  g_main d M a1 j dd er -> log_flat E [SE a 4 v] -> u (adenot E a) = u a1 + u dd -> u a1 + u dd + 4 < 2^64 ->
  u i = u (edenot E v) -> u k + 1 < len -> primc (byte_at d (u k + 1)) = true ->
  (forall acc, S1C d (u j) acc (errb er) = S1C d (PEC d (u k) + 1) (u i :: acc) (errb er')) ->
  g_prim d (mem_denot E M [SE a 4 v]) a1 i k dd er'.
Proof.
  intros E M a1 j dd er a v i k er' (acc & H1 & H2 & H3 & H4) HF HA HB HI HK HP HS.
  exists acc. split; [exact H1|]. split; [lia|]. split.
  - rewrite HI. apply gm_push_mem with (dd := u dd); [exact H3| lia| pose proof (ur a1); lia| lia| exact HF| exact HA].
  - split; [exact HK|]. split; [exact HP|]. rewrite H4. apply HS.
Qed.

(* [comment removed for export] *)
Lemma gs_same : forall M M' a1 i k k' dd er er',
  g_str d M a1 i k dd er -> (forall l, mbytes M (u a1) l -> Z.of_nat (length l) = u dd + 4 -> mbytes M' (u a1) l) ->
  VSC d (u k) (errb er) = VSC d (u k') (errb er') -> g_str d M' a1 i k' dd er'.
Proof.
  intros M M' a1 i k k' dd er er' (acc & H1 & H2 & H3 & H4) HM HS. exists acc. split; [exact H1|]. split; [exact H2|]. split.
  - apply HM; [exact H3|]. rewrite u32bytes_len, zlength_rev', zlength_cons. lia.
  - rewrite H4, HS. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gs_to_main : forall M M' a1 i k j' dd dd' er er',
  g_str d M a1 i k dd er -> (forall l, mbytes M (u a1) l -> Z.of_nat (length l) = u dd + 4 -> mbytes M' (u a1) l) ->
  u dd' = u dd + 4 ->
  (forall acc, SRES d (u i) acc (VSC d (u k) (errb er)) = S1C d (u j') (u i :: acc) (errb er')) ->
  g_main d M' a1 j' dd' er'.
Proof.
  intros M M' a1 i k j' dd dd' er er' (acc & H1 & H2 & H3 & H4) HM HD HS. exists (u i :: acc).
  split; [rewrite zlength_cons; lia|]. split; [lia|]. split.
  - apply HM; [exact H3|]. rewrite u32bytes_len, zlength_rev', zlength_cons. lia.
  - rewrite H4. apply HS.
Qed.

(* [comment removed for export] *)
Lemma gp_same : forall M a1 i k k' dd er,
  g_prim d M a1 i k dd er -> u k + 1 < len -> primc (byte_at d (u k + 1)) = true -> u k' = u k + 1 ->
  u k' + 1 < len -> primc (byte_at d (u k' + 1)) = true -> g_prim d M a1 i k' dd er.
Proof.
  intros M a1 i k k' dd er (acc & H1 & H2 & H3 & HK & HP & H4) _ _ HK' HK2 HP2. exists acc.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact HK2|]. split; [exact HP2|].
  rewrite H4. f_equal. f_equal. rewrite HK'. apply PEC_step; [pose proof (ur k); lia| exact HK| exact HP].
Qed.

(* [comment removed for export] *)
Lemma gp_to_main : forall M a1 i k j' dd dd' er,
  g_prim d M a1 i k dd er -> (u k + 2 >= len \/ primc (byte_at d (u k + 2)) = false) ->
  u j' = u k + 2 -> u dd' = u dd + 4 -> g_main d M a1 j' dd' er.
Proof.
  intros M a1 i k j' dd dd' er (acc & H1 & H2 & H3 & HK & HP & H4) HE HJ HD. exists (u i :: acc).
  split; [rewrite zlength_cons; lia|]. split; [lia|]. split; [exact H3|].
  rewrite H4. f_equal. rewrite HJ. rewrite PEC_step by (pose proof (ur k); lia || assumption).
  rewrite PEC_here; [lia|]. replace (u k + 1 + 1) with (u k + 2) by lia. destruct HE; [left; lia| right; assumption].
Qed.

(* [comment removed for export] *)
Lemma gx_intro : forall M a1 rc n this (acc : list Z) err uncl,
  scan d = fin3 (acc, err, uncl) ->
  (u rc = 0 <-> fst (fin3 (acc, err, uncl)) = true) ->
  (u rc = 0 -> u n = zlength acc /\ u a1 + 4 * u n + 12 < 2^64 /\ mbytes M (u a1) (u32bytes (rev acc ++ [len; len; 0]))
               /\ u this + 28 < 2^64 /\ mbytes M (u this + 24) (word_to_le_bytes 4 (Z_to_bv 64 0))) ->
  g_exit d M a1 rc n this.
Proof.
  intros M a1 rc n this acc err uncl HS HC HM. unfold g_exit. rewrite HS. split; [exact HC|].
  intros H0. destruct (HM H0) as (HN & HB & HMM & HT & HZ). cbn [fin3 snd]. rewrite zlength_rev'.
  split; [exact HN|]. split; [exact HB|]. split; [exact HMM|]. split; [exact HT| exact HZ].
Qed.
End Steps.
