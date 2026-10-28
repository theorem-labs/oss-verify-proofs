(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C8 ECH_AKit ECH_AsKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition DB_L3 : Z := 0x4228d0.   Definition DB_LAST : Z := 0x422b48.   Definition DB_J : Z := 0x422874.   Definition DB_RET : Z := 0x42287c.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint groups_bytes (vs : list Z) : list Z :=
  match vs with a :: b :: c :: d :: rest => quad_bytes (quad_val a b c d) ++ groups_bytes rest | _ => [] end.
Lemma decode_groups_ok : forall vs, Forall (fun v => 0 <= v < 64) vs -> decode_groups vs = Some (groups_bytes vs).
Proof.
  fix IH 1. intros [|a [|b [|c [|d rest]]]] F; try reflexivity.
  cbn [decode_groups groups_bytes].
  inversion F as [|? ? Fa F1]; subst. inversion F1 as [|? ? Fb F2]; subst. inversion F2 as [|? ? Fc F3]; subst. inversion F3 as [|? ? Fd F4]; subst.
  pose proof (lor_lt_pow2 a b 6 ltac:(lia) ltac:(lia)) as L1. pose proof (lor_lt_pow2 (Z.lor a b) c 6 L1 ltac:(lia)) as L2.
  pose proof (lor_lt_pow2 (Z.lor (Z.lor a b) c) d 6 L2 ltac:(lia)) as L3. change (2^6) with 64 in L3.
  replace (128 <=? Z.lor (Z.lor (Z.lor a b) c) d) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite (IH rest F4). reflexivity.
Qed.
Lemma groups_bytes_length : forall q vs, length vs = (4 * q)%nat -> length (groups_bytes vs) = (3 * q)%nat.
Proof.
  induction q as [|q IH]; intros [|a [|b [|c [|d rest]]]] L; cbn in L |- *; try lia.
  rewrite (IH rest) by lia. lia.
Qed.
Lemma groups_bytes_skip : forall g vs, (4 * g <= length vs)%nat -> skipn (3 * g) (groups_bytes vs) = groups_bytes (skipn (4 * g) vs).
Proof.
  induction g as [|g IH]; intros vs L; [reflexivity|].
  destruct vs as [|a [|b [|c [|d rest]]]]; cbn in L; try lia.
  replace (3 * S g)%nat with (3 * g + 3)%nat by lia. replace (4 * S g)%nat with (4 * g + 4)%nat by lia.
  rewrite <- (skipn_skipn (3 * g) 3), <- (skipn_skipn (4 * g) 4).
  change (skipn 3 (groups_bytes (a :: b :: c :: d :: rest))) with (groups_bytes rest).
  change (skipn 4 (a :: b :: c :: d :: rest)) with rest.
  apply IH. lia.
Qed.
Lemma groups_bytes_nth : forall vs g j a b c d rest,
  skipn (4 * g) vs = a :: b :: c :: d :: rest -> (j < 3)%nat ->
  nth_error (groups_bytes vs) (3 * g + j) = nth_error (quad_bytes (quad_val a b c d)) j.
Proof.
  intros vs g j a b c d rest E J.
  assert (L : (4 * g <= length vs)%nat).
  { destruct (Nat.le_gt_cases (4 * g) (length vs)) as [|K]; [assumption|]. rewrite skipn_all2 in E by lia. discriminate. }
  rewrite <- nth_error_skipn, groups_bytes_skip, E by exact L. cbn [groups_bytes].
  rewrite nth_error_app1 by (cbn; lia). reflexivity.
Qed.
Lemma lor_add_disjoint : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.lor_0_l. lia. }
  assert (D : Z.land x (y * 2^k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [LT|GE].
    - rewrite (Z.mul_pow2_bits_low y k i) by lia. apply andb_false_r.
    - assert (LX : Z.log2 x < k) by (apply (proj1 (Z.log2_lt_pow2 x k ltac:(lia))); lia).
      rewrite (Z.bits_above_log2 x i) by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.
Lemma b8_mod : forall x, b8 (x mod 256) = b8 x.
Proof. intros x. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_modulus 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma b8_eqm : forall x y, x mod 256 = y mod 256 -> b8 x = b8 y.
Proof. intros x y E. rewrite <- (b8_mod x), <- (b8_mod y), E. reflexivity. Qed.
Section BYTES.
  Variables va vb vc vd : Z.
  Hypothesis Ra : 0 <= va < 64. Hypothesis Rb : 0 <= vb < 64. Hypothesis Rc : 0 <= vc < 64. Hypothesis Rd : 0 <= vd < 64.
  Lemma lor_ab : Z.lor (vb * 4096) (va * 262144) = vb * 4096 + va * 262144.
  Proof. change 262144 with (2^18). apply lor_add_disjoint; lia. Qed.
  Lemma lor_bc : Z.lor (vc * 64) (vb * 4096) = vc * 64 + vb * 4096.
  Proof. change 4096 with (2^12). apply lor_add_disjoint; lia. Qed.
  Lemma lor_cd : Z.lor vd (vc * 64) = vd + vc * 64.
  Proof. change 64 with (2^6) at 1 2. apply lor_add_disjoint; lia. Qed.
  (* [comment removed for export] *)
  Lemma mb0_ok : b8 ((Z.lor (vb * 4096) (va * 262144) ≫ 16) mod 256) = b8 (nth 0 (quad_bytes (quad_val va vb vc vd)) 0).
  Proof.
    rewrite lor_ab, Z.shiftr_div_pow2 by lia. cbn [nth quad_bytes]. unfold quad_val. change (2^16) with 65536.
    apply b8_eqm. f_equal. Z.div_mod_to_equations. lia.
  Qed.
  Lemma mb1_ok : b8 ((Z.lor (vc * 64) (vb * 4096) ≫ 8) mod 256) = b8 (nth 1 (quad_bytes (quad_val va vb vc vd)) 0).
  Proof.
    rewrite lor_bc, Z.shiftr_div_pow2 by lia. cbn [nth quad_bytes]. unfold quad_val. change (2^8) with 256.
    apply b8_eqm. rewrite !Z.mod_mod by lia. Z.div_mod_to_equations. lia.
  Qed.
  Lemma mb2_ok : b8 (Z.lor vd (vc * 64) mod 256) = b8 (nth 2 (quad_bytes (quad_val va vb vc vd)) 0).
  Proof.
    rewrite lor_cd. cbn [nth quad_bytes]. unfold quad_val. apply b8_eqm. rewrite !Z.mod_mod by lia. Z.div_mod_to_equations. lia.
  Qed.
End BYTES.

(* [comment removed for export] *)
Definition saved_okb (c : Z) : bool :=
  negb (b64_base64 (a2b c)) || (a2b c =? B64_ERROR) || (a2b c =? B64_EOF) || ((0 <=? a2b c) && (a2b c <? 64)).
Fixpoint zall (n : nat) (f : Z -> bool) : bool := match n with O => true | S k => f (Z.of_nat k) && zall k f end.
Lemma zall_ok : forall n f, zall n f = true -> forall i, 0 <= i < Z.of_nat n -> f i = true.
Proof.
  induction n as [|n IH]; cbn [zall]; intros f H i Hi; [lia|]. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec i (Z.of_nat n)) as [->|NE]; [exact H1|]. apply IH; [exact H2| lia].
Qed.
Lemma b64_saved_lt64 : forall c, b64_saved c -> 0 <= a2b c < 64.
Proof.
  intros c (R & B & NE & NF).
  pose proof (zall_ok 128 saved_okb ltac:(vm_compute; reflexivity) c R) as K. unfold saved_okb in K.
  rewrite B in K. cbn [negb orb] in K. unfold B64_ERROR, B64_EOF in *.
  destruct (Z.eqb_spec (a2b c) 255); [lia|]. destruct (Z.eqb_spec (a2b c) 242); [lia|]. cbn [orb] in K.
  apply andb_prop in K. destruct K as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2. lia.
Qed.
Lemma skipn_nth_cons' : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - f_equal. apply IH. exact H.
Qed.
Lemma saved_nth : forall n (raw : list byte) i c,
  Forall b64_saved (map bv_unsigned (firstn (Z.to_nat n) raw)) -> nth_error raw (Z.to_nat i) = Some c -> 0 <= i < n ->
  b64_saved (bv_unsigned c).
Proof.
  intros n raw i c F N R. pose proof (nth_error_lt _ _ _ N) as L0.
  rewrite Forall_forall in F. apply F. apply in_map.
  apply nth_error_In with (n := Z.to_nat i). rewrite <- N. rewrite <- (firstn_skipn (Z.to_nat n) raw) at 2.
  symmetry. apply nth_error_app1. rewrite length_firstn. lia.
Qed.
Lemma sxb_small : forall b : byte, bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b Hb. unfold sxb. f_equal. unfold bv_signed. apply bv_swrap_small. pose proof (byte_range b).
  change (bv_half_modulus 8) with 128%Z. lia.
Qed.
(* [comment removed for export] *)
Lemma trim_block_saved : forall cs, Forall (fun c => 0 <= a2b c < 64) cs -> trim_block cs = cs.
Proof.
  intros cs F. unfold trim_block.
  assert (FR : trim_ws_front cs = cs).
  { destruct cs as [|c cs']; [reflexivity|]. cbn [trim_ws_front]. inversion F; subst. unfold B64_WS.
    replace (a2b c =? 224) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite FR.
  assert (BK : forall r, Forall (fun c => 0 <= a2b c < 64) r -> trim_nb64_back_rev r 0 = r).
  { intros [|c r] Fr; [reflexivity|]. cbn [trim_nb64_back_rev]. inversion Fr; subst.
    replace (b64_not_base64 (a2b c)) with false; [rewrite andb_false_r; reflexivity|].
    symmetry. unfold b64_not_base64. apply Z.eqb_neq. intros E.
    pose proof (Z.lor_nonneg (a2b c) 19). pose proof (lor_lt_pow2 (a2b c) 19 6 ltac:(lia) ltac:(lia)). change (2^6) with 64 in *. lia. }
  rewrite BK; [apply rev_involutive|]. apply Forall_rev. exact F.
Qed.
Lemma decodeblock_saved : forall cs q eof,
  Forall (fun c => 0 <= a2b c < 64) cs -> length cs = (4 * q)%nat -> (0 < q)%nat -> 0 <= eof <= 2 ->
  decodeblock cs eof = Some (firstn (3 * q - Z.to_nat eof) (groups_bytes (map a2b cs))).
Proof.
  intros cs q eof F L Q E. unfold decodeblock.
  replace ((eof <? -1) || (2 <? eof)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
  rewrite (trim_block_saved cs F), L.
  replace (Z.of_nat (4 * q) mod 4 =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite Nat2Z.inj_mul; change (Z.of_nat 4) with 4; rewrite Z.mul_comm, Z.mod_mul; lia).
  cbn [negb]. replace (Z.of_nat (4 * q) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite decode_groups_ok by (apply Forall_map; exact F).
  replace (eof =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (groups_bytes_length q) by (rewrite length_map; exact L). f_equal; f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MEMH.
  Context {HCEIL : HeapCeil}.
  Lemma tab_nth : forall c, 0 <= c < 128 -> nth_error (map (Z_to_bv 8) data_ascii2bin) (Z.to_nat c) = Some (b8 (a2b c)).
  Proof.
    intros c Hc. unfold a2b, b8. replace (128 <=? c) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite nth_error_map. destruct (nth_error data_ascii2bin (Z.to_nat c)) as [v|] eqn:E.
    - cbn [option_map]. f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
    - apply nth_error_None in E. cbn in E. lia.
  Qed.
  Lemma B64TAB_of_mem_inv : forall m, mem_inv asegs m -> B64TAB m.
  Proof.
    intros m MI. unfold B64TAB. apply ro_bytes_at; [exact MI| unfold A_data_ascii2bin; lia| | apply ro_bytes_b_sound; vm_compute; reflexivity].
    rewrite length_map. unfold A_data_ascii2bin. cbn. lia.
  Qed.
  Lemma rd_raw : forall m f0 raw i c, bytes_at asegs m f0 raw -> nth_error raw (Z.to_nat i) = Some c -> 0 <= i ->
    ov_read_bytes asegs m (wa (f0 + i)) 1 = Some [c].
  Proof. intros m f0 raw i c B N Hi. eapply u8ro_read; [exact B| exact N| exact Hi| reflexivity]. Qed.
  Lemma rd_tab : forall m c, mem_inv asegs m -> 0 <= c < 128 -> ov_read_bytes asegs m (wa (A_data_ascii2bin + c)) 1 = Some [b8 (a2b c)].
  Proof. intros m c MI Hc. eapply u8ro_read; [exact (B64TAB_of_mem_inv m MI)| apply tab_nth; exact Hc| lia| reflexivity]. Qed.
  Lemma ctx_raw : forall m a x raw y z, rw_cells asegs m a [C4 x; CB 80 raw; C4 y; CB 4 z] -> bytes_at asegs m (a + 4) raw.
  Proof.
    intros m a x raw y z H. pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes app] in B.
    apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
    replace (a + Z.of_nat (length (le4 x))) with (a + 4) in B by (rewrite length_le4; lia). exact B.
  Qed.
End MEMH.
