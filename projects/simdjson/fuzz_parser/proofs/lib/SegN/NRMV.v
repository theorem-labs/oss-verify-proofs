(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec SeqExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC SegLin.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjVCPre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG NRMG SLOWV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module NRV.
Local Notation u := bv_unsigned.

Lemma u_rng : forall w : word, 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.

Lemma u_small : forall z, 0 <= z < 2 ^ 64 -> u (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact H. Qed.

Section W.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition wat (M : word -> option byte) (a w : Z) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 a) 8 = Some bs /\ bytes_le_to_Z bs = w.

Lemma wat_fun : forall M a w w', wat M a w -> wat M a w' -> w = w'.
Proof. intros M a w w' (bs & H1 & <-) (bs' & H2 & <-). rewrite H1 in H2. injection H2 as ->. reflexivity. Qed.

Lemma bytes8_rng : forall bs, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2 ^ 64.
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs). rewrite Hl in R.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R. lia.
Qed.

Lemma wat_rng : forall M a w, wat M a w -> 0 <= w < 2 ^ 64.
Proof. intros M a w (bs & H & <-). apply bytes8_rng. exact (rdn_length segs M 8 _ bs H). Qed.

(* [comment removed for export] *)
Lemma rr8 : forall m E a k v, sc_denot segs m E (SCReadBase (SA a k) 8 false (EVar v)) ->
  wat m (u (adenot E (SA a k))) (u (ev E v)).
Proof.
  intros m E a k v (bs & Hr & Hv). cbn [edenot] in Hv. exists bs. rewrite Z_to_bv_bv_unsigned. split; [exact Hr|].
  rewrite <- Hv. cbn [extz]. rewrite u_small; [reflexivity|]. apply bytes8_rng. exact (rdn_length segs m 8 _ bs Hr).
Qed.

(* [comment removed for export] *)
Lemma topnz_wat : forall M x n, SNU.topnz segs M x n -> exists w, wat M (u x + 8 * u n - 8) w /\ w <> 0.
Proof. intros M x n (bs & H & Hnz). exists (bytes_le_to_Z bs). split; [exists bs; split; [exact H | reflexivity] | exact Hnz]. Qed.
Lemma wat_topnz : forall M x n w, wat M (u x + 8 * u n - 8) w -> w <> 0 -> SNU.topnz segs M x n.
Proof. intros M x n w (bs & H & <-) Hnz. exists bs. split; [exact H | exact Hnz]. Qed.
Lemma topw_wat : forall M a, SNU.g_topw segs M a -> 8 <= u a /\ exists w, wat M (u a - 8) w /\ w <> 0.
Proof. intros M a (Ha & bs & H & Hnz). split; [exact Ha|]. exists (bytes_le_to_Z bs). split; [exists bs; split; [exact H | reflexivity] | exact Hnz]. Qed.
Lemma wat_topw : forall M a w, 8 <= u a -> wat M (u a - 8) w -> w <> 0 -> SNU.g_topw segs M a.
Proof. intros M a w Ha (bs & H & <-) Hnz. split; [exact Ha|]. exists bs. split; [exact H | exact Hnz]. Qed.

(* [comment removed for export] *)
Lemma wat_hit : forall E M b k v rest a, a = u (adenot E (SA b k)) -> a + 8 <= 2 ^ 64 ->
  wat (mem_denot E M (SE (SA b k) 8 v :: rest)) a (u (edenot E v)).
Proof.
  intros E M b k v rest a Ha Hn. subst a. cbn [mem_denot]. exists (word_to_le_bytes 8 (edenot E v)).
  rewrite Z_to_bv_bv_unsigned. split; [apply rdn_wbytes_hit8; exact Hn | apply bytes_le_to_Z_8].
Qed.

Lemma wat_miss : forall E M b k w v rest a x, a + 8 <= 2 ^ 64 -> 0 <= a -> u (adenot E (SA b k)) + Z.of_nat w <= 2 ^ 64 ->
  (a + 8 <= u (adenot E (SA b k)) \/ u (adenot E (SA b k)) + Z.of_nat w <= a) ->
  wat (mem_denot E M rest) a x -> wat (mem_denot E M (SE (SA b k) w v :: rest)) a x.
Proof.
  intros E M b k w v rest a x Hn H0 Hs Hap (bs & Hr & <-). exists bs. split; [|reflexivity].
  cbn [mem_denot]. rewrite rdn_wbytes_out; [exact Hr | | | ].
  - rewrite u_small by lia. rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. lia.
  - rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. exact Hs.
Qed.

Lemma wat_nil : forall E M a x, wat M a x -> wat (mem_denot E M []) a x.
Proof. intros E M a x H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma smul_nz : forall x y c, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> x <> 0 -> y <> 0 ->
  (c + (x * y) mod 2 ^ 64) mod 2 ^ 64 <> 0 \/
  ((if (c + (x * y) mod 2 ^ 64) mod 2 ^ 64 <? (x * y) mod 2 ^ 64 then 1 else 0) + x * y / 2 ^ 64) mod 2 ^ 64 <> 0.
Proof.
  intros x y c Hx Hy Hc Hx0 Hy0.
  destruct (Z.eq_dec ((c + (x * y) mod 2 ^ 64) mod 2 ^ 64) 0) as [E0|E0]; [right|left; exact E0].
  assert (HP : 1 <= x * y) by nia.
  assert (HH : x * y / 2 ^ 64 < 2 ^ 64 - 1).
  { apply Z.div_lt_upper_bound; [lia|]. nia. }
  pose proof (Z.div_pos (x * y) (2 ^ 64) ltac:(lia) ltac:(lia)) as HH0.
  rewrite E0. destruct (Z.ltb_spec 0 ((x * y) mod 2 ^ 64)) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - pose proof (Z.mod_pos_bound (x * y) (2 ^ 64) ltac:(lia)) as R.
    assert (Z0 : (x * y) mod 2 ^ 64 = 0) by lia.
    rewrite Z.add_0_l. rewrite Z.mod_small by lia.
    intro C. rewrite (Z_div_mod_eq_full (x * y) (2 ^ 64)) in HP. rewrite Z0, C in HP. lia.
Qed.

(* [comment removed for export] *)
Lemma add_nowrap_nz : forall x v, 0 <= x < 2 ^ 64 -> x <> 0 -> x <= (x + v) mod 2 ^ 64 -> (x + v) mod 2 ^ 64 <> 0.
Proof. intros x v Hx Hx0 H. lia. Qed.
(* [comment removed for export] *)
Lemma shl_top_nz : forall x p e1 e2, 0 <= x < 2 ^ 64 -> 0 <= p -> 1 <= e1 <= 63 -> e2 = 64 - e1 -> x <> 0 -> x / 2 ^ e2 = 0 ->
  Z.lor ((x * 2 ^ e1) mod 2 ^ 64) (p / 2 ^ e2) <> 0.
Proof.
  intros x p e1 e2 Hx Hp He1 He2 Hx0 Hd. subst e2.
  assert (Hlt : x < 2 ^ (64 - e1)).
  { destruct (Z.lt_ge_cases x (2 ^ (64 - e1))) as [L|G]; [exact L|].
    exfalso. assert (1 <= x / 2 ^ (64 - e1)) by (apply Z.div_le_lower_bound; [apply Z.pow_pos_nonneg; lia | lia]). lia. }
  assert (Hm : x * 2 ^ e1 < 2 ^ 64).
  { replace (2 ^ 64) with (2 ^ (64 - e1) * 2 ^ e1) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia | exact Hlt]. }
  assert (Hpos : 0 < 2 ^ e1) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_small by nia.
  intros C. apply Z.lor_eq_0_iff in C as [C _]. nia.
Qed.

(* [comment removed for export] *)
Definition w4at (M : word -> option byte) (a w : Z) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = w.
Lemma w4at_fun : forall M a w w', w4at M a w -> w4at M a w' -> w = w'.
Proof. intros M a w w' (bs & H1 & <-) (bs' & H2 & <-). rewrite H1 in H2. injection H2 as ->. reflexivity. Qed.
Lemma bytes4_rng : forall bs, length bs = 4%nat -> 0 <= bytes_le_to_Z bs < 2 ^ 32.
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs). rewrite Hl in R.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. lia.
Qed.
Lemma w4at_rng : forall M a w, w4at M a w -> 0 <= w < 2 ^ 32.
Proof. intros M a w (bs & H & <-). apply bytes4_rng. exact (rdn_length segs M 4 _ bs H). Qed.
Lemma wat_44 : forall M a L H, 0 <= a -> a + 8 <= 2 ^ 64 -> w4at M a L -> w4at M (a + 4) H -> wat M a (L + 2 ^ 32 * H).
Proof.
  intros M a L H Ha Hn (b1 & H1 & <-) (b2 & H2 & <-).
  pose proof (rdn_length segs M 4 _ b1 H1) as L1. pose proof (rdn_length segs M 4 _ b2 H2) as L2.
  exists (b1 ++ b2). split.
  - change 8%nat with (4 + 4)%nat. apply rdn_app; [exact H1|].
    match goal with |- rdn _ _ ?A _ = _ => replace A with (Z_to_bv 64 (a + 4)); [exact H2|] end.
    apply bv_eq. rewrite bv_add_unsigned. unfold nat_to_word. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod. reflexivity.
  - rewrite bytes_le_app, L1. change (8 * Z.of_nat 4) with 32.
    pose proof (bytes4_rng b1 L1). pose proof (bytes4_rng b2 L2).
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite <- Z.lxor_lor. 2: { apply Z.bits_inj_0. intros i. rewrite Z.land_spec.
      destruct (Z.lt_ge_cases i 32) as [Li|Gi].
      - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
      - destruct (Z.lt_ge_cases i 0) as [Ni|Pi]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
        rewrite (Z.bits_above_log2 (bytes_le_to_Z b1) i); [reflexivity | lia |].
        destruct (Z.eq_dec (bytes_le_to_Z b1) 0) as [Z0|Z0]; [rewrite Z0; cbn; lia|].
        apply Z.log2_lt_pow2; [lia|]. assert (2 ^ 32 <= 2 ^ i) by (apply Z.pow_le_mono_r; lia). lia. }
    rewrite <- Z.add_nocarry_lxor.
    + lia.
    + apply Z.bits_inj_0. intros i. rewrite Z.land_spec.
      destruct (Z.lt_ge_cases i 32) as [Li|Gi].
      * rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
      * destruct (Z.lt_ge_cases i 0) as [Ni|Pi]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
        rewrite (Z.bits_above_log2 (bytes_le_to_Z b1) i); [reflexivity | lia |].
        destruct (Z.eq_dec (bytes_le_to_Z b1) 0) as [Z0|Z0]; [rewrite Z0; cbn; lia|].
        apply Z.log2_lt_pow2; [lia|]. assert (2 ^ 32 <= 2 ^ i) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma rr4 : forall m E a k sx v, sc_denot segs m E (SCReadBase (SA a k) 4 sx (EVar v)) ->
  w4at m (u (adenot E (SA a k))) (u (ev E v) mod 2 ^ 32).
Proof.
  intros m E a k sx v (bs & Hr & Hv). cbn [edenot] in Hv. exists bs. rewrite Z_to_bv_bv_unsigned. split; [exact Hr|].
  pose proof (bytes4_rng bs (rdn_length segs m 4 _ bs Hr)) as R.
  rewrite <- Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct sx; cbn [extz].
  - set (x := bytes_le_to_Z bs) in *.
    rewrite <- (Znumtheory.Zmod_div_mod (2 ^ 32) (2 ^ 64)) by (lia || (exists (2 ^ 32); reflexivity)).
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N (8 * N.of_nat 4)) with (2 ^ 32).
    change (2 ^ 32 / 2) with (2 ^ 31).
    pose proof (Z_div_mod_eq_full (x + 2 ^ 31) (2 ^ 32)) as D.
    replace ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) with (x + (- ((x + 2 ^ 31) / 2 ^ 32)) * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
  - rewrite (Z.mod_small _ (2 ^ 64)) by lia. symmetry. apply Z.mod_small. lia.
Qed.

Lemma w4at_hit : forall E M b k v rest a, a = u (adenot E (SA b k)) -> a + 4 <= 2 ^ 64 ->
  w4at (mem_denot E M (SE (SA b k) 4 v :: rest)) a (u (edenot E v) mod 2 ^ 32).
Proof.
  intros E M b k v rest a Ha Hn. subst a. cbn [mem_denot]. exists (word_to_le_bytes 4 (edenot E v)).
  rewrite Z_to_bv_bv_unsigned. split.
  - pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 (edenot E v)) (mem_denot E M rest) (adenot E (SA b k))) as H.
    rewrite length_N_to_le_bytes in H. apply H. exact Hn.
  - rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). reflexivity.
Qed.

Lemma w4at_miss : forall E M b k w v rest a x, a + 4 <= 2 ^ 64 -> 0 <= a -> u (adenot E (SA b k)) + Z.of_nat w <= 2 ^ 64 ->
  (a + 4 <= u (adenot E (SA b k)) \/ u (adenot E (SA b k)) + Z.of_nat w <= a) ->
  w4at (mem_denot E M rest) a x -> w4at (mem_denot E M (SE (SA b k) w v :: rest)) a x.
Proof.
  intros E M b k w v rest a x Hn H0 Hs Hap (bs & Hr & <-). exists bs. split; [|reflexivity].
  cbn [mem_denot]. rewrite rdn_wbytes_out; [exact Hr | | | ].
  - rewrite u_small by lia. rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat] in *. lia.
  - rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. exact Hs.
Qed.
Lemma w4at_nil : forall E M a x, w4at M a x -> w4at (mem_denot E M []) a x.
Proof. intros E M a x H. exact H. Qed.
Lemma w4at_addr : forall M a a' w, w4at M a w -> a = a' -> w4at M a' w.
Proof. intros M a a' w H <-. exact H. Qed.

Lemma wat_addr : forall M a a' w, wat M a w -> a = a' -> wat M a' w.
Proof. intros M a a' w H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma nrm_unfold : forall M x n, SNU.g_nrm segs M x n <-> SNU.tbnd x n /\ (u n = 0 \/ SNU.topnz segs M x n).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma topnz_iff : forall M x n a W, wat M a W -> a = u x + 8 * u n - 8 -> (SNU.topnz segs M x n <-> W <> 0).
Proof.
  intros M x n a W HW Ha. subst a. split.
  - intros H. destruct (topnz_wat M x n H) as (w & Hw & Hnz). rewrite (wat_fun M _ W w HW Hw). exact Hnz.
  - intros Hnz. exact (wat_topnz M x n W HW Hnz).
Qed.
Lemma topw_iff : forall M a a' W, wat M a' W -> a' = u a - 8 -> 8 <= u a -> (SNU.g_topw segs M a <-> W <> 0).
Proof.
  intros M a a' W HW Ha' H8. subst a'. split.
  - intros H. destruct (topw_wat M a H) as (_ & w & Hw & Hnz). rewrite (wat_fun M _ W w HW Hw). exact Hnz.
  - intros Hnz. exact (wat_topw M a W H8 HW Hnz).
Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ue_lit : forall E z, u (edenot E (ELit z)) = z mod 2 ^ 64.
Proof. intros E z. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma ue_var : forall E n, u (edenot E (EVar n)) = u (ev E n).
Proof. reflexivity. Qed.
Lemma ue_add : forall E a b, u (edenot E (EAlu ALU_ADD a b)) = (u (edenot E a) + u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. cbn [edenot]. apply u_add64. Qed.
Lemma ue_sub : forall E a b, u (edenot E (EAlu ALU_SUB a b)) = (u (edenot E a) - u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. cbn [edenot]. apply u_sub64. Qed.
Lemma ue_mul : forall E a b, u (edenot E (EMd M_MUL a b)) = (u (edenot E a) * u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. cbn [edenot]. apply u_mul64. Qed.
Lemma ue_mulhu : forall E a b, u (edenot E (EMd M_MULHU a b)) = u (edenot E a) * u (edenot E b) / 2 ^ 64.
Proof. intros E a b. cbn [edenot]. apply u_mulhu64. Qed.
Lemma ue_sltu : forall E a b, u (edenot E (EAlu ALU_SLTU a b)) = if u (edenot E a) <? u (edenot E b) then 1 else 0.
Proof. intros E a b. cbn [edenot]. apply u_sltu64. Qed.
Lemma ue_srl : forall E a k, 0 <= k < 64 -> u (edenot E (EAlu ALU_SRL a (ELit k))) = u (edenot E a) / 2 ^ k.
Proof.
  intros E a k Hk. cbn [edenot]. rewrite u_srl64. f_equal. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small k (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma ue_sll : forall E a k, 0 <= k < 64 -> u (edenot E (EAlu ALU_SLL a (ELit k))) = (u (edenot E a) * 2 ^ k) mod 2 ^ 64.
Proof.
  intros E a k Hk. cbn [edenot]. rewrite u_sll64. f_equal. f_equal. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small k (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma ue_adenot : forall E b k, u (adenot E (SA b k)) = (u (edenot E b) + k) mod 2 ^ 64.
Proof. intros E b k. unfold adenot. cbn [a_base a_off]. unfold v_addi. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint zv (E : env) (e : expr) : Z :=
  match e with
  | ELit z => if (0 <=? z) && (z <? 18446744073709551616) then z else z mod 2 ^ 64
  | EVar n => u (ev E n)
  | EAlu ALU_ADD a b => (zv E a + zv E b) mod 2 ^ 64
  | EAlu ALU_SUB a b => (zv E a - zv E b) mod 2 ^ 64
  | EAlu ALU_SLTU a b => if zv E a <? zv E b then 1 else 0
  | EAlu ALU_SRL a b => zv E a / 2 ^ (zv E b mod 64)
  | EAlu ALU_SLL a b => (zv E a * 2 ^ (zv E b mod 64)) mod 2 ^ 64
  | EAlu ALU_OR a b => Z.lor (zv E a) (zv E b)
  | EAlu ALU_XOR a b => Z.lxor (zv E a) (zv E b)
  | EMd M_MUL a b => (zv E a * zv E b) mod 2 ^ 64
  | EMd M_MULHU a b => zv E a * zv E b / 2 ^ 64
  | _ => u (edenot E e)
  end.
Lemma zv_ok : forall E e, u (edenot E e) = zv E e.
Proof.
  intros E e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    try reflexivity.
  - cbn [zv]. rewrite ue_lit. destruct ((0 <=? z) && (z <? 18446744073709551616))%bool eqn:C; [|reflexivity].
    apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.mod_small. lia.
  - destruct op; try reflexivity.
    + rewrite ue_add, IHa, IHb. reflexivity.
    + rewrite ue_sub, IHa, IHb. reflexivity.
    + cbn [zv edenot]. rewrite u_sll64, IHa, IHb. reflexivity.
    + rewrite ue_sltu, IHa, IHb. reflexivity.
    + cbn [zv edenot]. rewrite u_xor64, IHa, IHb. reflexivity.
    + cbn [zv edenot]. rewrite u_srl64, IHa, IHb. reflexivity.
    + cbn [zv edenot]. unfold alu64, alu. rewrite bv_or_unsigned, IHa, IHb. reflexivity.
  - destruct op; try reflexivity.
    + rewrite ue_mul, IHa, IHb. reflexivity.
    + rewrite ue_mulhu, IHa, IHb. reflexivity.
Qed.
Lemma zv_adenot : forall E b k, u (adenot E (SA b k)) = (zv E b + k) mod 2 ^ 64.
Proof. intros E b k. rewrite ue_adenot, zv_ok. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac nv_forall H :=
  repeat match type of H with
  | Forall _ (_ :: _) => apply Forall_cons_iff in H; let X := fresh "G" in destruct H as [X H]
  | Forall _ [] => clear H
  end.

(* [comment removed for export] *)
Ltac nv_vals := rewrite ?zv_adenot, ?zv_ok in *; cbn [zv andb Z.leb Z.ltb Z.compare Pos.compare Pos.compare_cont] in *.
(* [comment removed for export] *)
Ltac nv_valsg := rewrite ?zv_adenot, ?zv_ok; cbn [zv andb Z.leb Z.ltb Z.compare Pos.compare Pos.compare_cont].

(* [comment removed for export] *)
Ltac nv_mods :=
  repeat match goal with
  | H : context [?x mod 2 ^ 64] |- _ =>
      lazymatch x with context [_ mod _] => fail | _ => idtac end;
      let B := fresh "B" in assert (B : 0 <= x < 2 ^ 64) by lia;     (* [comment removed for export] *)
      rewrite (Z.mod_small x (2 ^ 64) B) in H
  | |- context [?x mod 2 ^ 64] =>
      lazymatch x with context [_ mod _] => fail | _ => idtac end;
      rewrite (Z.mod_small x (2 ^ 64)) by lia
  end.
Ltac nv_modsg :=
  repeat match goal with
  | |- context [?x mod 2 ^ 64] =>
      lazymatch x with context [_ mod _] => fail | _ => idtac end;
      let B := fresh "B" in assert (B : 0 <= x < 2 ^ 64) by lia; rewrite (Z.mod_small x (2 ^ 64) B)
  end.

(* [comment removed for export] *)
Ltac nv_rngs :=
  repeat match goal with
  | |- context [u (ev ?E ?n)] =>
      lazymatch goal with _ : 0 <= u (ev E n) < 2 ^ 64 |- _ => fail | _ => pose proof (u_rng (ev E n)) end
  | H : context [u (ev ?E ?n)] |- _ =>
      lazymatch goal with _ : 0 <= u (ev E n) < 2 ^ 64 |- _ => fail | _ => pose proof (u_rng (ev E n)) end
  end.

(* [comment removed for export] *)
Ltac nv_pre :=
  unfold SG.vc_holds; cbn [SG.vc_kn SG.vc_path SG.vc_log SG.vc_src SG.vc_tgt SG.vc_facts];
  let E := fresh "E" in let m := fresh "m" in let HK := fresh "HK" in let HP := fresh "HP" in let HL := fresh "HL" in
  let HS := fresh "HS" in
  intros E m HK HP HL HS;
  lazymatch type of HK with know_ok ?segs _ _ ?kn =>
    let lx := eval vm_compute in (SNV.kdigestX kn kn) in
    let ZX := fresh "ZX" in
    assert (ZX : Forall (VP.zf_den E) lx)
      by (replace lx with (SNV.kdigestX kn kn) by (vm_compute; reflexivity); exact (SNV.kdigestX_sound segs E m kn kn HK HK));
    VP.vp_forall ZX;
    VP.vp_digest segs E m HK HP;
    repeat match goal with
      | P : sc_denot _ m E (SCReadBase (SA ?a ?k) 8 false (EVar ?v)) |- _ =>
          let R := fresh "R" in pose proof (rr8 segs m E a k v P) as R; clear P
      | P : sc_denot _ m E (SCReadBase (SA ?a ?k) 4 ?sx (EVar ?v)) |- _ =>
          let R := fresh "R" in pose proof (rr4 segs m E a k sx v P) as R; clear P
      end;
    repeat match goal with
      | P : sc_denot ?segs m E (SCBr false BC_LT ?a (ELit ?c)) |- _ =>
          let Q := fresh "Q" in pose proof (SNV.slt_lit_false segs m E a c ltac:(lia) P) as Q; clear P
      end;
    repeat match goal with
      | P : sc_denot ?segs m E (SCBr ?t ?c ?a ?b) |- _ =>
          lazymatch c with BC_LT => fail | BC_GE => fail | _ => idtac end;
          let Q := fresh "Q" in pose proof (SNV.scbr_u segs m E t c a b P) as Q; cbn beta iota in Q; clear P
      end;
    unfold SG.gholds in HS; nv_forall HS;
    cbn [SNU.snu_gp map ST.g_id ST.g_args] in *;
    unfold SNU.g_nrm, SNU.g_nrm62, SNU.g_nrmc, SNU.tbnd in *
  end.

(* [comment removed for export] *)
Ltac nv_src :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : SNU.topnz ?segs ?M ?x ?n |- _ =>
      let w := fresh "w" in let Hw := fresh "Hw" in let Hn := fresh "Hn" in
      destruct (topnz_wat segs M x n H) as (w & Hw & Hn); clear H
  | H : SNU.g_topw ?segs ?M ?a |- _ =>
      let w := fresh "w" in let Hw := fresh "Hw" in let Hn := fresh "Hn" in let H8 := fresh "H8" in
      destruct (topw_wat segs M a H) as (H8 & w & Hw & Hn); clear H
  end.

(* [comment removed for export] *)
Ltac nv_w44 :=
  repeat match goal with
  | H1 : w4at ?segs ?M ?a1 ?L, H2 : w4at ?segs ?M ?a2 ?H |- _ =>
      lazymatch goal with _ : wat segs M a1 (L + 2 ^ 32 * H) |- _ => fail | _ => idtac end;
      let Q := fresh "Q" in assert (Q : a2 = a1 + 4) by (nv_valsg; lia);
      let W := fresh "W4" in assert (W : wat segs M a1 (L + 2 ^ 32 * H)) by
        (apply wat_44; [nv_valsg; lia | nv_valsg; lia | exact H1 | rewrite <- Q; exact H2]); clear Q
  end.

(* [comment removed for export] *)
Ltac nv_wfun :=
  repeat match goal with
  | H1 : wat ?segs ?M ?a1 ?w1, H2 : wat ?segs ?M ?a2 ?w2 |- _ =>
      lazymatch w1 with w2 => fail | _ => idtac end;
      lazymatch goal with _ : w1 = w2 |- _ => fail | _ : w2 = w1 |- _ => fail | _ => idtac end;
      let Q := fresh "Q" in
      assert (Q : a1 = a2) by (nv_valsg; lia);
      let E := fresh "Ew" in assert (E : w1 = w2) by (apply (wat_fun segs M a1 w1 w2 H1); rewrite Q; exact H2); clear Q
  end.

(* [comment removed for export] *)
Ltac nv_apart := nv_valsg; cbn [Z.of_nat Pos.of_succ_nat]; first [lia | (unfold VP.disj in *; lia)].

(* [comment removed for export] *)
Ltac nv_walk4 :=
  lazymatch goal with
  | |- w4at ?segs (mem_denot ?E ?m (SE (SA ?b ?k) 4 ?v :: ?rest)) ?a _ =>
      first [ apply (w4at_hit segs E m b k v rest a); [ nv_valsg; lia | nv_valsg; lia ]
            | eapply (w4at_miss segs E m b k 4 v rest a); [ nv_valsg; lia | nv_valsg; lia | nv_apart | nv_apart | nv_walk4 ] ]
  | |- w4at ?segs (mem_denot ?E ?m (SE (SA ?b ?k) ?w ?v :: ?rest)) ?a _ =>
      eapply (w4at_miss segs E m b k w v rest a); [ nv_valsg; lia | nv_valsg; lia | nv_apart | nv_apart | nv_walk4 ]
  | |- w4at ?segs (mem_denot ?E ?m []) ?a _ =>
      apply w4at_nil; match goal with H : w4at segs m ?a' ?w |- _ => apply (w4at_addr segs m a' a w H); nv_valsg; lia end
  end.

(* [comment removed for export] *)
Ltac nv_walk :=
  lazymatch goal with
  | |- wat ?segs (mem_denot ?E ?m (SE (SA ?b ?k) 8 ?v :: ?rest)) ?a _ =>
      first [ apply (wat_hit segs E m b k v rest a); [ nv_valsg; lia | nv_valsg; lia ]
            | eapply (wat_miss segs E m b k 8 v rest a); [ nv_valsg; lia | nv_valsg; lia | nv_apart | nv_apart | nv_walk ] ]
  | |- wat ?segs (mem_denot ?E ?m (SE (SA ?b ?k) ?w ?v :: ?rest)) ?a _ =>
      first [ eapply (wat_miss segs E m b k w v rest a); [ nv_valsg; lia | nv_valsg; lia | nv_apart | nv_apart | nv_walk ]
            | apply wat_44; [ nv_valsg; lia | nv_valsg; lia | nv_walk4 | nv_walk4 ] ]
  | |- wat ?segs (mem_denot ?E ?m []) ?a _ =>
      apply wat_nil; match goal with H : wat segs m ?a' ?w |- _ => apply (wat_addr segs m a' a w H); nv_valsg; lia end
  | |- wat ?segs ?m ?a _ =>
      match goal with H : wat segs m ?a' ?w |- _ => apply (wat_addr segs m a' a w H); nv_valsg; lia end
  end.

(* [comment removed for export] *)
Ltac nv_shl :=
  repeat match goal with
  | |- context [Z.lor ((?x * 2 ^ ?e1) mod 2 ^ 64) (?p / 2 ^ ?e2)] =>
      lazymatch goal with _ : Z.lor ((x * 2 ^ e1) mod 2 ^ 64) (p / 2 ^ e2) <> 0 |- _ => fail | _ => idtac end;
      pose proof (shl_top_nz x p e1 e2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  end.

(* [comment removed for export] *)
Ltac nv_ifs :=
  repeat match goal with
  | |- context [if ?a <? ?b then 1 else 0] => destruct (Z.ltb_spec a b)
  | H : context [if ?a <? ?b then 1 else 0] |- _ => destruct (Z.ltb_spec a b)
  end.

(* [comment removed for export] *)
Lemma wk2 : forall A B C : Prop, A \/ B -> A \/ B \/ C.
Proof. intros A B C [H|H]; [left|right; left]; exact H. Qed.
Lemma wk3 : forall A B C D : Prop, A \/ B \/ C -> A \/ B \/ C \/ D.
Proof. intros A B C D [H|[H|H]]; [left|right; left|right; right; left]; exact H. Qed.
Lemma wk1 : forall A D : Prop, A -> A \/ D.
Proof. intros A D H. left. exact H. Qed.

(* [comment removed for export] *)
Ltac nv_smul :=
  repeat match goal with
  | |- context [((?c + (?x * ?y) mod 2 ^ 64) mod 2 ^ 64)] =>
      lazymatch goal with _ : ((c + (x * y) mod 2 ^ 64) mod 2 ^ 64) <> 0 \/ _ |- _ => fail | _ => idtac end;
      pose proof (smul_nz x y c ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  end.

Ltac nv_clear :=
  repeat match goal with
  | H : know_ok _ _ _ _ |- _ => clear H
  | H : log_flat _ _ |- _ => clear H
  | H : sc_denot _ _ _ _ |- _ => clear H
  end.

Ltac nv_z := nv_valsg; nv_rngs; nv_ifs; lia.

(* [comment removed for export] *)
Ltac nv_dsplit a E log :=
  lazymatch log with
  | SE (SA ?b ?k) ?w ?v :: ?rest =>
      first [ (assert (a = u (adenot E (SA b k))) as _ by (nv_valsg; lia)); fail 1   (* [comment removed for export] *)
            | (assert (a + 8 <= u (adenot E (SA b k)) \/ u (adenot E (SA b k)) + Z.of_nat w <= a) as _
                 by (nv_valsg; cbn [Z.of_nat Pos.of_succ_nat]; lia)); nv_dsplit a E rest
            | let D := fresh "D" in destruct (Z.eq_dec a (u (adenot E (SA b k)))) as [D|D];
              rewrite ?zv_adenot, ?zv_ok in D; cbn [zv andb Z.leb Z.ltb Z.compare Pos.compare Pos.compare_cont] in D ]
  end.

Ltac nv_topnz_goal segs M x n :=
  let HW := fresh "HW" in
  eassert (HW : wat segs M (u x + 8 * u n - 8) _) by nv_walk;
  rewrite (topnz_iff segs M x n _ _ HW eq_refl); nv_w44; nv_wfun; nv_valsg; nv_rngs; nv_smul; nv_shl; nv_ifs; lia.

(* [comment removed for export] *)
Ltac nv_atom :=
  lazymatch goal with
  | |- _ /\ _ => split; [nv_z | nv_atom]
  | |- ?A \/ ?B \/ ?C \/ SNU.topnz ?segs ?M ?x ?n =>
      first [ apply wk3; nv_z | nv_topnz_goal segs M x n | nv_atom_split segs M x n | (exfalso; nv_z) ]
  | |- ?A \/ ?B \/ SNU.topnz ?segs ?M ?x ?n =>
      first [ apply wk2; nv_z | nv_topnz_goal segs M x n | nv_atom_split segs M x n | (exfalso; nv_z) ]
  | |- ?A \/ SNU.topnz ?segs ?M ?x ?n =>
      first [ apply wk1; nv_z | nv_topnz_goal segs M x n | nv_atom_split segs M x n | (exfalso; nv_z) ]
  | |- SNU.g_topw ?segs ?M ?a =>
      first [ let HW := fresh "HW" in
              eassert (HW : wat segs M (u a - 8) _) by nv_walk;
              rewrite (topw_iff segs M a _ _ HW eq_refl ltac:(nv_z)); nv_w44; nv_wfun; nv_valsg; nv_rngs; nv_ifs; lia
            | (exfalso; nv_z) ]
  | |- _ => nv_z
  end
with nv_atom_split segs M x n :=
  lazymatch M with mem_denot ?E ?m ?log =>
    nv_dsplit (u x + 8 * u n - 8) E log; nv_atom end.

(* [comment removed for export] *)
Ltac nv_goal :=
  lazymatch goal with |- SG.gholds _ _ _ _ /\ know_ok _ _ _ _ =>
    split; [unfold SG.gholds; repeat (apply Forall_cons; [|]); try apply Forall_nil | ]
  end;
  cbn [SNU.snu_gp map ST.g_id ST.g_args] in *;
  unfold SNU.g_nrm, SNU.g_nrm62, SNU.g_nrmc, SNU.tbnd in *;
  try (lazymatch goal with |- know_ok _ _ _ _ => unfold know_ok; repeat (apply Forall_cons; [|]); try apply Forall_nil end);
  cbn [kentry_ok] in *.

(* [comment removed for export] *)
Ltac nv_litops :=
  repeat match goal with
  | |- context [Z.lxor ?a ?b] => let c := eval vm_compute in (Z.lxor a b) in
                                 lazymatch c with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (Z.lxor a b) with c
  | |- context [Z.lor ?a ?b] => let c := eval vm_compute in (Z.lor a b) in
                                lazymatch c with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (Z.lor a b) with c
  end.
Ltac nv_flagleaf := nv_valsg; nv_ifs; nv_litops; first [lia | (unfold VP.disj in *; lia)].
Ltac nv_flags :=
  SNV.sn_pre; SNV.sn_goal;
  lazymatch goal with HK : know_ok ?segs ?E ?m _ |- _ => SNV.sn_lin segs E m HK; SNV.sn_aluw; SNV.sn_lin segs E m HK end;
  SNV.sn_ext; SNV.sn_bats; SNV.sn_hyps; SNV.sn_clear; SNV.sn_hmods; SNV.sn_gmods;
  repeat split; solve [SNV.sn_leaf | nv_flagleaf].

Ltac nv_solve :=
  nv_pre; nv_src; nv_clear; nv_vals; nv_rngs; nv_goal; nv_wfun; nv_atom.
End NRV.
