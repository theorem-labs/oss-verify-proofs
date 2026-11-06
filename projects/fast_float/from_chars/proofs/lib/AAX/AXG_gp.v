(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.

Module AXF_np0bc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition STK := SA (EVar 2) (-1024).
Definition sr_np0bc := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (e_CA)) 12 (e_ND)) 13 (ELit 8)).
Definition kn_np0bc : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 513 65536;
    KRange (EVar 2) (2^46) (2^47);
    KWr STK (ELit 1024) ].
Definition scr_np0bc : scripts := SCR [] [] [].
Definition ss_np0bc := SS 0x43ce8 sr_np0bc [] kn_np0bc 34.
Definition RUN_np0bc := sym_exec SEGS 120 true [0x43e7c] scr_np0bc ss_np0bc [].

Definition scr_pnp0bc : scripts := SCR [] [] [].
Definition RES_pnp0bc := Eval vm_compute in sym_exec SEGS 120 true [0x43e7c] scr_pnp0bc ss_np0bc [].
Lemma RES_pnp0bc_ok : sym_exec SEGS 120 true [0x43e7c] scr_pnp0bc (SS 0x43ce8 sr_np0bc [] kn_np0bc 34) [] = RES_pnp0bc.
Proof. vm_compute. reflexivity. Qed.
End AXF_np0bc.

Module AXG_npb.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFold.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition cid (nd : Z) : Z :=
  let l := Z.log2 nd in
  16 + 2 * (l - 9) + Z.land (Z.shiftr nd (l - 1)) 1 + (if Z.eqb (Z.land nd (Z.ones (l - 1))) 0 then 0 else 1).

(* [comment removed for export] *)
Definition CLS_E : expr := let '(s, _, _) := AXF_np0bc.RES_pnp0bc in sr_get (s_regs s) (Z_to_bv 5 8).
Definition cls_fun (w : word) : word :=
  let x0 := (alu64 ALU_SRL w (Z_to_bv 64 (1))) in
  let x1 := (alu64 ALU_OR w x0) in
  let x2 := (alu64 ALU_SRL x1 (Z_to_bv 64 (2))) in
  let x3 := (alu64 ALU_OR x1 x2) in
  let x4 := (alu64 ALU_SRL x3 (Z_to_bv 64 (4))) in
  let x5 := (alu64 ALU_OR x3 x4) in
  let x6 := (alu64 ALU_SRL x5 (Z_to_bv 64 (8))) in
  let x7 := (alu64 ALU_OR x5 x6) in
  let x8 := (alu64 ALU_SRL x7 (Z_to_bv 64 (16))) in
  let x9 := (alu64 ALU_OR x7 x8) in
  let x10 := (mul_div M_MUL (Z_to_bv 64 (-1)) x9) in
  let x11 := (alu64 ALU_ADD x10 (Z_to_bv 64 (-1))) in
  let x12 := (alu64 ALU_SRL x11 (Z_to_bv 64 (1))) in
  let x13 := (alu64 ALU_AND x12 (Z_to_bv 64 (6148914691236517205))) in
  let x14 := (mul_div M_MUL (Z_to_bv 64 (-1)) x13) in
  let x15 := (alu64 ALU_ADD x10 x14) in
  let x16 := (alu64 ALU_ADD x15 (Z_to_bv 64 (-1))) in
  let x17 := (alu64 ALU_AND x16 (Z_to_bv 64 (3689348814741910323))) in
  let x18 := (alu64 ALU_SRL x16 (Z_to_bv 64 (2))) in
  let x19 := (alu64 ALU_AND x18 (Z_to_bv 64 (3689348814741910323))) in
  let x20 := (alu64 ALU_ADD x17 x19) in
  let x21 := (alu64 ALU_SRL x20 (Z_to_bv 64 (4))) in
  let x22 := (alu64 ALU_ADD x21 x20) in
  let x23 := (alu64 ALU_AND x22 (Z_to_bv 64 (1085102592571150095))) in
  let x24 := (mul_div M_MUL (Z_to_bv 64 (72340172838076673)) x23) in
  let x25 := (alu64 ALU_SRL x24 (Z_to_bv 64 (56))) in
  let x26 := (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 (62))) (low32 x25))) in
  let x27 := (sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 (18446744073709551615))) (low32 x26))) in
  let x28 := (mul_div M_MUL (Z_to_bv 64 (-1)) x27) in
  let x29 := (alu64 ALU_ADD x28 (Z_to_bv 64 (-1))) in
  let x30 := (alu64 ALU_AND w x29) in
  let x31 := (alu64 ALU_SLTU (Z_to_bv 64 (0)) x30) in
  let x32 := (mul_div M_MUL (Z_to_bv 64 (2)) x25) in
  let x33 := (alu64 ALU_XOR x32 (Z_to_bv 64 (126))) in
  let x34 := (alu64 ALU_SRL w x26) in
  let x35 := (alu64 ALU_AND x34 (Z_to_bv 64 (1))) in
  let x36 := (alu64 ALU_OR x33 x35) in
  let x37 := (alu64 ALU_ADD x31 x36) in
  let x38 := (alu64 ALU_ADD x37 (Z_to_bv 64 (-2))) in
  x38.
Lemma cls_fun_eq : forall E, edenot E CLS_E = cls_fun (ev E 33).
Proof. intros E. reflexivity. Qed.

(* [comment removed for export] *)
Definition smear_b (w : word) : word :=
  let x0 := (alu64 ALU_SRL w (Z_to_bv 64 (1))) in
  let x1 := (alu64 ALU_OR w x0) in
  let x2 := (alu64 ALU_SRL x1 (Z_to_bv 64 (2))) in
  let x3 := (alu64 ALU_OR x1 x2) in
  let x4 := (alu64 ALU_SRL x3 (Z_to_bv 64 (4))) in
  let x5 := (alu64 ALU_OR x3 x4) in
  let x6 := (alu64 ALU_SRL x5 (Z_to_bv 64 (8))) in
  let x7 := (alu64 ALU_OR x5 x6) in
  let x8 := (alu64 ALU_SRL x7 (Z_to_bv 64 (16))) in
  let x9 := (alu64 ALU_OR x7 x8) in
  x9.
Definition pc_b (s : word) : word :=
  let x10 := (mul_div M_MUL (Z_to_bv 64 (-1)) s) in
  let x11 := (alu64 ALU_ADD x10 (Z_to_bv 64 (-1))) in
  let x12 := (alu64 ALU_SRL x11 (Z_to_bv 64 (1))) in
  let x13 := (alu64 ALU_AND x12 (Z_to_bv 64 (6148914691236517205))) in
  let x14 := (mul_div M_MUL (Z_to_bv 64 (-1)) x13) in
  let x15 := (alu64 ALU_ADD x10 x14) in
  let x16 := (alu64 ALU_ADD x15 (Z_to_bv 64 (-1))) in
  let x17 := (alu64 ALU_AND x16 (Z_to_bv 64 (3689348814741910323))) in
  let x18 := (alu64 ALU_SRL x16 (Z_to_bv 64 (2))) in
  let x19 := (alu64 ALU_AND x18 (Z_to_bv 64 (3689348814741910323))) in
  let x20 := (alu64 ALU_ADD x17 x19) in
  let x21 := (alu64 ALU_SRL x20 (Z_to_bv 64 (4))) in
  let x22 := (alu64 ALU_ADD x21 x20) in
  let x23 := (alu64 ALU_AND x22 (Z_to_bv 64 (1085102592571150095))) in
  let x24 := (mul_div M_MUL (Z_to_bv 64 (72340172838076673)) x23) in
  let x25 := (alu64 ALU_SRL x24 (Z_to_bv 64 (56))) in
  x25.
Definition k26 (p : word) : word := sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 62)) (low32 p)).
Definition k29 (p : word) : word :=
  let x27 := sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 18446744073709551615)) (low32 (k26 p))) in
  let x28 := mul_div M_MUL (Z_to_bv 64 (-1)) x27 in alu64 ALU_ADD x28 (Z_to_bv 64 (-1)).
Definition k33 (p : word) : word := alu64 ALU_XOR (mul_div M_MUL (Z_to_bv 64 2) p) (Z_to_bv 64 126).
Definition tail2 (w c26 c29 c33 : word) : word :=
  let x30 := alu64 ALU_AND w c29 in let x31 := alu64 ALU_SLTU (Z_to_bv 64 0) x30 in
  let x34 := alu64 ALU_SRL w c26 in let x35 := alu64 ALU_AND x34 (Z_to_bv 64 1) in
  let x36 := alu64 ALU_OR c33 x35 in let x37 := alu64 ALU_ADD x31 x36 in alu64 ALU_ADD x37 (Z_to_bv 64 (-2)).
Lemma cls_fun_split : forall w, cls_fun w = tail2 w (k26 (pc_b (smear_b w))) (k29 (pc_b (smear_b w))) (k33 (pc_b (smear_b w))).
Proof. intros w. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alu64_z : forall op x y, 0 <= x < two64 -> 0 <= y < two64 -> alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (alu_z op x y).
Proof. intros op x y Hx Hy. rewrite (alu_z_ok op x y Hx Hy). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma alu_z_range : forall op x y, 0 <= x < two64 -> 0 <= y < two64 -> 0 <= alu_z op x y < two64.
Proof. intros op x y Hx Hy. rewrite (alu_z_ok op x y Hx Hy). pose proof (bv_unsigned_in_range _ (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y))) as H. exact H. Qed.
Ltac zrng := solve [repeat (apply alu_z_range); unfold two64 in *; lia].
Ltac zb := repeat (rewrite alu64_z by zrng).

(* [comment removed for export] *)
Lemma smear_step_bit : forall s k n, 0 <= s -> 0 <= k -> 0 <= n ->
  Z.testbit (Z.lor s (Z.shiftr s k)) n = (Z.testbit s n || Z.testbit s (n + k))%bool.
Proof. intros s k n Hs Hk Hn. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition smear5 (x : Z) : Z :=
  let x1 := Z.lor x (Z.shiftr x 1) in let x3 := Z.lor x1 (Z.shiftr x1 2) in let x5 := Z.lor x3 (Z.shiftr x3 4) in
  let x7 := Z.lor x5 (Z.shiftr x5 8) in Z.lor x7 (Z.shiftr x7 16).

(* [comment removed for export] *)
Fixpoint smk (k : nat) (x : Z) : Z := match k with O => x | S k' => let s := smk k' x in Z.lor s (Z.shiftr s (2 ^ Z.of_nat k')) end.
Lemma smk_nonneg : forall k x, 0 <= x -> 0 <= smk k x.
Proof. induction k as [|k IH]; intros x Hx; cbn [smk]; [exact Hx|]. apply Z.lor_nonneg. split; [apply IH; exact Hx | apply Z.shiftr_nonneg; apply IH; exact Hx]. Qed.
Lemma smk_bit : forall k x n, 0 <= x -> 0 <= n ->
  Z.testbit (smk k x) n = true <-> exists j, 0 <= j < 2 ^ Z.of_nat k /\ Z.testbit x (n + j) = true.
Proof.
  induction k as [|k IH]; intros x n Hx Hn; cbn [smk].
  - change (2 ^ Z.of_nat 0) with 1. split; [intros H; exists 0; split; [lia | rewrite Z.add_0_r; exact H] | intros (j & Hj & H); replace j with 0 in H by lia; rewrite Z.add_0_r in H; exact H].
  - assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    rewrite smear_step_bit by (try apply smk_nonneg; lia). rewrite orb_true_iff, (IH x n Hx Hn), (IH x (n + 2 ^ Z.of_nat k) Hx ltac:(lia)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. split.
    + intros [(j & Hj & H)|(j & Hj & H)]; [exists j; split; [lia | exact H] | exists (2 ^ Z.of_nat k + j); split; [lia | rewrite Z.add_assoc; exact H]].
    + intros (j & Hj & H). destruct (Z_lt_le_dec j (2 ^ Z.of_nat k)) as [Hl|Hl].
      * left. exists j. split; [lia | exact H].
      * right. exists (j - 2 ^ Z.of_nat k). split; [lia | replace (n + 2 ^ Z.of_nat k + (j - 2 ^ Z.of_nat k)) with (n + j) by ring; exact H].
Qed.
Lemma smear5_smk : forall x, smear5 x = smk 5 x.
Proof. intros x. reflexivity. Qed.

Lemma smear5_eq : forall x, 0 < x < 2 ^ 32 -> smear5 x = Z.ones (Z.log2 x + 1).
Proof.
  intros x Hx. rewrite smear5_smk. pose proof (Z.log2_spec x ltac:(lia)) as [L1 L2]. pose proof (Z.log2_nonneg x) as L0.
  assert (Hl : Z.log2 x < 32) by (apply Z.log2_lt_pow2; lia).
  apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_ones by lia.
  destruct (Z.testbit (smk 5 x) n) eqn:Hb.
  - apply (smk_bit 5 x n ltac:(lia) Hn) in Hb as (j & Hj & Hb). symmetry. apply andb_true_iff. split; [apply Z.leb_le; lia|].
    apply Z.ltb_lt. destruct (Z_lt_le_dec n (Z.log2 x + 1)) as [H|H]; [exact H|].
    exfalso. rewrite Z.bits_above_log2 in Hb; [discriminate | lia | lia].
  - symmetry. apply andb_false_iff. destruct (Z_lt_le_dec n (Z.log2 x + 1)) as [H|H]; [|right; apply Z.ltb_ge; lia].
    exfalso. assert (Ht : Z.testbit (smk 5 x) n = true).
    { apply (smk_bit 5 x n ltac:(lia) Hn). exists (Z.log2 x - n). split; [change (2 ^ Z.of_nat 5) with 32; lia|].
      replace (n + (Z.log2 x - n)) with (Z.log2 x) by ring. apply Z.bit_log2. lia. }
    rewrite Hb in Ht. discriminate.
Qed.

Lemma smear_z : forall x, 0 <= x < two64 -> smear_b (Z_to_bv 64 x) = Z_to_bv 64 (smear5 x).
Proof. intros x Hx. unfold smear_b. cbv zeta. zb. reflexivity. Qed.

(* [comment removed for export] *)
Lemma l_cases : forall l, 9 <= l <= 16 -> l = 9 \/ l = 10 \/ l = 11 \/ l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16.
Proof. intros l Hl. lia. Qed.
Lemma pc_tab : forall l, 9 <= l <= 16 -> pc_b (Z_to_bv 64 (Z.ones (l + 1))) = Z_to_bv 64 (63 - l).
Proof. intros l Hl. destruct (l_cases l Hl) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; apply bv_eq; vm_compute; reflexivity. Qed.
Lemma k_tab : forall l, 9 <= l <= 16 ->
  k26 (Z_to_bv 64 (63 - l)) = Z_to_bv 64 (l - 1) /\ k29 (Z_to_bv 64 (63 - l)) = Z_to_bv 64 (Z.ones (l - 1)) /\ k33 (Z_to_bv 64 (63 - l)) = Z_to_bv 64 (2 * l).
Proof. intros l Hl. destruct (l_cases l Hl) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; refine (conj _ (conj _ _)); apply bv_eq; vm_compute; reflexivity. Qed.

Lemma lor_even_bit : forall a h, 0 <= a -> a mod 2 = 0 -> 0 <= h <= 1 -> Z.lor a h = a + h.
Proof.
  intros a h Ha Hm Hh.
  assert (H0 : Z.land a h = 0).
  { destruct (Z.eq_dec h 0) as [->|Hh1]; [apply Z.land_0_r|]. replace h with 1 by lia.
    change 1 with (Z.ones 1). rewrite Z.land_ones by lia. exact Hm. }
  rewrite <- (Z.lxor_lor a h H0). symmetry. apply Z.add_nocarry_lxor. exact H0.
Qed.

Lemma land1_range : forall v, 0 <= v -> 0 <= Z.land v 1 <= 1.
Proof.
  intros v Hv. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound v 2 ltac:(lia)) as H.
  change (2 ^ Z.ones 1) with 2. change (Z.ones 1) with 1. lia.
Qed.
Lemma tail_z : forall x l, 9 <= l <= 16 -> 2 ^ l <= x < 2 ^ (l + 1) ->
  tail2 (Z_to_bv 64 x) (Z_to_bv 64 (l - 1)) (Z_to_bv 64 (Z.ones (l - 1))) (Z_to_bv 64 (2 * l)) = Z_to_bv 64 (cid x).
Proof.
  intros x l Hl Hx.
  assert (Hp : 2 ^ 9 <= 2 ^ l /\ 2 ^ (l + 1) <= 2 ^ 17) by (split; apply Z.pow_le_mono_r; lia).
  assert (Ho : 0 <= Z.ones (l - 1) < two64) by (rewrite Z.ones_equiv; assert (2 ^ (l - 1) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia); unfold two64; lia).
  unfold tail2. cbv zeta. replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 18446744073709551614) by (apply bv_eq; reflexivity).
  zb. f_equal.
  assert (HL : Z.log2 x = l) by (apply Z.log2_unique; lia).
  unfold cid. rewrite HL. cbn [alu_z].
  set (lb := Z.land x (Z.ones (l - 1))). set (hb := Z.land (Z.shiftr x (Z.land (l - 1) 63)) 1).
  assert (Hsh : Z.land (l - 1) 63 = l - 1) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  assert (Hhb : 0 <= hb <= 1) by (unfold hb; apply land1_range; apply Z.shiftr_nonneg; lia).
  assert (Hlb : 0 <= lb) by (unfold lb; apply Z.land_nonneg; left; lia).
  rewrite lor_even_bit by (try lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
  unfold hb in *. rewrite Hsh in *.
  set (h := Z.land (Z.shiftr x (l - 1)) 1) in *. rewrite !w64_mod.
  set (b := if 0 <? lb then 1 else 0).
  assert (Hb : 0 <= b <= 1) by (unfold b; destruct (0 <? lb); lia).
  assert (Hb' : (if lb =? 0 then 0 else 1) = b) by (unfold b; destruct (Z.ltb_spec 0 lb); destruct (Z.eqb_spec lb 0); try reflexivity; lia).
  rewrite Hb'. rewrite (Z.mod_small (b + (2 * l + h)) FxLin.two64) by (unfold FxLin.two64; lia).
  rewrite <- (Z.mod_unique (b + (2 * l + h) + 18446744073709551614) FxLin.two64 1 (b + 2 * l + h - 2)) by (unfold FxLin.two64; lia). lia.
Qed.

Lemma cls_eq : forall E nd, 513 <= nd <= 65536 -> ev E 33 = Z_to_bv 64 nd -> edenot E CLS_E = Z_to_bv 64 (cid nd).
Proof.
  intros E nd Hnd Hv. rewrite cls_fun_eq, Hv, cls_fun_split.
  set (l := Z.log2 nd). pose proof (Z.log2_spec nd ltac:(lia)) as [L1 L2]. fold l in L1, L2.
  assert (Hl : 9 <= l <= 16).
  { split; [destruct (Z_lt_le_dec l 9) as [H|H]; [|exact H]; assert (2 ^ (l + 1) <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia); lia|].
    unfold l. change 16 with (Z.log2 65536). apply Z.log2_le_mono. lia. }
  rewrite smear_z by (unfold two64; lia). rewrite smear5_eq by lia. fold l. rewrite (pc_tab l Hl).
  destruct (k_tab l Hl) as (K1 & K2 & K3). rewrite K1, K2, K3. exact (tail_z nd l Hl ltac:(lia)).
Qed.

Section NPB.
Context {fx : FPState}.

Definition VALS_np0bc (CA ND : Z) : list Z := [CA; ND].

Record np0bc_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND : Z) : Prop := {
  np0bc_R10 : getr regs 10 = wa 923480 ;
  np0bc_R11 : getr regs 11 = wa CA ;
  np0bc_R12 : getr regs 12 = wa ND ;
  np0bc_R13 : getr regs 13 = wa 8 ;
  np0bc_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  np0bc_rng_CA : 1 <= CA <= 2^47 ;
  np0bc_rng_ND : 513 <= ND <= 65536 ;
  np0bc_ka1 : CA mod 16 = 0 ;
  np0bc_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47)
}.

#[using="Type"] Lemma np0bc_setup : forall regs m CA ND, np0bc_pre regs m CA ND ->
  regs_ok (Ez regs (VALS_np0bc CA ND)) AXF_np0bc.sr_np0bc regs /\ know_ok SEGS (Ez regs (VALS_np0bc CA ND)) m AXF_np0bc.kn_np0bc.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND P. destruct P as [np0bc_R10 np0bc_R11 np0bc_R12 np0bc_R13 np0bc_HSTK np0bc_rng_CA np0bc_rng_ND np0bc_ka1 np0bc_kr3].
  set (E := Ez regs (VALS_np0bc CA ND)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  split.
  { unfold AXF_np0bc.sr_np0bc.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite np0bc_R10. reflexivity.
    - rewrite np0bc_R11. reflexivity.
    - rewrite np0bc_R12. reflexivity.
    - rewrite np0bc_R13. reflexivity. }
  unfold know_ok, AXF_np0bc.kn_np0bc.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024);
                 [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
  all: cbn [zeval edenot AXF_np0bc.e_CA AXF_np0bc.e_ND AXF_np0bc.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ np0bc_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ np0bc_rng_ND eq_refl eq_refl).
  all: litmods.
  all: try assumption.
  all: try (clear - np0bc_rng_CA np0bc_rng_ND np0bc_ka1 np0bc_kr3; lia).
  all: first [lia].
Qed.

(* [comment removed for export] *)
Definition np0bc_mem (m : word -> option byte) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
    (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
    (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
    (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
    (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
    (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
    (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))).

Definition KNPB : list nat := [1; 3; 4; 7; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

#[using="Type"] Theorem np_cls_big : forall regs m rom CA ND, np0bc_pre regs m CA ND ->
  exists R, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R (wa 0x43e7c) (np0bc_mem m regs) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48) /\ getr R 8 = wa (cid ND) /\
    getr R 10 = wa 923480 /\ getr R 11 = wa CA /\ getr R 13 = wa 8 /\
    (forall k, In k KNPB -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND P. destruct (np0bc_setup regs m CA ND P) as [HR HK].
  set (E := Ez regs (VALS_np0bc CA ND)) in *.
  destruct P as [np0bc_R10 np0bc_R11 np0bc_R12 np0bc_R13 np0bc_HSTK np0bc_rng_CA np0bc_rng_ND np0bc_ka1 np0bc_kr3].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 120 [0x43e7c] AXF_np0bc.scr_pnp0bc 0x43ce8 AXF_np0bc.sr_np0bc AXF_np0bc.kn_np0bc 34 _ _ _ E m rom regs
              AXF_np0bc.RES_pnp0bc_ok HR HK ltac:(cbn [AXF_np0bc.RES_pnp0bc fst snd]; constructor)) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_np0bc.RES_pnp0bc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (np0bc_mem m regs) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold np0bc_mem. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
  - assert (H8 : getr R 8 = edenot E CLS_E).
    { unfold CLS_E. rewrite (HR' _). reflexivity. }
    clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [rewrite H8; apply (cls_eq E ND np0bc_rng_ND); apply bv_eq; rewrite Z33, u_wa_small by lia; reflexivity|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.
End NPB.
End AXG_npb.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXG_npb.

Module AXF_ghs.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition STK := SA (EVar 2) (-1024).
Definition sr_ghs := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (e_CA)) 12 (e_ND)) 13 (ELit 8)).
Definition kn_ghs : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 1 512;
    KRange (EVar 2) (2^46) (2^47);
    KWr STK (ELit 1024) ].
Definition scr_ghs : scripts := SCR [] [] [].
Definition ss_ghs := SS 0x43ce8 sr_ghs [] kn_ghs 34.
Definition RUN_ghs := sym_exec SEGS 60 true [0x43e7c] scr_ghs ss_ghs [].

Definition scr_pghs : scripts := SCR [] [] [].
Definition RES_pghs := Eval vm_compute in sym_exec SEGS 60 true [0x43e7c] scr_pghs ss_ghs [].
Lemma RES_pghs_ok : sym_exec SEGS 60 true [0x43e7c] scr_pghs (SS 0x43ce8 sr_ghs [] kn_ghs 34) [] = RES_pghs.
Proof. vm_compute. reflexivity. Qed.
End AXF_ghs.


Module AXF_gnp0t.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_cnt := EVar 34.
Definition e_sz := EVar 35.
Definition e_cp := EVar 36.
Definition e_SB := EVar 37.
Definition e_st := EVar 38.
Definition e_s0o := EVar 39.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition CHP := EAlu ALU_ADD e_CA (EAlu ALU_ADD (EMd M_MUL (ELit 80) e_CLS) (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_cnt)) (ELit (-4294967296))) (ELit 30))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_gnp0t := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_CLS)) 10 (ELit 923480)) 11 (e_CA)) 13 (ELit 8)).
Definition kn_gnp0t : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (EVar 2) 40) 8 (EVar 1);
    KWord (SA (EVar 2) 32) 8 e_s0o;
    KWord (SA (EVar 2) 24) 8 (EVar 9);
    KWord (SA (EVar 2) 16) 8 (EVar 18);
    KWord (SA (EVar 2) 8) 8 (EVar 19);
    KWord (SA (EVar 2) 0) 8 (EVar 20);
    KWord (SA REC 0) 4 e_cnt;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA CHP 16) 4 e_cp;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_gnp0t : scripts := SCR [false] [] [].
Definition ss_gnp0t := SS 0x43e7c sr_gnp0t [] kn_gnp0t 40.
Definition RUN_gnp0t := sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_gnp0t ss_gnp0t [].

Definition scr_pnp0tp : scripts := SCR [false] [] [].
Definition RES_pnp0tp := Eval vm_compute in sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0tp ss_gnp0t [].
Lemma RES_pnp0tp_ok : sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0tp (SS 0x43e7c sr_gnp0t [] kn_gnp0t 40) [] = RES_pnp0tp.
Proof. vm_compute. reflexivity. Qed.
End AXF_gnp0t.


Module AXF_gnp0tz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNP0T.
Context {fx : FPState}.

Definition VALS_gnp0t (CA CLS cnt sz cp SB st s0o : Z) : list Z := [CA; CLS; cnt; sz; cp; SB; st; s0o].

Record gnp0t_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS cnt sz cp SB st s0o : Z) : Prop := {
  gnp0t_R8 : getr regs 8 = wa CLS ;
  gnp0t_R10 : getr regs 10 = wa 923480 ;
  gnp0t_R11 : getr regs 11 = wa CA ;
  gnp0t_R13 : getr regs 13 = wa 8 ;
  gnp0t_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gnp0t_rng_CA : 1 <= CA <= 2^47 ;
  gnp0t_rng_CLS : 1 <= CLS <= 30 ;
  gnp0t_rng_cnt : 0 <= cnt <= 2^32-1 ;
  gnp0t_rng_sz : 0 <= sz <= 2^64-1 ;
  gnp0t_rng_cp : 0 <= cp <= 2^32-1 ;
  gnp0t_rng_SB : 0 <= SB <= 2^64-1 ;
  gnp0t_rng_st : 0 <= st <= 2^64-1 ;
  gnp0t_rng_s0o : 0 <= s0o <= 2^64-1 ;
  gnp0t_ka1 : CA mod 16 = 0 ;
  gnp0t_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gnp0t_kw4 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))) ;
  gnp0t_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa s0o)) ;
  gnp0t_kw6 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))) ;
  gnp0t_kw7 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))) ;
  gnp0t_kw8 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))) ;
  gnp0t_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) ;
  gnp0t_kw10 : rdn SEGS m (wa (CA + (80 * CLS) + 0)) 4 = Some (word_to_le_bytes 4 (wa cnt)) ;
  gnp0t_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + (80 * CLS) + 0 + d)) k = true ;
  gnp0t_kw12 : rdn SEGS m (wa (CA + (80 * CLS) + 8)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  gnp0t_kw13 : rdn SEGS m (wa (CA + ((80 * CLS) + Z.shiftr ((((4294967296 * ext_Z true 0 4 cnt) + -4294967296)) mod 2^64) 30) + 16)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  gnp0t_kw14 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  gnp0t_kw15 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  gnp0t_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true
}.


#[using="Type"] Lemma gnp0t_setup : forall regs m CA CLS cnt sz cp SB st s0o, gnp0t_pre regs m CA CLS cnt sz cp SB st s0o ->
  regs_ok (Ez regs (VALS_gnp0t CA CLS cnt sz cp SB st s0o)) AXF_gnp0t.sr_gnp0t regs /\ know_ok SEGS (Ez regs (VALS_gnp0t CA CLS cnt sz cp SB st s0o)) m AXF_gnp0t.kn_gnp0t.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS cnt sz cp SB st s0o P. destruct P as [gnp0t_R8 gnp0t_R10 gnp0t_R11 gnp0t_R13 gnp0t_HSTK gnp0t_rng_CA gnp0t_rng_CLS gnp0t_rng_cnt gnp0t_rng_sz gnp0t_rng_cp gnp0t_rng_SB gnp0t_rng_st gnp0t_rng_s0o gnp0t_ka1 gnp0t_kr3 gnp0t_kw4 gnp0t_kw5 gnp0t_kw6 gnp0t_kw7 gnp0t_kw8 gnp0t_kw9 gnp0t_kw10 gnp0t_kwr11 gnp0t_kw12 gnp0t_kw13 gnp0t_kw14 gnp0t_kw15 gnp0t_kwr16].
  set (E := Ez regs (VALS_gnp0t CA CLS cnt sz cp SB st s0o)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0o) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z1 : bv_unsigned (ev E 1) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) by reflexivity.
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (Z9 : bv_unsigned (ev E 9) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) by reflexivity.
  assert (Z18 : bv_unsigned (ev E 18) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) by reflexivity.
  assert (Z19 : bv_unsigned (ev E 19) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) by reflexivity.
  assert (Z20 : bv_unsigned (ev E 20) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) by reflexivity.
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 cnt + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_gnp0t.sr_gnp0t.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite gnp0t_R8. reflexivity.
    - rewrite gnp0t_R10. reflexivity.
    - rewrite gnp0t_R11. reflexivity.
    - rewrite gnp0t_R13. reflexivity. }
  unfold know_ok, AXF_gnp0t.kn_gnp0t.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gnp0t.e_CA AXF_gnp0t.e_CLS AXF_gnp0t.e_cnt AXF_gnp0t.e_sz AXF_gnp0t.e_cp AXF_gnp0t.e_SB AXF_gnp0t.e_st AXF_gnp0t.e_s0o AXF_gnp0t.REC AXF_gnp0t.CHP AXF_gnp0t.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z1, ?Z2, ?Z9, ?Z18, ?Z19, ?Z20.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gnp0t_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gnp0t_rng_CLS eq_refl eq_refl), ?(mod64_of_range cnt _ _ gnp0t_rng_cnt eq_refl eq_refl), ?(mod64_of_range cp _ _ gnp0t_rng_cp eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gnp0t_kwr11 | apply gnp0t_kwr16]; assumption).
  all: try (clear - gnp0t_rng_CA gnp0t_rng_CLS gnp0t_rng_cnt gnp0t_rng_sz gnp0t_rng_cp gnp0t_rng_SB gnp0t_rng_st gnp0t_rng_s0o gnp0t_ka1 gnp0t_kr3 HP; lia).
  all: first [lia].
Qed.


Definition gnp0t_mem_pnp0tp (m : word -> option byte) (regs : bvmap 5 word) (CA CLS cnt sz cp SB st s0o : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (CA + (80 * CLS) + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 cnt + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))).

#[using="Type"] Theorem gnp0t_pnp0tp : forall regs m rom CA CLS cnt sz cp SB st s0o, gnp0t_pre regs m CA CLS cnt sz cp SB st s0o ->
  scs_denot SEGS m (Ez regs (VALS_gnp0t CA CLS cnt sz cp SB st s0o)) (snd (fst AXF_gnp0t.RES_pnp0tp)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43e7c) m rom) (mkst R (wa 0x43f08) (gnp0t_mem_pnp0tp m regs CA CLS cnt sz cp SB st s0o) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48) /\ getr R 8 = wa s0o /\ getr R 10 = wa ((4294967296 * CLS) + (SB + (16 * ext_Z false 0 4 cp))) /\ getr R 11 = wa 9 /\ getr R 12 = wa sz /\ getr R 13 = wa 8 /\ getr R 14 = wa (16 * ext_Z false 0 4 cp) /\ (forall k, In k [1; 3; 4; 5; 6; 7; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS cnt sz cp SB st s0o P Hsc. destruct (gnp0t_setup regs m CA CLS cnt sz cp SB st s0o P) as [HR HK].
  set (E := Ez regs (VALS_gnp0t CA CLS cnt sz cp SB st s0o)) in *. destruct P as [gnp0t_R8 gnp0t_R10 gnp0t_R11 gnp0t_R13 gnp0t_HSTK gnp0t_rng_CA gnp0t_rng_CLS gnp0t_rng_cnt gnp0t_rng_sz gnp0t_rng_cp gnp0t_rng_SB gnp0t_rng_st gnp0t_rng_s0o gnp0t_ka1 gnp0t_kr3 gnp0t_kw4 gnp0t_kw5 gnp0t_kw6 gnp0t_kw7 gnp0t_kw8 gnp0t_kw9 gnp0t_kw10 gnp0t_kwr11 gnp0t_kw12 gnp0t_kw13 gnp0t_kw14 gnp0t_kw15 gnp0t_kwr16].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0o) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z1 : bv_unsigned (ev E 1) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) by reflexivity.
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (Z9 : bv_unsigned (ev E 9) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) by reflexivity.
  assert (Z18 : bv_unsigned (ev E 18) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) by reflexivity.
  assert (Z19 : bv_unsigned (ev E 19) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) by reflexivity.
  assert (Z20 : bv_unsigned (ev E 20) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) by reflexivity.
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 cnt + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 80 [0x43f08; 0x43f94] AXF_gnp0t.scr_pnp0tp 0x43e7c AXF_gnp0t.sr_gnp0t AXF_gnp0t.kn_gnp0t 40 _ _ _ E m rom regs AXF_gnp0t.RES_pnp0tp_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gnp0t.RES_pnp0tp fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gnp0t_mem_pnp0tp m regs CA CLS cnt sz cp SB st s0o) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gnp0t_mem_pnp0tp. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNP0T.
End AXF_gnp0tz.


Module AXF_gnp0rt.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_cnt := EVar 34.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition sr_gnp0rt := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_CLS)) 10 (ELit 923480)) 11 (e_CA)) 13 (ELit 8)).
Definition kn_gnp0rt : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 0) 4 e_cnt ].
Definition scr_gnp0rt : scripts := SCR [true] [] [].
Definition ss_gnp0rt := SS 0x43e7c sr_gnp0rt [] kn_gnp0rt 35.
Definition RUN_gnp0rt := sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_gnp0rt ss_gnp0rt [].

Definition scr_pnp0rt : scripts := SCR [true] [] [].
Definition RES_pnp0rt := Eval vm_compute in sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0rt ss_gnp0rt [].
Lemma RES_pnp0rt_ok : sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0rt (SS 0x43e7c sr_gnp0rt [] kn_gnp0rt 35) [] = RES_pnp0rt.
Proof. vm_compute. reflexivity. Qed.
End AXF_gnp0rt.


Module AXF_gnp0rtz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNP0RT.
Context {fx : FPState}.

Definition VALS_gnp0rt (CA CLS cnt : Z) : list Z := [CA; CLS; cnt].

Record gnp0rt_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS cnt : Z) : Prop := {
  gnp0rt_R8 : getr regs 8 = wa CLS ;
  gnp0rt_R10 : getr regs 10 = wa 923480 ;
  gnp0rt_R11 : getr regs 11 = wa CA ;
  gnp0rt_R13 : getr regs 13 = wa 8 ;
  gnp0rt_rng_CA : 1 <= CA <= 2^47 ;
  gnp0rt_rng_CLS : 1 <= CLS <= 30 ;
  gnp0rt_rng_cnt : 0 <= cnt <= 2^32-1 ;
  gnp0rt_ka1 : CA mod 16 = 0 ;
  gnp0rt_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gnp0rt_kw4 : rdn SEGS m (wa (CA + (80 * CLS) + 0)) 4 = Some (word_to_le_bytes 4 (wa cnt))
}.


#[using="Type"] Lemma gnp0rt_setup : forall regs m CA CLS cnt, gnp0rt_pre regs m CA CLS cnt ->
  regs_ok (Ez regs (VALS_gnp0rt CA CLS cnt)) AXF_gnp0rt.sr_gnp0rt regs /\ know_ok SEGS (Ez regs (VALS_gnp0rt CA CLS cnt)) m AXF_gnp0rt.kn_gnp0rt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS cnt P. destruct P as [gnp0rt_R8 gnp0rt_R10 gnp0rt_R11 gnp0rt_R13 gnp0rt_rng_CA gnp0rt_rng_CLS gnp0rt_rng_cnt gnp0rt_ka1 gnp0rt_kr3 gnp0rt_kw4].
  set (E := Ez regs (VALS_gnp0rt CA CLS cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gnp0rt.sr_gnp0rt.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite gnp0rt_R8. reflexivity.
    - rewrite gnp0rt_R10. reflexivity.
    - rewrite gnp0rt_R11. reflexivity.
    - rewrite gnp0rt_R13. reflexivity. }
  unfold know_ok, AXF_gnp0rt.kn_gnp0rt.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gnp0rt.e_CA AXF_gnp0rt.e_CLS AXF_gnp0rt.e_cnt AXF_gnp0rt.REC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gnp0rt_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gnp0rt_rng_CLS eq_refl eq_refl), ?(mod64_of_range cnt _ _ gnp0rt_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - gnp0rt_rng_CA gnp0rt_rng_CLS gnp0rt_rng_cnt gnp0rt_ka1 gnp0rt_kr3; lia).
  all: first [lia].
Qed.


Definition gnp0rt_mem_pnp0rt (m : word -> option byte) (regs : bvmap 5 word) (CA CLS cnt : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem gnp0rt_pnp0rt : forall regs m rom CA CLS cnt, gnp0rt_pre regs m CA CLS cnt ->
  scs_denot SEGS m (Ez regs (VALS_gnp0rt CA CLS cnt)) (snd (fst AXF_gnp0rt.RES_pnp0rt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43e7c) m rom) (mkst R (wa 0x43f94) (gnp0rt_mem_pnp0rt m regs CA CLS cnt) rom) /\
    getr R 8 = wa CLS /\ getr R 9 = wa (CA + (80 * CLS)) /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + (80 * CLS)) /\ getr R 12 = wa 923480 /\ getr R 13 = wa CLS /\ getr R 18 = wa 8 /\ getr R 19 = wa CA /\ getr R 20 = wa 923480 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS cnt P Hsc. destruct (gnp0rt_setup regs m CA CLS cnt P) as [HR HK].
  set (E := Ez regs (VALS_gnp0rt CA CLS cnt)) in *. destruct P as [gnp0rt_R8 gnp0rt_R10 gnp0rt_R11 gnp0rt_R13 gnp0rt_rng_CA gnp0rt_rng_CLS gnp0rt_rng_cnt gnp0rt_ka1 gnp0rt_kr3 gnp0rt_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 80 [0x43f08; 0x43f94] AXF_gnp0rt.scr_pnp0rt 0x43e7c AXF_gnp0rt.sr_gnp0rt AXF_gnp0rt.kn_gnp0rt 35 _ _ _ E m rom regs AXF_gnp0rt.RES_pnp0rt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gnp0rt.RES_pnp0rt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gnp0rt_mem_pnp0rt m regs CA CLS cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gnp0rt_mem_pnp0rt. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNP0RT.
End AXF_gnp0rtz.


Module AXF_gnpr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_mc := EVar 34.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition STK := SA (EVar 2) (-1024).
Definition sr_gnpr := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 923480)) 13 (e_CLS)).
Definition kn_gnpr : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 e_mc;
    KWr STK (ELit 1024) ].
Definition scr_gnpr : scripts := SCR [false] [] [].
Definition ss_gnpr := SS 0x43f94 sr_gnpr [] kn_gnpr 35.
Definition RUN_gnpr := sym_exec SEGS 40 true [0x44474] scr_gnpr ss_gnpr [].

Definition scr_pnpr : scripts := SCR [false] [] [].
Definition RES_pnpr := Eval vm_compute in sym_exec SEGS 40 true [0x44474] scr_pnpr ss_gnpr [].
Lemma RES_pnpr_ok : sym_exec SEGS 40 true [0x44474] scr_pnpr (SS 0x43f94 sr_gnpr [] kn_gnpr 35) [] = RES_pnpr.
Proof. vm_compute. reflexivity. Qed.
End AXF_gnpr.


Module AXF_gnprz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNPR.
Context {fx : FPState}.

Definition VALS_gnpr (CA CLS mc : Z) : list Z := [CA; CLS; mc].

Record gnpr_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS mc : Z) : Prop := {
  gnpr_R10 : getr regs 10 = wa CA ;
  gnpr_R11 : getr regs 11 = wa (CA + (80 * CLS)) ;
  gnpr_R12 : getr regs 12 = wa 923480 ;
  gnpr_R13 : getr regs 13 = wa CLS ;
  gnpr_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gnpr_rng_CA : 1 <= CA <= 2^47 ;
  gnpr_rng_CLS : 1 <= CLS <= 30 ;
  gnpr_rng_mc : 2 <= mc <= 16 ;
  gnpr_ka1 : CA mod 16 = 0 ;
  gnpr_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gnpr_kw4 : rdn SEGS m (wa (CA + (80 * CLS) + 4)) 4 = Some (word_to_le_bytes 4 (wa mc))
}.


#[using="Type"] Lemma gnpr_setup : forall regs m CA CLS mc, gnpr_pre regs m CA CLS mc ->
  regs_ok (Ez regs (VALS_gnpr CA CLS mc)) AXF_gnpr.sr_gnpr regs /\ know_ok SEGS (Ez regs (VALS_gnpr CA CLS mc)) m AXF_gnpr.kn_gnpr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS mc P. destruct P as [gnpr_R10 gnpr_R11 gnpr_R12 gnpr_R13 gnpr_HSTK gnpr_rng_CA gnpr_rng_CLS gnpr_rng_mc gnpr_ka1 gnpr_kr3 gnpr_kw4].
  set (E := Ez regs (VALS_gnpr CA CLS mc)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gnpr.sr_gnpr.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite gnpr_R10. reflexivity.
    - rewrite gnpr_R11, zeval_sound. cbn [zeval edenot AXF_gnpr.e_CA AXF_gnpr.e_CLS AXF_gnpr.e_mc AXF_gnpr.REC AXF_gnpr.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gnpr_R12. reflexivity.
    - rewrite gnpr_R13. reflexivity. }
  unfold know_ok, AXF_gnpr.kn_gnpr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gnpr.e_CA AXF_gnpr.e_CLS AXF_gnpr.e_mc AXF_gnpr.REC AXF_gnpr.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gnpr_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gnpr_rng_CLS eq_refl eq_refl), ?(mod64_of_range mc _ _ gnpr_rng_mc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - gnpr_rng_CA gnpr_rng_CLS gnpr_rng_mc gnpr_ka1 gnpr_kr3; lia).
  all: first [lia].
Qed.


Definition gnpr_mem_pnpr (m : word -> option byte) (regs : bvmap 5 word) (CA CLS mc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 278424))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))).

#[using="Type"] Theorem gnpr_pnpr : forall regs m rom CA CLS mc, gnpr_pre regs m CA CLS mc ->
  scs_denot SEGS m (Ez regs (VALS_gnpr CA CLS mc)) (snd (fst AXF_gnpr.RES_pnpr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43f94) m rom) (mkst R (wa 0x44474) (gnpr_mem_pnpr m regs CA CLS mc) rom) /\
    getr R 1 = wa 278424 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 8 = wa (CA + (80 * CLS)) /\ getr R 9 = wa (bv_unsigned (edenot (Ez regs (VALS_gnpr CA CLS mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ getr R 10 = wa 923480 /\ getr R 11 = wa (CA + 2560) /\ getr R 12 = wa CLS /\ getr R 13 = wa ((CA + (80 * CLS)) + 16) /\ getr R 14 = wa (bv_unsigned (edenot (Ez regs (VALS_gnpr CA CLS mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ (forall k, In k [3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS mc P Hsc. destruct (gnpr_setup regs m CA CLS mc P) as [HR HK].
  set (E := Ez regs (VALS_gnpr CA CLS mc)) in *. destruct P as [gnpr_R10 gnpr_R11 gnpr_R12 gnpr_R13 gnpr_HSTK gnpr_rng_CA gnpr_rng_CLS gnpr_rng_mc gnpr_ka1 gnpr_kr3 gnpr_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 40 [0x44474] AXF_gnpr.scr_pnpr 0x43f94 AXF_gnpr.sr_gnpr AXF_gnpr.kn_gnpr 35 _ _ _ E m rom regs AXF_gnpr.RES_pnpr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gnpr.RES_pnpr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gnpr_mem_pnpr m regs CA CLS mc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gnpr_mem_pnpr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNPR.
End AXF_gnprz.


Module AXF_gnri.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition STK := SA (EVar 2) (-1024).
Definition sr_gnri := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 923480)) 13 (e_CLS)).
Definition kn_gnri : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 (ELit 0);
    KWr (SA e_CA 84) (ELit 2488);
    KWr STK (ELit 1024) ].
Definition scr_gnri : scripts := SCR [] [] [].
Definition ss_gnri := SS 0x43f94 sr_gnri [] kn_gnri 34.
Definition RUN_gnri := sym_exec SEGS 900 true [0x44530] scr_gnri ss_gnri [].

Definition scr_pnri : scripts := SCR [] [] [].
Definition RES_pnri := Eval vm_compute in sym_exec SEGS 900 true [0x44530] scr_pnri ss_gnri [].
Lemma RES_pnri_ok : sym_exec SEGS 900 true [0x44530] scr_pnri (SS 0x43f94 sr_gnri [] kn_gnri 34) [] = RES_pnri.
Proof. vm_compute. reflexivity. Qed.
End AXF_gnri.


Module AXF_gnriz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNRI.
Context {fx : FPState}.

Definition VALS_gnri (CA CLS : Z) : list Z := [CA; CLS].

Record gnri_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS : Z) : Prop := {
  gnri_R10 : getr regs 10 = wa CA ;
  gnri_R11 : getr regs 11 = wa (CA + (80 * CLS)) ;
  gnri_R12 : getr regs 12 = wa 923480 ;
  gnri_R13 : getr regs 13 = wa CLS ;
  gnri_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gnri_rng_CA : 1 <= CA <= 2^47 ;
  gnri_rng_CLS : 1 <= CLS <= 30 ;
  gnri_ka1 : CA mod 16 = 0 ;
  gnri_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gnri_kw4 : rdn SEGS m (wa (CA + (80 * CLS) + 4)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  gnri_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 2488 -> store_ok SEGS m (wa (CA + 84 + d)) k = true
}.


#[using="Type"] Lemma gnri_setup : forall regs m CA CLS, gnri_pre regs m CA CLS ->
  regs_ok (Ez regs (VALS_gnri CA CLS)) AXF_gnri.sr_gnri regs /\ know_ok SEGS (Ez regs (VALS_gnri CA CLS)) m AXF_gnri.kn_gnri.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS P. destruct P as [gnri_R10 gnri_R11 gnri_R12 gnri_R13 gnri_HSTK gnri_rng_CA gnri_rng_CLS gnri_ka1 gnri_kr3 gnri_kw4 gnri_kwr5].
  set (E := Ez regs (VALS_gnri CA CLS)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gnri.sr_gnri.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite gnri_R10. reflexivity.
    - rewrite gnri_R11, zeval_sound. cbn [zeval edenot AXF_gnri.e_CA AXF_gnri.e_CLS AXF_gnri.REC AXF_gnri.STK]. rewrite ?Z32, ?Z33, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gnri_R12. reflexivity.
    - rewrite gnri_R13. reflexivity. }
  unfold know_ok, AXF_gnri.kn_gnri.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gnri.e_CA AXF_gnri.e_CLS AXF_gnri.REC AXF_gnri.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gnri_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gnri_rng_CLS eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gnri_kwr5]; assumption).
  all: try (clear - gnri_rng_CA gnri_rng_CLS gnri_ka1 gnri_kr3; lia).
  all: first [lia].
Qed.


Definition gnri_mem_pnri (m : word -> option byte) (regs : bvmap 5 word) (CA CLS : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 278424))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (CA + 84)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 88)) (word_to_le_bytes 8 (wa 32))) (wa (CA + 164)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 168)) (word_to_le_bytes 8 (wa 64))) (wa (CA + 244)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 248)) (word_to_le_bytes 8 (wa 96))) (wa (CA + 324)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 328)) (word_to_le_bytes 8 (wa 128))) (wa (CA + 404)) (word_to_le_bytes 4 (wa 12))) (wa (CA + 408)) (word_to_le_bytes 8 (wa 160))) (wa (CA + 484)) (word_to_le_bytes 4 (wa 10))) (wa (CA + 488)) (word_to_le_bytes 8 (wa 192))) (wa (CA + 564)) (word_to_le_bytes 4 (wa 8))) (wa (CA + 568)) (word_to_le_bytes 8 (wa 224))) (wa (CA + 644)) (word_to_le_bytes 4 (wa 8))) (wa (CA + 648)) (word_to_le_bytes 8 (wa 256))) (wa (CA + 724)) (word_to_le_bytes 4 (wa 6))) (wa (CA + 728)) (word_to_le_bytes 8 (wa 288))) (wa (CA + 804)) (word_to_le_bytes 4 (wa 6))) (wa (CA + 808)) (word_to_le_bytes 8 (wa 320))) (wa (CA + 884)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 888)) (word_to_le_bytes 8 (wa 352))) (wa (CA + 964)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 968)) (word_to_le_bytes 8 (wa 384))) (wa (CA + 1044)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1048)) (word_to_le_bytes 8 (wa 416))) (wa (CA + 1124)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1128)) (word_to_le_bytes 8 (wa 448))) (wa (CA + 1204)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1208)) (word_to_le_bytes 8 (wa 480))) (wa (CA + 1284)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1288)) (word_to_le_bytes 8 (wa 512))) (wa (CA + 1364)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1368)) (word_to_le_bytes 8 (wa 768))) (wa (CA + 1444)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1448)) (word_to_le_bytes 8 (wa 1024))) (wa (CA + 1524)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1528)) (word_to_le_bytes 8 (wa 1536))) (wa (CA + 1604)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1608)) (word_to_le_bytes 8 (wa 2048))) (wa (CA + 1684)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1688)) (word_to_le_bytes 8 (wa 3072))) (wa (CA + 1764)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1768)) (word_to_le_bytes 8 (wa 4096))) (wa (CA + 1844)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1848)) (word_to_le_bytes 8 (wa 6144))) (wa (CA + 1924)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1928)) (word_to_le_bytes 8 (wa 8192))) (wa (CA + 2004)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2008)) (word_to_le_bytes 8 (wa 12288))) (wa (CA + 2084)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2088)) (word_to_le_bytes 8 (wa 16384))) (wa (CA + 2164)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2168)) (word_to_le_bytes 8 (wa 24576))) (wa (CA + 2244)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2248)) (word_to_le_bytes 8 (wa 32768))) (wa (CA + 2324)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2328)) (word_to_le_bytes 8 (wa 49152))) (wa (CA + 2404)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2408)) (word_to_le_bytes 8 (wa 65536))) (wa (CA + 2484)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 2488)) (word_to_le_bytes 8 (wa 64)).

#[using="Type"] Theorem gnri_pnri : forall regs m rom CA CLS, gnri_pre regs m CA CLS ->
  scs_denot SEGS m (Ez regs (VALS_gnri CA CLS)) (snd (fst AXF_gnri.RES_pnri)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43f94) m rom) (mkst R (wa 0x44530) (gnri_mem_pnri m regs CA CLS) rom) /\
    getr R 1 = wa 278424 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 5 = wa 16 /\ getr R 6 = wa 17 /\ getr R 7 = wa 512 /\ getr R 8 = wa (CA + (80 * CLS)) /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + 2568) /\ getr R 12 = wa 923480 /\ getr R 13 = wa 1024 /\ getr R 14 = wa CLS /\ getr R 15 = wa 16 /\ getr R 16 = wa 15 /\ getr R 17 = wa 1024 /\ getr R 28 = wa 64 /\ getr R 29 = wa 16 /\ getr R 30 = wa 0 /\ (forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS P Hsc. destruct (gnri_setup regs m CA CLS P) as [HR HK].
  set (E := Ez regs (VALS_gnri CA CLS)) in *. destruct P as [gnri_R10 gnri_R11 gnri_R12 gnri_R13 gnri_HSTK gnri_rng_CA gnri_rng_CLS gnri_ka1 gnri_kr3 gnri_kw4 gnri_kwr5].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 900 [0x44530] AXF_gnri.scr_pnri 0x43f94 AXF_gnri.sr_gnri AXF_gnri.kn_gnri 34 _ _ _ E m rom regs AXF_gnri.RES_pnri_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gnri.RES_pnri fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gnri_mem_pnri m regs CA CLS) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gnri_mem_pnri. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNRI.
End AXF_gnriz.


Module AXF_gnri2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_mc := EVar 34.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition sr_gnri2 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (REC)) 10 (e_CA)) 12 (ELit 923480)) 14 (e_CLS)).
Definition kn_gnri2 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KWord (SA REC 4) 4 e_mc ].
Definition scr_gnri2 : scripts := SCR [] [] [].
Definition ss_gnri2 := SS 0x44530 sr_gnri2 [] kn_gnri2 35.
Definition RUN_gnri2 := sym_exec SEGS 40 true [0x44474] scr_gnri2 ss_gnri2 [].

Definition scr_pnri2 : scripts := SCR [] [] [].
Definition RES_pnri2 := Eval vm_compute in sym_exec SEGS 40 true [0x44474] scr_pnri2 ss_gnri2 [].
Lemma RES_pnri2_ok : sym_exec SEGS 40 true [0x44474] scr_pnri2 (SS 0x44530 sr_gnri2 [] kn_gnri2 35) [] = RES_pnri2.
Proof. vm_compute. reflexivity. Qed.
End AXF_gnri2.


Module AXF_gnri2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNRI2.
Context {fx : FPState}.

Definition VALS_gnri2 (CA CLS mc : Z) : list Z := [CA; CLS; mc].

Record gnri2_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS mc : Z) : Prop := {
  gnri2_R8 : getr regs 8 = wa (CA + (80 * CLS)) ;
  gnri2_R10 : getr regs 10 = wa CA ;
  gnri2_R12 : getr regs 12 = wa 923480 ;
  gnri2_R14 : getr regs 14 = wa CLS ;
  gnri2_rng_CA : 1 <= CA <= 2^47 ;
  gnri2_rng_CLS : 1 <= CLS <= 30 ;
  gnri2_rng_mc : 2 <= mc <= 16 ;
  gnri2_ka1 : CA mod 16 = 0 ;
  gnri2_kw3 : rdn SEGS m (wa (CA + (80 * CLS) + 4)) 4 = Some (word_to_le_bytes 4 (wa mc))
}.


#[using="Type"] Lemma gnri2_setup : forall regs m CA CLS mc, gnri2_pre regs m CA CLS mc ->
  regs_ok (Ez regs (VALS_gnri2 CA CLS mc)) AXF_gnri2.sr_gnri2 regs /\ know_ok SEGS (Ez regs (VALS_gnri2 CA CLS mc)) m AXF_gnri2.kn_gnri2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS mc P. destruct P as [gnri2_R8 gnri2_R10 gnri2_R12 gnri2_R14 gnri2_rng_CA gnri2_rng_CLS gnri2_rng_mc gnri2_ka1 gnri2_kw3].
  set (E := Ez regs (VALS_gnri2 CA CLS mc)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_gnri2.sr_gnri2.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite gnri2_R8, zeval_sound. cbn [zeval edenot AXF_gnri2.e_CA AXF_gnri2.e_CLS AXF_gnri2.e_mc AXF_gnri2.REC]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gnri2_R10. reflexivity.
    - rewrite gnri2_R12. reflexivity.
    - rewrite gnri2_R14. reflexivity. }
  unfold know_ok, AXF_gnri2.kn_gnri2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gnri2.e_CA AXF_gnri2.e_CLS AXF_gnri2.e_mc AXF_gnri2.REC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gnri2_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gnri2_rng_CLS eq_refl eq_refl), ?(mod64_of_range mc _ _ gnri2_rng_mc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - gnri2_rng_CA gnri2_rng_CLS gnri2_rng_mc gnri2_ka1; lia).
  all: first [lia].
Qed.


Definition gnri2_mem_pnri2 (m : word -> option byte) (regs : bvmap 5 word) (CA CLS mc : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem gnri2_pnri2 : forall regs m rom CA CLS mc, gnri2_pre regs m CA CLS mc ->
  scs_denot SEGS m (Ez regs (VALS_gnri2 CA CLS mc)) (snd (fst AXF_gnri2.RES_pnri2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44530) m rom) (mkst R (wa 0x44474) (gnri2_mem_pnri2 m regs CA CLS mc) rom) /\
    getr R 8 = wa (CA + (80 * CLS)) /\ getr R 9 = wa (bv_unsigned (edenot (Ez regs (VALS_gnri2 CA CLS mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ getr R 10 = wa 923480 /\ getr R 11 = wa (CA + 2560) /\ getr R 12 = wa CLS /\ getr R 13 = wa ((CA + (80 * CLS)) + 16) /\ getr R 14 = wa (bv_unsigned (edenot (Ez regs (VALS_gnri2 CA CLS mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS mc P Hsc. destruct (gnri2_setup regs m CA CLS mc P) as [HR HK].
  set (E := Ez regs (VALS_gnri2 CA CLS mc)) in *. destruct P as [gnri2_R8 gnri2_R10 gnri2_R12 gnri2_R14 gnri2_rng_CA gnri2_rng_CLS gnri2_rng_mc gnri2_ka1 gnri2_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 40 [0x44474] AXF_gnri2.scr_pnri2 0x44530 AXF_gnri2.sr_gnri2 AXF_gnri2.kn_gnri2 35 _ _ _ E m rom regs AXF_gnri2.RES_pnri2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gnri2.RES_pnri2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gnri2_mem_pnri2 m regs CA CLS mc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gnri2_mem_pnri2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNRI2.
End AXF_gnri2z.


Module AXF_gng0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition e_nf := EVar 37.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition RI := EAlu ALU_ADD (EMd M_MUL (ELit 128) e_CLS) e_RIB.
Definition STK := SA (EVar 2) (-1024).
Definition sr_gng0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (EAlu ALU_ADD e_CA (ELit 2560))) 12 (e_CLS)) 13 (EAlu ALU_ADD REC (ELit 16))) 14 (e_n)).
Definition kn_gng0 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 30;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA (ELit 0) 923528) 8 e_RIB;
    KWord (SA RI 0) 8 (ELit 0);
    KWr (SA RI 0) (ELit 8);
    KWord (SA RI 16) 8 e_nf;
    KWr (SA RI 16) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_gng0 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition ss_gng0 := SS 0x44474 sr_gng0 [] kn_gng0 38.
Definition RUN_gng0 := sym_exec SEGS 60 true [0x446ac; 0x446c0] scr_gng0 ss_gng0 [].

Definition scr_png0 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition RES_png0 := Eval vm_compute in sym_exec SEGS 60 true [0x446ac; 0x446c0] scr_png0 ss_gng0 [].
Lemma RES_png0_ok : sym_exec SEGS 60 true [0x446ac; 0x446c0] scr_png0 (SS 0x44474 sr_gng0 [] kn_gng0 38) [] = RES_png0.
Proof. vm_compute. reflexivity. Qed.
End AXF_gng0.


Module AXF_gng0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNG0.
Context {fx : FPState}.

Definition VALS_gng0 (CA CLS n SB RIB nf : Z) : list Z := [CA; CLS; n; SB; RIB; nf].

Record gng0_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS n SB RIB nf : Z) : Prop := {
  gng0_R10 : getr regs 10 = wa 923480 ;
  gng0_R11 : getr regs 11 = wa (CA + 2560) ;
  gng0_R12 : getr regs 12 = wa CLS ;
  gng0_R13 : getr regs 13 = wa ((CA + (80 * CLS)) + 16) ;
  gng0_R14 : getr regs 14 = wa n ;
  gng0_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gng0_rng_CA : 1 <= CA <= 2^47 ;
  gng0_rng_CLS : 1 <= CLS <= 30 ;
  gng0_rng_n : 1 <= n <= 8 ;
  gng0_rng_SB : 0 <= SB <= 2^64-1 ;
  gng0_rng_RIB : 1 <= RIB <= 2^47 ;
  gng0_rng_nf : 0 <= nf <= 2^64-1 ;
  gng0_ka1 : CA mod 16 = 0 ;
  gng0_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gng0_ka5 : RIB mod 128 = 0 ;
  gng0_kw6 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  gng0_kw7 : rdn SEGS m (wa (0 + 923528)) 8 = Some (word_to_le_bytes 8 (wa RIB)) ;
  gng0_kw8 : rdn SEGS m (wa ((128 * CLS) + RIB + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa ((128 * CLS) + RIB + 0 + d)) k = true ;
  gng0_kw10 : rdn SEGS m (wa ((128 * CLS) + RIB + 16)) 8 = Some (word_to_le_bytes 8 (wa nf)) ;
  gng0_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa ((128 * CLS) + RIB + 16 + d)) k = true
}.


#[using="Type"] Lemma gng0_setup : forall regs m CA CLS n SB RIB nf, gng0_pre regs m CA CLS n SB RIB nf ->
  regs_ok (Ez regs (VALS_gng0 CA CLS n SB RIB nf)) AXF_gng0.sr_gng0 regs /\ know_ok SEGS (Ez regs (VALS_gng0 CA CLS n SB RIB nf)) m AXF_gng0.kn_gng0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS n SB RIB nf P. destruct P as [gng0_R10 gng0_R11 gng0_R12 gng0_R13 gng0_R14 gng0_HSTK gng0_rng_CA gng0_rng_CLS gng0_rng_n gng0_rng_SB gng0_rng_RIB gng0_rng_nf gng0_ka1 gng0_kr3 gng0_ka5 gng0_kw6 gng0_kw7 gng0_kw8 gng0_kwr9 gng0_kw10 gng0_kwr11].
  set (E := Ez regs (VALS_gng0 CA CLS n SB RIB nf)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gng0.sr_gng0.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite gng0_R10. reflexivity.
    - rewrite gng0_R11, zeval_sound. cbn [zeval edenot AXF_gng0.e_CA AXF_gng0.e_CLS AXF_gng0.e_n AXF_gng0.e_SB AXF_gng0.e_RIB AXF_gng0.e_nf AXF_gng0.REC AXF_gng0.RI AXF_gng0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gng0_R12. reflexivity.
    - rewrite gng0_R13, zeval_sound. cbn [zeval edenot AXF_gng0.e_CA AXF_gng0.e_CLS AXF_gng0.e_n AXF_gng0.e_SB AXF_gng0.e_RIB AXF_gng0.e_nf AXF_gng0.REC AXF_gng0.RI AXF_gng0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gng0_R14. reflexivity. }
  unfold know_ok, AXF_gng0.kn_gng0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gng0.e_CA AXF_gng0.e_CLS AXF_gng0.e_n AXF_gng0.e_SB AXF_gng0.e_RIB AXF_gng0.e_nf AXF_gng0.REC AXF_gng0.RI AXF_gng0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gng0_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gng0_rng_CLS eq_refl eq_refl), ?(mod64_of_range n _ _ gng0_rng_n eq_refl eq_refl), ?(mod64_of_range RIB _ _ gng0_rng_RIB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gng0_kwr9 | apply gng0_kwr11]; assumption).
  all: try (clear - gng0_rng_CA gng0_rng_CLS gng0_rng_n gng0_rng_SB gng0_rng_RIB gng0_rng_nf gng0_ka1 gng0_kr3 gng0_ka5; lia).
  all: first [lia].
Qed.


Definition gng0_mem_png0 (m : word -> option byte) (regs : bvmap 5 word) (CA CLS n SB RIB nf : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 279672))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))) (wa ((128 * CLS) + RIB + 0)) (word_to_le_bytes 8 (wa 1152921504606846976))) (wa ((128 * CLS) + RIB + 16)) (word_to_le_bytes 8 (wa ((-1 * n) + nf))).

#[using="Type"] Theorem gng0_png0 : forall regs m rom CA CLS n SB RIB nf, gng0_pre regs m CA CLS n SB RIB nf ->
  scs_denot SEGS m (Ez regs (VALS_gng0 CA CLS n SB RIB nf)) (snd (fst AXF_gng0.RES_png0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44474) m rom) (mkst R (wa 0x446ac) (gng0_mem_png0 m regs CA CLS n SB RIB nf) rom) /\
    getr R 1 = wa 279672 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128) /\ getr R 5 = wa 0 /\ getr R 6 = wa 1152921504606846976 /\ getr R 7 = wa 0 /\ getr R 8 = wa ((128 * CLS) + RIB) /\ getr R 9 = wa 923480 /\ getr R 10 = wa (((128 * CLS) + RIB) + 8) /\ getr R 11 = wa ((CA + ((80 * CLS) + (4 * n))) + 16) /\ getr R 12 = wa CLS /\ getr R 13 = wa ((CA + (80 * CLS)) + 16) /\ getr R 14 = wa n /\ getr R 15 = wa ((-4 * n) + (4 * nf)) /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 19 = wa 2305843009213693952 /\ getr R 20 = wa (((4294967296 * CLS) + ((-4 * n) + (SB + (4 * nf)))) + 3758096384) /\ getr R 21 = wa 1099511627776 /\ getr R 22 = wa 1152921504607895551 /\ getr R 23 = wa 1152921504606846976 /\ getr R 24 = wa 1500 /\ getr R 25 = wa 16140901064495857663 /\ (forall k, In k [3; 4; 18; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS n SB RIB nf P Hsc. destruct (gng0_setup regs m CA CLS n SB RIB nf P) as [HR HK].
  set (E := Ez regs (VALS_gng0 CA CLS n SB RIB nf)) in *. destruct P as [gng0_R10 gng0_R11 gng0_R12 gng0_R13 gng0_R14 gng0_HSTK gng0_rng_CA gng0_rng_CLS gng0_rng_n gng0_rng_SB gng0_rng_RIB gng0_rng_nf gng0_ka1 gng0_kr3 gng0_ka5 gng0_kw6 gng0_kw7 gng0_kw8 gng0_kwr9 gng0_kw10 gng0_kwr11].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 60 [0x446ac; 0x446c0] AXF_gng0.scr_png0 0x44474 AXF_gng0.sr_gng0 AXF_gng0.kn_gng0 38 _ _ _ E m rom regs AXF_gng0.RES_png0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gng0.RES_png0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gng0_mem_png0 m regs CA CLS n SB RIB nf) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gng0_mem_png0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNG0.
End AXF_gng0z.


Module AXF_gng0ps.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition RI := EAlu ALU_ADD (EMd M_MUL (ELit 128) e_CLS) e_RIB.
Definition STK := SA (EVar 2) (-1024).
Definition sr_gng0ps := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (EAlu ALU_ADD e_CA (ELit 2560))) 12 (e_CLS)) 13 (EAlu ALU_ADD REC (ELit 16))) 14 (e_n)).
Definition kn_gng0ps : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 1 16;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KRange e_SB 1 (2^47);
    KAlign e_SB 4096;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA (ELit 0) 923528) 8 e_RIB;
    KWord (SA (ELit 0) 923520) 4 (ELit 4294967295);
    KWord (SA (ELit 0) 923536) 1 (ELit 0);
    KWord (SA RI 0) 8 (ELit 0);
    KWr (SA RI 0) (ELit 8);
    KWord (SA RI 16) 8 (ELit 0);
    KWord (SA RI 32) 8 (ELit 0);
    KWord (SA RI 48) 8 (ELit 0);
    KWord (SA RI 56) 8 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_gng0ps : scripts := SCR [true; true; false] [] [].
Definition ss_gng0ps := SS 0x44474 sr_gng0ps [] kn_gng0ps 37.
Definition RUN_gng0ps := sym_exec SEGS 200 true [0x7db90] scr_gng0ps ss_gng0ps [].

Definition scr_png0ps : scripts := SCR [true; true; false] [] [].
Definition RES_png0ps := Eval vm_compute in sym_exec SEGS 200 true [0x7db90] scr_png0ps ss_gng0ps [].
Lemma RES_png0ps_ok : sym_exec SEGS 200 true [0x7db90] scr_png0ps (SS 0x44474 sr_gng0ps [] kn_gng0ps 37) [] = RES_png0ps.
Proof. vm_compute. reflexivity. Qed.
End AXF_gng0ps.


Module AXF_gng0psz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNG0PS.
Context {fx : FPState}.

Definition VALS_gng0ps (CA CLS n SB RIB : Z) : list Z := [CA; CLS; n; SB; RIB].

Record gng0ps_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS n SB RIB : Z) : Prop := {
  gng0ps_R10 : getr regs 10 = wa 923480 ;
  gng0ps_R11 : getr regs 11 = wa (CA + 2560) ;
  gng0ps_R12 : getr regs 12 = wa CLS ;
  gng0ps_R13 : getr regs 13 = wa ((CA + (80 * CLS)) + 16) ;
  gng0ps_R14 : getr regs 14 = wa n ;
  gng0ps_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gng0ps_rng_CA : 1 <= CA <= 2^47 ;
  gng0ps_rng_CLS : 1 <= CLS <= 16 ;
  gng0ps_rng_n : 1 <= n <= 8 ;
  gng0ps_rng_SB : 1 <= SB <= 2^47 ;
  gng0ps_rng_RIB : 1 <= RIB <= 2^47 ;
  gng0ps_ka1 : CA mod 16 = 0 ;
  gng0ps_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gng0ps_ka5 : RIB mod 128 = 0 ;
  gng0ps_ka7 : SB mod 4096 = 0 ;
  gng0ps_kw8 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  gng0ps_kw9 : rdn SEGS m (wa (0 + 923528)) 8 = Some (word_to_le_bytes 8 (wa RIB)) ;
  gng0ps_kw10 : rdn SEGS m (wa (0 + 923520)) 4 = Some (word_to_le_bytes 4 (wa 4294967295)) ;
  gng0ps_kw11 : rdn SEGS m (wa (0 + 923536)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  gng0ps_kw12 : rdn SEGS m (wa ((128 * CLS) + RIB + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0ps_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa ((128 * CLS) + RIB + 0 + d)) k = true ;
  gng0ps_kw14 : rdn SEGS m (wa ((128 * CLS) + RIB + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0ps_kw15 : rdn SEGS m (wa ((128 * CLS) + RIB + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0ps_kw16 : rdn SEGS m (wa ((128 * CLS) + RIB + 48)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0ps_kw17 : rdn SEGS m (wa ((128 * CLS) + RIB + 56)) 8 = Some (word_to_le_bytes 8 (wa 0))
}.


#[using="Type"] Lemma gng0ps_setup : forall regs m CA CLS n SB RIB, gng0ps_pre regs m CA CLS n SB RIB ->
  regs_ok (Ez regs (VALS_gng0ps CA CLS n SB RIB)) AXF_gng0ps.sr_gng0ps regs /\ know_ok SEGS (Ez regs (VALS_gng0ps CA CLS n SB RIB)) m AXF_gng0ps.kn_gng0ps.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS n SB RIB P. destruct P as [gng0ps_R10 gng0ps_R11 gng0ps_R12 gng0ps_R13 gng0ps_R14 gng0ps_HSTK gng0ps_rng_CA gng0ps_rng_CLS gng0ps_rng_n gng0ps_rng_SB gng0ps_rng_RIB gng0ps_ka1 gng0ps_kr3 gng0ps_ka5 gng0ps_ka7 gng0ps_kw8 gng0ps_kw9 gng0ps_kw10 gng0ps_kw11 gng0ps_kw12 gng0ps_kwr13 gng0ps_kw14 gng0ps_kw15 gng0ps_kw16 gng0ps_kw17].
  set (E := Ez regs (VALS_gng0ps CA CLS n SB RIB)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gng0ps.sr_gng0ps.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite gng0ps_R10. reflexivity.
    - rewrite gng0ps_R11, zeval_sound. cbn [zeval edenot AXF_gng0ps.e_CA AXF_gng0ps.e_CLS AXF_gng0ps.e_n AXF_gng0ps.e_SB AXF_gng0ps.e_RIB AXF_gng0ps.REC AXF_gng0ps.RI AXF_gng0ps.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gng0ps_R12. reflexivity.
    - rewrite gng0ps_R13, zeval_sound. cbn [zeval edenot AXF_gng0ps.e_CA AXF_gng0ps.e_CLS AXF_gng0ps.e_n AXF_gng0ps.e_SB AXF_gng0ps.e_RIB AXF_gng0ps.REC AXF_gng0ps.RI AXF_gng0ps.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gng0ps_R14. reflexivity. }
  unfold know_ok, AXF_gng0ps.kn_gng0ps.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gng0ps.e_CA AXF_gng0ps.e_CLS AXF_gng0ps.e_n AXF_gng0ps.e_SB AXF_gng0ps.e_RIB AXF_gng0ps.REC AXF_gng0ps.RI AXF_gng0ps.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gng0ps_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gng0ps_rng_CLS eq_refl eq_refl), ?(mod64_of_range n _ _ gng0ps_rng_n eq_refl eq_refl), ?(mod64_of_range SB _ _ gng0ps_rng_SB eq_refl eq_refl), ?(mod64_of_range RIB _ _ gng0ps_rng_RIB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gng0ps_kwr13]; assumption).
  all: try (clear - gng0ps_rng_CA gng0ps_rng_CLS gng0ps_rng_n gng0ps_rng_SB gng0ps_rng_RIB gng0ps_ka1 gng0ps_kr3 gng0ps_ka5 gng0ps_ka7; lia).
  all: first [lia].
Qed.


Definition gng0ps_mem_png0ps (m : word -> option byte) (regs : bvmap 5 word) (CA CLS n SB RIB : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 279672))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))) (wa ((128 * CLS) + RIB + 0)) (word_to_le_bytes 8 (wa 1152921504606846976))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -136)) (word_to_le_bytes 8 (wa 280564))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -144)) (word_to_le_bytes 8 (wa ((128 * CLS) + RIB)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -152)) (word_to_le_bytes 8 (wa 923480))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -160)) (word_to_le_bytes 8 (wa (((128 * CLS) + RIB) + 8)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -168)) (word_to_le_bytes 8 (wa 2305843009213693952))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -176)) (word_to_le_bytes 8 (wa (((4294967296 * CLS) + SB) + 3758096384)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -184)) (word_to_le_bytes 8 (wa ((CA + (80 * CLS)) + 16)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -192)) (word_to_le_bytes 8 (wa n)).

#[using="Type"] Theorem gng0ps_png0ps : forall regs m rom CA CLS n SB RIB, gng0ps_pre regs m CA CLS n SB RIB ->
  scs_denot SEGS m (Ez regs (VALS_gng0ps CA CLS n SB RIB)) (snd (fst AXF_gng0ps.RES_png0ps)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44474) m rom) (mkst R (wa 0x7db90) (gng0ps_mem_png0ps m regs CA CLS n SB RIB) rom) /\
    getr R 1 = wa 280928 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -192) /\ getr R 5 = wa 0 /\ getr R 6 = wa 1152921504606846976 /\ getr R 7 = wa 0 /\ getr R 8 = wa ((128 * CLS) + RIB) /\ getr R 9 = wa (CA + 2560) /\ getr R 10 = wa 923480 /\ getr R 11 = wa ((4294967296 * CLS) + SB) /\ getr R 12 = wa ((262144 * Z.shiftr (((((32 * CLS) * n) + -1)) mod 2^64) 18) + 262144) /\ getr R 13 = wa 96458 /\ getr R 14 = wa n /\ getr R 15 = wa 0 /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 18 = wa ((4294967296 * CLS) + SB) /\ getr R 19 = wa ((262144 * Z.shiftr (((((32 * CLS) * n) + -1)) mod 2^64) 18) + 262144) /\ getr R 20 = wa ((4294967296 * CLS) + SB) /\ getr R 21 = wa (32 * CLS) /\ getr R 22 = wa 923480 /\ getr R 23 = wa 1152921504606846976 /\ getr R 24 = wa 1500 /\ getr R 25 = wa 16140901064495857663 /\ (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS n SB RIB P Hsc. destruct (gng0ps_setup regs m CA CLS n SB RIB P) as [HR HK].
  set (E := Ez regs (VALS_gng0ps CA CLS n SB RIB)) in *. destruct P as [gng0ps_R10 gng0ps_R11 gng0ps_R12 gng0ps_R13 gng0ps_R14 gng0ps_HSTK gng0ps_rng_CA gng0ps_rng_CLS gng0ps_rng_n gng0ps_rng_SB gng0ps_rng_RIB gng0ps_ka1 gng0ps_kr3 gng0ps_ka5 gng0ps_ka7 gng0ps_kw8 gng0ps_kw9 gng0ps_kw10 gng0ps_kw11 gng0ps_kw12 gng0ps_kwr13 gng0ps_kw14 gng0ps_kw15 gng0ps_kw16 gng0ps_kw17].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 200 [0x7db90] AXF_gng0ps.scr_png0ps 0x44474 AXF_gng0ps.sr_gng0ps AXF_gng0ps.kn_gng0ps 37 _ _ _ E m rom regs AXF_gng0ps.RES_png0ps_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gng0ps.RES_png0ps fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gng0ps_mem_png0ps m regs CA CLS n SB RIB) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gng0ps_mem_png0ps. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNG0PS.
End AXF_gng0psz.


Module AXF_gng0pb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_CLS := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) e_CLS).
Definition RI := EAlu ALU_ADD (EMd M_MUL (ELit 128) e_CLS) e_RIB.
Definition STK := SA (EVar 2) (-1024).
Definition sr_gng0pb := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (EAlu ALU_ADD e_CA (ELit 2560))) 12 (e_CLS)) 13 (EAlu ALU_ADD REC (ELit 16))) 14 (ELit 1)).
Definition kn_gng0pb : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_CLS 17 30;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KRange e_SB 1 (2^47);
    KAlign e_SB 4096;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA (ELit 0) 923528) 8 e_RIB;
    KWord (SA (ELit 0) 923520) 4 (ELit 4294967295);
    KWord (SA (ELit 0) 923536) 1 (ELit 0);
    KWord (SA RI 0) 8 (ELit 0);
    KWr (SA RI 0) (ELit 8);
    KWord (SA RI 16) 8 (ELit 0);
    KWord (SA RI 32) 8 (ELit 0);
    KWord (SA RI 48) 8 (ELit 0);
    KWord (SA RI 56) 8 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_gng0pb : scripts := SCR [true; true; false] [] [].
Definition ss_gng0pb := SS 0x44474 sr_gng0pb [] kn_gng0pb 37.
Definition RUN_gng0pb := sym_exec SEGS 200 true [0x7db90] scr_gng0pb ss_gng0pb [].

Definition scr_png0pb : scripts := SCR [true; true; false] [] [].
Definition RES_png0pb := Eval vm_compute in sym_exec SEGS 200 true [0x7db90] scr_png0pb ss_gng0pb [].
Lemma RES_png0pb_ok : sym_exec SEGS 200 true [0x7db90] scr_png0pb (SS 0x44474 sr_gng0pb [] kn_gng0pb 37) [] = RES_png0pb.
Proof. vm_compute. reflexivity. Qed.
End AXF_gng0pb.


Module AXF_gng0pbz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GNG0PB.
Context {fx : FPState}.

Definition VALS_gng0pb (CA CLS n SB RIB : Z) : list Z := [CA; CLS; n; SB; RIB].

Record gng0pb_pre (regs : bvmap 5 word) (m : word -> option byte) (CA CLS n SB RIB : Z) : Prop := {
  gng0pb_R10 : getr regs 10 = wa 923480 ;
  gng0pb_R11 : getr regs 11 = wa (CA + 2560) ;
  gng0pb_R12 : getr regs 12 = wa CLS ;
  gng0pb_R13 : getr regs 13 = wa ((CA + (80 * CLS)) + 16) ;
  gng0pb_R14 : getr regs 14 = wa 1 ;
  gng0pb_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gng0pb_rng_CA : 1 <= CA <= 2^47 ;
  gng0pb_rng_CLS : 17 <= CLS <= 30 ;
  gng0pb_rng_n : 1 <= n <= 8 ;
  gng0pb_rng_SB : 1 <= SB <= 2^47 ;
  gng0pb_rng_RIB : 1 <= RIB <= 2^47 ;
  gng0pb_ka1 : CA mod 16 = 0 ;
  gng0pb_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gng0pb_ka5 : RIB mod 128 = 0 ;
  gng0pb_ka7 : SB mod 4096 = 0 ;
  gng0pb_kw8 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  gng0pb_kw9 : rdn SEGS m (wa (0 + 923528)) 8 = Some (word_to_le_bytes 8 (wa RIB)) ;
  gng0pb_kw10 : rdn SEGS m (wa (0 + 923520)) 4 = Some (word_to_le_bytes 4 (wa 4294967295)) ;
  gng0pb_kw11 : rdn SEGS m (wa (0 + 923536)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  gng0pb_kw12 : rdn SEGS m (wa ((128 * CLS) + RIB + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0pb_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa ((128 * CLS) + RIB + 0 + d)) k = true ;
  gng0pb_kw14 : rdn SEGS m (wa ((128 * CLS) + RIB + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0pb_kw15 : rdn SEGS m (wa ((128 * CLS) + RIB + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0pb_kw16 : rdn SEGS m (wa ((128 * CLS) + RIB + 48)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gng0pb_kw17 : rdn SEGS m (wa ((128 * CLS) + RIB + 56)) 8 = Some (word_to_le_bytes 8 (wa 0))
}.


#[using="Type"] Lemma gng0pb_setup : forall regs m CA CLS n SB RIB, gng0pb_pre regs m CA CLS n SB RIB ->
  regs_ok (Ez regs (VALS_gng0pb CA CLS n SB RIB)) AXF_gng0pb.sr_gng0pb regs /\ know_ok SEGS (Ez regs (VALS_gng0pb CA CLS n SB RIB)) m AXF_gng0pb.kn_gng0pb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA CLS n SB RIB P. destruct P as [gng0pb_R10 gng0pb_R11 gng0pb_R12 gng0pb_R13 gng0pb_R14 gng0pb_HSTK gng0pb_rng_CA gng0pb_rng_CLS gng0pb_rng_n gng0pb_rng_SB gng0pb_rng_RIB gng0pb_ka1 gng0pb_kr3 gng0pb_ka5 gng0pb_ka7 gng0pb_kw8 gng0pb_kw9 gng0pb_kw10 gng0pb_kw11 gng0pb_kw12 gng0pb_kwr13 gng0pb_kw14 gng0pb_kw15 gng0pb_kw16 gng0pb_kw17].
  set (E := Ez regs (VALS_gng0pb CA CLS n SB RIB)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gng0pb.sr_gng0pb.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite gng0pb_R10. reflexivity.
    - rewrite gng0pb_R11, zeval_sound. cbn [zeval edenot AXF_gng0pb.e_CA AXF_gng0pb.e_CLS AXF_gng0pb.e_n AXF_gng0pb.e_SB AXF_gng0pb.e_RIB AXF_gng0pb.REC AXF_gng0pb.RI AXF_gng0pb.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gng0pb_R12. reflexivity.
    - rewrite gng0pb_R13, zeval_sound. cbn [zeval edenot AXF_gng0pb.e_CA AXF_gng0pb.e_CLS AXF_gng0pb.e_n AXF_gng0pb.e_SB AXF_gng0pb.e_RIB AXF_gng0pb.REC AXF_gng0pb.RI AXF_gng0pb.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gng0pb_R14. reflexivity. }
  unfold know_ok, AXF_gng0pb.kn_gng0pb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gng0pb.e_CA AXF_gng0pb.e_CLS AXF_gng0pb.e_n AXF_gng0pb.e_SB AXF_gng0pb.e_RIB AXF_gng0pb.REC AXF_gng0pb.RI AXF_gng0pb.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gng0pb_rng_CA eq_refl eq_refl), ?(mod64_of_range CLS _ _ gng0pb_rng_CLS eq_refl eq_refl), ?(mod64_of_range n _ _ gng0pb_rng_n eq_refl eq_refl), ?(mod64_of_range SB _ _ gng0pb_rng_SB eq_refl eq_refl), ?(mod64_of_range RIB _ _ gng0pb_rng_RIB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gng0pb_kwr13]; assumption).
  all: try (clear - gng0pb_rng_CA gng0pb_rng_CLS gng0pb_rng_n gng0pb_rng_SB gng0pb_rng_RIB gng0pb_ka1 gng0pb_kr3 gng0pb_ka5 gng0pb_ka7; lia).
  all: first [lia].
Qed.


Definition gng0pb_mem_png0pb (m : word -> option byte) (regs : bvmap 5 word) (CA CLS n SB RIB : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 279672))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))) (wa ((128 * CLS) + RIB + 0)) (word_to_le_bytes 8 (wa 1152921504606846976))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -136)) (word_to_le_bytes 8 (wa 280564))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -144)) (word_to_le_bytes 8 (wa ((128 * CLS) + RIB)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -152)) (word_to_le_bytes 8 (wa 923480))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -160)) (word_to_le_bytes 8 (wa (((128 * CLS) + RIB) + 8)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -168)) (word_to_le_bytes 8 (wa 2305843009213693952))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -176)) (word_to_le_bytes 8 (wa (((4294967296 * CLS) + SB) + 3758096384)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -184)) (word_to_le_bytes 8 (wa ((CA + (80 * CLS)) + 16)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -192)) (word_to_le_bytes 8 (wa 1)).

#[using="Type"] Theorem gng0pb_png0pb : forall regs m rom CA CLS n SB RIB, gng0pb_pre regs m CA CLS n SB RIB ->
  scs_denot SEGS m (Ez regs (VALS_gng0pb CA CLS n SB RIB)) (snd (fst AXF_gng0pb.RES_png0pb)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44474) m rom) (mkst R (wa 0x7db90) (gng0pb_mem_png0pb m regs CA CLS n SB RIB) rom) /\
    getr R 1 = wa 280928 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -192) /\ getr R 5 = wa 0 /\ getr R 6 = wa 1152921504606846976 /\ getr R 7 = wa 0 /\ getr R 8 = wa ((128 * CLS) + RIB) /\ getr R 9 = wa (CA + 2560) /\ getr R 10 = wa 923480 /\ getr R 11 = wa ((4294967296 * CLS) + SB) /\ getr R 12 = wa 262144 /\ getr R 13 = wa 96458 /\ getr R 14 = wa 1 /\ getr R 15 = wa (bv_unsigned (edenot (Ez regs (VALS_gng0pb CA CLS n SB RIB)) (EAlu ALU_SRA (EMd M_MUL (ELit (-9223372036854775808)) (EVar 33)) (ELit 63)))) /\ getr R 16 = wa (-9223372036854775808 * CLS) /\ getr R 17 = wa 0 /\ getr R 18 = wa ((4294967296 * CLS) + SB) /\ getr R 19 = wa 262144 /\ getr R 20 = wa ((4294967296 * CLS) + SB) /\ getr R 21 = wa (bv_unsigned (edenot (Ez regs (VALS_gng0pb CA CLS n SB RIB)) (EAlu ALU_ADD (EAlu ALU_SLL (ELit 512) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-16))) (ELit 1))) (EAlu ALU_AND (EAlu ALU_SRA (EMd M_MUL (ELit (-9223372036854775808)) (EVar 33)) (ELit 63)) (EAlu ALU_SRL (EAlu ALU_SLL (ELit 512) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-16))) (ELit 1))) (ELit 1)))))) /\ getr R 22 = wa 923480 /\ getr R 23 = wa 1152921504606846976 /\ getr R 24 = wa 1500 /\ getr R 25 = wa 16140901064495857663 /\ (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA CLS n SB RIB P Hsc. destruct (gng0pb_setup regs m CA CLS n SB RIB P) as [HR HK].
  set (E := Ez regs (VALS_gng0pb CA CLS n SB RIB)) in *. destruct P as [gng0pb_R10 gng0pb_R11 gng0pb_R12 gng0pb_R13 gng0pb_R14 gng0pb_HSTK gng0pb_rng_CA gng0pb_rng_CLS gng0pb_rng_n gng0pb_rng_SB gng0pb_rng_RIB gng0pb_ka1 gng0pb_kr3 gng0pb_ka5 gng0pb_ka7 gng0pb_kw8 gng0pb_kw9 gng0pb_kw10 gng0pb_kw11 gng0pb_kw12 gng0pb_kwr13 gng0pb_kw14 gng0pb_kw15 gng0pb_kw16 gng0pb_kw17].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CLS) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 200 [0x7db90] AXF_gng0pb.scr_png0pb 0x44474 AXF_gng0pb.sr_gng0pb AXF_gng0pb.kn_gng0pb 37 _ _ _ E m rom regs AXF_gng0pb.RES_png0pb_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gng0pb.RES_png0pb fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gng0pb_mem_png0pb m regs CA CLS n SB RIB) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gng0pb_mem_png0pb. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GNG0PB.
End AXF_gng0pbz.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_gngtz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_gngtz.

Module AXF_gpb2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_RI := EVar 33.
Definition e_RB := EVar 34.
Definition e_S16 := EVar 35.
Definition e_TP := EVar 36.
Definition e_K := EVar 37.
Definition e_TSDA := EVar 38.
Definition e_PT := EVar 39.
Definition e_T := EVar 40.
Definition e_mm1 := EVar 41.
Definition e_mm2 := EVar 42.
Definition e_st2 := EVar 43.
Definition STK := SA (EVar 2) (-1024).
Definition sr_gpb2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 4 (e_TP)) 8 (e_RI)) 9 (EAlu ALU_ADD e_CA (ELit 2560))) 18 (e_RB)) 19 (ELit 262144)) 20 (e_RB)) 21 (EMd M_MUL (ELit 16) e_S16)) 22 (ELit 923480)).
Definition kn_gpb2 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_RI 1 (2^47);
    KAlign e_RI 128;
    KRange e_RB 4096 (2^47);
    KAlign e_RB 4096;
    KRange e_S16 2 4096;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 935456) 1 (ELit 1);
    KWord (SA (ELit 0) 935460) 4 e_K;
    KWord (SA e_TP (-88)) 8 e_TSDA;
    KWord (SA (EAlu ALU_ADD e_TSDA (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_K)) (ELit 29))) 0) 8 e_PT;
    KWord (SA e_PT 152) 8 e_T;
    KWord (SA e_T 2872) 8 e_mm1;
    KWr (SA e_T 2872) (ELit 8);
    KWord (SA e_T 2880) 8 e_mm2;
    KWr (SA e_T 2880) (ELit 8);
    KWord (SA e_CA 2584) 8 e_st2;
    KWr (SA e_CA 2584) (ELit 8);
    KWord (SA e_RI 16) 8 (ELit 0);
    KWord (SA e_RI 24) 8 (ELit 0);
    KWord (SA e_RI 32) 8 (ELit 0);
    KWord (SA e_RI 48) 8 (ELit 0);
    KWr (SA e_RI 48) (ELit 8);
    KWord (SA (ELit 0) 923536) 1 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_gpb2 : scripts := SCR [false; false] [] [].
Definition ss_gpb2 := SS 0x4497c sr_gpb2 [] kn_gpb2 44.
Definition RUN_gpb2 := sym_exec SEGS 160 true [0x7db90] scr_gpb2 ss_gpb2 [].

Definition scr_ppb2 : scripts := SCR [false; false] [] [].
Definition RES_ppb2 := Eval vm_compute in sym_exec SEGS 160 true [0x7db90] scr_ppb2 ss_gpb2 [].
Lemma RES_ppb2_ok : sym_exec SEGS 160 true [0x7db90] scr_ppb2 (SS 0x4497c sr_gpb2 [] kn_gpb2 44) [] = RES_ppb2.
Proof. vm_compute. reflexivity. Qed.
End AXF_gpb2.


Module AXF_gpb2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GPB2.
Context {fx : FPState}.

Definition VALS_gpb2 (CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 : Z) : list Z := [CA; RI; RB; S16; TP; K; TSDA; PT; T; mm1; mm2; st2].

Record gpb2_pre (regs : bvmap 5 word) (m : word -> option byte) (CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 : Z) : Prop := {
  gpb2_R4 : getr regs 4 = wa TP ;
  gpb2_R8 : getr regs 8 = wa RI ;
  gpb2_R9 : getr regs 9 = wa (CA + 2560) ;
  gpb2_R18 : getr regs 18 = wa RB ;
  gpb2_R19 : getr regs 19 = wa 262144 ;
  gpb2_R20 : getr regs 20 = wa RB ;
  gpb2_R21 : getr regs 21 = wa (16 * S16) ;
  gpb2_R22 : getr regs 22 = wa 923480 ;
  gpb2_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gpb2_rng_CA : 1 <= CA <= 2^47 ;
  gpb2_rng_RI : 1 <= RI <= 2^47 ;
  gpb2_rng_RB : 4096 <= RB <= 2^47 ;
  gpb2_rng_S16 : 2 <= S16 <= 4096 ;
  gpb2_rng_TP : 4096 <= TP <= 2^47 ;
  gpb2_rng_K : 0 <= K <= 1023 ;
  gpb2_rng_TSDA : 1 <= TSDA <= 2^47 ;
  gpb2_rng_PT : 1 <= PT <= 2^47 ;
  gpb2_rng_T : 1 <= T <= 2^47 ;
  gpb2_rng_mm1 : 0 <= mm1 <= 2^64-1 ;
  gpb2_rng_mm2 : 0 <= mm2 <= 2^64-1 ;
  gpb2_rng_st2 : 0 <= st2 <= 2^64-1 ;
  gpb2_ka1 : CA mod 16 = 0 ;
  gpb2_ka3 : RI mod 128 = 0 ;
  gpb2_ka5 : RB mod 4096 = 0 ;
  gpb2_kr7 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gpb2_kw8 : rdn SEGS m (wa (0 + 935456)) 1 = Some (word_to_le_bytes 1 (wa 1)) ;
  gpb2_kw9 : rdn SEGS m (wa (0 + 935460)) 4 = Some (word_to_le_bytes 4 (wa K)) ;
  gpb2_kw10 : rdn SEGS m (wa (TP + -88)) 8 = Some (word_to_le_bytes 8 (wa TSDA)) ;
  gpb2_kw11 : rdn SEGS m (wa (TSDA + Z.shiftr (((4294967296 * ext_Z true 0 4 K)) mod 2^64) 29 + 0)) 8 = Some (word_to_le_bytes 8 (wa PT)) ;
  gpb2_kw12 : rdn SEGS m (wa (PT + 152)) 8 = Some (word_to_le_bytes 8 (wa T)) ;
  gpb2_kw13 : rdn SEGS m (wa (T + 2872)) 8 = Some (word_to_le_bytes 8 (wa mm1)) ;
  gpb2_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2872 + d)) k = true ;
  gpb2_kw15 : rdn SEGS m (wa (T + 2880)) 8 = Some (word_to_le_bytes 8 (wa mm2)) ;
  gpb2_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2880 + d)) k = true ;
  gpb2_kw17 : rdn SEGS m (wa (CA + 2584)) 8 = Some (word_to_le_bytes 8 (wa st2)) ;
  gpb2_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2584 + d)) k = true ;
  gpb2_kw19 : rdn SEGS m (wa (RI + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpb2_kw20 : rdn SEGS m (wa (RI + 24)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpb2_kw21 : rdn SEGS m (wa (RI + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpb2_kw22 : rdn SEGS m (wa (RI + 48)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpb2_kwr23 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 48 + d)) k = true ;
  gpb2_kw24 : rdn SEGS m (wa (0 + 923536)) 1 = Some (word_to_le_bytes 1 (wa 0))
}.


#[using="Type"] Lemma gpb2_setup : forall regs m CA RI RB S16 TP K TSDA PT T mm1 mm2 st2, gpb2_pre regs m CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 ->
  regs_ok (Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) AXF_gpb2.sr_gpb2 regs /\ know_ok SEGS (Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) m AXF_gpb2.kn_gpb2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 P. destruct P as [gpb2_R4 gpb2_R8 gpb2_R9 gpb2_R18 gpb2_R19 gpb2_R20 gpb2_R21 gpb2_R22 gpb2_HSTK gpb2_rng_CA gpb2_rng_RI gpb2_rng_RB gpb2_rng_S16 gpb2_rng_TP gpb2_rng_K gpb2_rng_TSDA gpb2_rng_PT gpb2_rng_T gpb2_rng_mm1 gpb2_rng_mm2 gpb2_rng_st2 gpb2_ka1 gpb2_ka3 gpb2_ka5 gpb2_kr7 gpb2_kw8 gpb2_kw9 gpb2_kw10 gpb2_kw11 gpb2_kw12 gpb2_kw13 gpb2_kwr14 gpb2_kw15 gpb2_kwr16 gpb2_kw17 gpb2_kwr18 gpb2_kw19 gpb2_kw20 gpb2_kw21 gpb2_kw22 gpb2_kwr23 gpb2_kw24].
  set (E := Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = S16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = st2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  split.
  { unfold AXF_gpb2.sr_gpb2.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 4); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite gpb2_R4. reflexivity.
    - rewrite gpb2_R8. reflexivity.
    - rewrite gpb2_R9, zeval_sound. cbn [zeval edenot AXF_gpb2.e_CA AXF_gpb2.e_RI AXF_gpb2.e_RB AXF_gpb2.e_S16 AXF_gpb2.e_TP AXF_gpb2.e_K AXF_gpb2.e_TSDA AXF_gpb2.e_PT AXF_gpb2.e_T AXF_gpb2.e_mm1 AXF_gpb2.e_mm2 AXF_gpb2.e_st2 AXF_gpb2.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gpb2_R18. reflexivity.
    - rewrite gpb2_R19. reflexivity.
    - rewrite gpb2_R20. reflexivity.
    - rewrite gpb2_R21, zeval_sound. cbn [zeval edenot AXF_gpb2.e_CA AXF_gpb2.e_RI AXF_gpb2.e_RB AXF_gpb2.e_S16 AXF_gpb2.e_TP AXF_gpb2.e_K AXF_gpb2.e_TSDA AXF_gpb2.e_PT AXF_gpb2.e_T AXF_gpb2.e_mm1 AXF_gpb2.e_mm2 AXF_gpb2.e_st2 AXF_gpb2.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gpb2_R22. reflexivity. }
  unfold know_ok, AXF_gpb2.kn_gpb2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gpb2.e_CA AXF_gpb2.e_RI AXF_gpb2.e_RB AXF_gpb2.e_S16 AXF_gpb2.e_TP AXF_gpb2.e_K AXF_gpb2.e_TSDA AXF_gpb2.e_PT AXF_gpb2.e_T AXF_gpb2.e_mm1 AXF_gpb2.e_mm2 AXF_gpb2.e_st2 AXF_gpb2.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ gpb2_rng_CA eq_refl eq_refl), ?(mod64_of_range RI _ _ gpb2_rng_RI eq_refl eq_refl), ?(mod64_of_range RB _ _ gpb2_rng_RB eq_refl eq_refl), ?(mod64_of_range S16 _ _ gpb2_rng_S16 eq_refl eq_refl), ?(mod64_of_range TP _ _ gpb2_rng_TP eq_refl eq_refl), ?(mod64_of_range K _ _ gpb2_rng_K eq_refl eq_refl), ?(mod64_of_range TSDA _ _ gpb2_rng_TSDA eq_refl eq_refl), ?(mod64_of_range PT _ _ gpb2_rng_PT eq_refl eq_refl), ?(mod64_of_range T _ _ gpb2_rng_T eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gpb2_kwr14 | apply gpb2_kwr16 | apply gpb2_kwr18 | apply gpb2_kwr23]; assumption).
  all: try (clear - gpb2_rng_CA gpb2_rng_RI gpb2_rng_RB gpb2_rng_S16 gpb2_rng_TP gpb2_rng_K gpb2_rng_TSDA gpb2_rng_PT gpb2_rng_T gpb2_rng_mm1 gpb2_rng_mm2 gpb2_rng_st2 gpb2_ka1 gpb2_ka3 gpb2_ka5 gpb2_kr7 HKO; lia).
  all: first [lia].
Qed.


Definition gpb2_mem_ppb2 (m : word -> option byte) (regs : bvmap 5 word) (CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 280960))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa 436892))) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))) (wa (CA + 2584)) (word_to_le_bytes 8 (wa (st2 + 262144)))) (wa (RI + 48)) (word_to_le_bytes 8 (wa 262144))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 281044))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa RI))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (edenot (Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) (EMd M_DIVU (ELit 262144) (EMd M_MUL (ELit 16) (EVar 35)))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa RB))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (edenot (Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) (EMd M_DIVU (ELit 262144) (EMd M_MUL (ELit 16) (EVar 35))))))).

#[using="Type"] Theorem gpb2_ppb2 : forall regs m rom CA RI RB S16 TP K TSDA PT T mm1 mm2 st2, gpb2_pre regs m CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 ->
  scs_denot SEGS m (Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) (snd (fst AXF_gpb2.RES_ppb2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x4497c) m rom) (mkst R (wa 0x7db90) (gpb2_mem_ppb2 m regs CA RI RB S16 TP K TSDA PT T mm1 mm2 st2) rom) /\
    getr R 1 = wa 271780 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48) /\ getr R 4 = wa TP /\ getr R 8 = wa 262144 /\ getr R 9 = wa (RB + 3758096384) /\ getr R 10 = wa 923480 /\ getr R 11 = wa (RB + 3758096384) /\ getr R 12 = wa 262144 /\ getr R 13 = wa 104134 /\ getr R 14 = wa 0 /\ getr R 15 = wa 3758096384 /\ getr R 18 = wa 262144 /\ getr R 19 = wa RI /\ getr R 20 = wa 262144 /\ getr R 21 = wa (16 * S16) /\ getr R 22 = wa 923480 /\ (forall k, In k [3; 5; 6; 7; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 P Hsc. destruct (gpb2_setup regs m CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 P) as [HR HK].
  set (E := Ez regs (VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) in *. destruct P as [gpb2_R4 gpb2_R8 gpb2_R9 gpb2_R18 gpb2_R19 gpb2_R20 gpb2_R21 gpb2_R22 gpb2_HSTK gpb2_rng_CA gpb2_rng_RI gpb2_rng_RB gpb2_rng_S16 gpb2_rng_TP gpb2_rng_K gpb2_rng_TSDA gpb2_rng_PT gpb2_rng_T gpb2_rng_mm1 gpb2_rng_mm2 gpb2_rng_st2 gpb2_ka1 gpb2_ka3 gpb2_ka5 gpb2_kr7 gpb2_kw8 gpb2_kw9 gpb2_kw10 gpb2_kw11 gpb2_kw12 gpb2_kw13 gpb2_kwr14 gpb2_kw15 gpb2_kwr16 gpb2_kw17 gpb2_kwr18 gpb2_kw19 gpb2_kw20 gpb2_kw21 gpb2_kw22 gpb2_kwr23 gpb2_kw24].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = S16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = st2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  destruct (run_sound SEGS 160 [0x7db90] AXF_gpb2.scr_ppb2 0x4497c AXF_gpb2.sr_gpb2 AXF_gpb2.kn_gpb2 44 _ _ _ E m rom regs AXF_gpb2.RES_ppb2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gpb2.RES_ppb2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gpb2_mem_ppb2 m regs CA RI RB S16 TP K TSDA PT T mm1 mm2 st2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gpb2_mem_ppb2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GPB2.
End AXF_gpb2z.


Module AXF_gpc1b.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_RI := EVar 32.
Definition e_RB := EVar 33.
Definition e_S16 := EVar 34.
Definition e_NEW := EVar 35.
Definition e_TP := EVar 36.
Definition e_K := EVar 37.
Definition e_TSDA := EVar 38.
Definition e_PT := EVar 39.
Definition e_T := EVar 40.
Definition e_mm1 := EVar 41.
Definition e_mm2 := EVar 42.
Definition STK := SA (EVar 2) (-1024).
Definition sr_gpc1b := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 4 (e_TP)) 8 (ELit 262144)) 9 (EAlu ALU_ADD e_RB (ELit 3758096384))) 18 (ELit 262144)) 19 (e_RI)) 20 (ELit 262144)) 21 (EMd M_MUL (ELit 16) e_S16)) 22 (ELit 923480)).
Definition kn_gpc1b : list kentry :=
  [ KRange e_RI 1 (2^47);
    KAlign e_RI 128;
    KRange e_RB 4096 (2^47);
    KAlign e_RB 4096;
    KRange e_S16 2 4096;
    KRange e_NEW 4 8192;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 935456) 1 (ELit 1);
    KWord (SA (ELit 0) 935460) 4 e_K;
    KWord (SA e_TP (-88)) 8 e_TSDA;
    KWord (SA (EAlu ALU_ADD e_TSDA (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_K)) (ELit 29))) 0) 8 e_PT;
    KWord (SA e_PT 152) 8 e_T;
    KWord (SA e_T 2872) 8 e_mm1;
    KWr (SA e_T 2872) (ELit 8);
    KWord (SA e_T 2880) 8 e_mm2;
    KWr (SA e_T 2880) (ELit 8);
    KWr (SA e_RI 24) (ELit 8);
    KWord (SA e_RI 32) 8 (ELit 0);
    KWord (SA (EVar 2) 40) 8 (ELit 281044);
    KWord (SA (EVar 2) 32) 8 e_RI;
    KWord (SA (EVar 2) 24) 8 e_NEW;
    KWord (SA (EVar 2) 16) 8 e_RB;
    KWord (SA (EVar 2) 8) 8 e_NEW;
    KWr STK (ELit 1024) ].
Definition scr_gpc1b : scripts := SCR [false; false] [] [].
Definition ss_gpc1b := SS 0x425c0 sr_gpc1b [] kn_gpc1b 43.
Definition RUN_gpc1b := sym_exec SEGS 120 true [0x449fc] scr_gpc1b ss_gpc1b [].

Definition scr_ppc1b : scripts := SCR [false; false] [] [].
Definition RES_ppc1b := Eval vm_compute in sym_exec SEGS 120 true [0x449fc] scr_ppc1b ss_gpc1b [].
Lemma RES_ppc1b_ok : sym_exec SEGS 120 true [0x449fc] scr_ppc1b (SS 0x425c0 sr_gpc1b [] kn_gpc1b 43) [] = RES_ppc1b.
Proof. vm_compute. reflexivity. Qed.
End AXF_gpc1b.


Module AXF_gpc1bz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GPC1B.
Context {fx : FPState}.

Definition VALS_gpc1b (RI RB S16 NEW TP K TSDA PT T mm1 mm2 : Z) : list Z := [RI; RB; S16; NEW; TP; K; TSDA; PT; T; mm1; mm2].

Record gpc1b_pre (regs : bvmap 5 word) (m : word -> option byte) (RI RB S16 NEW TP K TSDA PT T mm1 mm2 : Z) : Prop := {
  gpc1b_R4 : getr regs 4 = wa TP ;
  gpc1b_R8 : getr regs 8 = wa 262144 ;
  gpc1b_R9 : getr regs 9 = wa (RB + 3758096384) ;
  gpc1b_R18 : getr regs 18 = wa 262144 ;
  gpc1b_R19 : getr regs 19 = wa RI ;
  gpc1b_R20 : getr regs 20 = wa 262144 ;
  gpc1b_R21 : getr regs 21 = wa (16 * S16) ;
  gpc1b_R22 : getr regs 22 = wa 923480 ;
  gpc1b_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gpc1b_rng_RI : 1 <= RI <= 2^47 ;
  gpc1b_rng_RB : 4096 <= RB <= 2^47 ;
  gpc1b_rng_S16 : 2 <= S16 <= 4096 ;
  gpc1b_rng_NEW : 4 <= NEW <= 8192 ;
  gpc1b_rng_TP : 4096 <= TP <= 2^47 ;
  gpc1b_rng_K : 0 <= K <= 1023 ;
  gpc1b_rng_TSDA : 1 <= TSDA <= 2^47 ;
  gpc1b_rng_PT : 1 <= PT <= 2^47 ;
  gpc1b_rng_T : 1 <= T <= 2^47 ;
  gpc1b_rng_mm1 : 0 <= mm1 <= 2^64-1 ;
  gpc1b_rng_mm2 : 0 <= mm2 <= 2^64-1 ;
  gpc1b_ka1 : RI mod 128 = 0 ;
  gpc1b_ka3 : RB mod 4096 = 0 ;
  gpc1b_kr6 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gpc1b_kw7 : rdn SEGS m (wa (0 + 935456)) 1 = Some (word_to_le_bytes 1 (wa 1)) ;
  gpc1b_kw8 : rdn SEGS m (wa (0 + 935460)) 4 = Some (word_to_le_bytes 4 (wa K)) ;
  gpc1b_kw9 : rdn SEGS m (wa (TP + -88)) 8 = Some (word_to_le_bytes 8 (wa TSDA)) ;
  gpc1b_kw10 : rdn SEGS m (wa (TSDA + Z.shiftr (((4294967296 * ext_Z true 0 4 K)) mod 2^64) 29 + 0)) 8 = Some (word_to_le_bytes 8 (wa PT)) ;
  gpc1b_kw11 : rdn SEGS m (wa (PT + 152)) 8 = Some (word_to_le_bytes 8 (wa T)) ;
  gpc1b_kw12 : rdn SEGS m (wa (T + 2872)) 8 = Some (word_to_le_bytes 8 (wa mm1)) ;
  gpc1b_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2872 + d)) k = true ;
  gpc1b_kw14 : rdn SEGS m (wa (T + 2880)) 8 = Some (word_to_le_bytes 8 (wa mm2)) ;
  gpc1b_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2880 + d)) k = true ;
  gpc1b_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 24 + d)) k = true ;
  gpc1b_kw17 : rdn SEGS m (wa (RI + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpc1b_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa 281044)) ;
  gpc1b_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa RI)) ;
  gpc1b_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa NEW)) ;
  gpc1b_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa RB)) ;
  gpc1b_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa NEW))
}.


#[using="Type"] Lemma gpc1b_setup : forall regs m RI RB S16 NEW TP K TSDA PT T mm1 mm2, gpc1b_pre regs m RI RB S16 NEW TP K TSDA PT T mm1 mm2 ->
  regs_ok (Ez regs (VALS_gpc1b RI RB S16 NEW TP K TSDA PT T mm1 mm2)) AXF_gpc1b.sr_gpc1b regs /\ know_ok SEGS (Ez regs (VALS_gpc1b RI RB S16 NEW TP K TSDA PT T mm1 mm2)) m AXF_gpc1b.kn_gpc1b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m RI RB S16 NEW TP K TSDA PT T mm1 mm2 P. destruct P as [gpc1b_R4 gpc1b_R8 gpc1b_R9 gpc1b_R18 gpc1b_R19 gpc1b_R20 gpc1b_R21 gpc1b_R22 gpc1b_HSTK gpc1b_rng_RI gpc1b_rng_RB gpc1b_rng_S16 gpc1b_rng_NEW gpc1b_rng_TP gpc1b_rng_K gpc1b_rng_TSDA gpc1b_rng_PT gpc1b_rng_T gpc1b_rng_mm1 gpc1b_rng_mm2 gpc1b_ka1 gpc1b_ka3 gpc1b_kr6 gpc1b_kw7 gpc1b_kw8 gpc1b_kw9 gpc1b_kw10 gpc1b_kw11 gpc1b_kw12 gpc1b_kwr13 gpc1b_kw14 gpc1b_kwr15 gpc1b_kwr16 gpc1b_kw17 gpc1b_kw18 gpc1b_kw19 gpc1b_kw20 gpc1b_kw21 gpc1b_kw22].
  set (E := Ez regs (VALS_gpc1b RI RB S16 NEW TP K TSDA PT T mm1 mm2)).
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = S16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  split.
  { unfold AXF_gpc1b.sr_gpc1b.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 4); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite gpc1b_R4. reflexivity.
    - rewrite gpc1b_R8. reflexivity.
    - rewrite gpc1b_R9, zeval_sound. cbn [zeval edenot AXF_gpc1b.e_RI AXF_gpc1b.e_RB AXF_gpc1b.e_S16 AXF_gpc1b.e_NEW AXF_gpc1b.e_TP AXF_gpc1b.e_K AXF_gpc1b.e_TSDA AXF_gpc1b.e_PT AXF_gpc1b.e_T AXF_gpc1b.e_mm1 AXF_gpc1b.e_mm2 AXF_gpc1b.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gpc1b_R18. reflexivity.
    - rewrite gpc1b_R19. reflexivity.
    - rewrite gpc1b_R20. reflexivity.
    - rewrite gpc1b_R21, zeval_sound. cbn [zeval edenot AXF_gpc1b.e_RI AXF_gpc1b.e_RB AXF_gpc1b.e_S16 AXF_gpc1b.e_NEW AXF_gpc1b.e_TP AXF_gpc1b.e_K AXF_gpc1b.e_TSDA AXF_gpc1b.e_PT AXF_gpc1b.e_T AXF_gpc1b.e_mm1 AXF_gpc1b.e_mm2 AXF_gpc1b.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite gpc1b_R22. reflexivity. }
  unfold know_ok, AXF_gpc1b.kn_gpc1b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gpc1b.e_RI AXF_gpc1b.e_RB AXF_gpc1b.e_S16 AXF_gpc1b.e_NEW AXF_gpc1b.e_TP AXF_gpc1b.e_K AXF_gpc1b.e_TSDA AXF_gpc1b.e_PT AXF_gpc1b.e_T AXF_gpc1b.e_mm1 AXF_gpc1b.e_mm2 AXF_gpc1b.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range RI _ _ gpc1b_rng_RI eq_refl eq_refl), ?(mod64_of_range RB _ _ gpc1b_rng_RB eq_refl eq_refl), ?(mod64_of_range S16 _ _ gpc1b_rng_S16 eq_refl eq_refl), ?(mod64_of_range NEW _ _ gpc1b_rng_NEW eq_refl eq_refl), ?(mod64_of_range TP _ _ gpc1b_rng_TP eq_refl eq_refl), ?(mod64_of_range K _ _ gpc1b_rng_K eq_refl eq_refl), ?(mod64_of_range TSDA _ _ gpc1b_rng_TSDA eq_refl eq_refl), ?(mod64_of_range PT _ _ gpc1b_rng_PT eq_refl eq_refl), ?(mod64_of_range T _ _ gpc1b_rng_T eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gpc1b_kwr13 | apply gpc1b_kwr15 | apply gpc1b_kwr16]; assumption).
  all: try (clear - gpc1b_rng_RI gpc1b_rng_RB gpc1b_rng_S16 gpc1b_rng_NEW gpc1b_rng_TP gpc1b_rng_K gpc1b_rng_TSDA gpc1b_rng_PT gpc1b_rng_T gpc1b_rng_mm1 gpc1b_rng_mm2 gpc1b_ka1 gpc1b_ka3 gpc1b_kr6 HKO; lia).
  all: first [lia].
Qed.


Definition gpc1b_mem_ppc1b (m : word -> option byte) (regs : bvmap 5 word) (RI RB S16 NEW TP K TSDA PT T mm1 mm2 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 271812))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa 436892))) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))) (wa (RI + 24)) (word_to_le_bytes 8 (wa 262144)).

#[using="Type"] Theorem gpc1b_ppc1b : forall regs m rom RI RB S16 NEW TP K TSDA PT T mm1 mm2, gpc1b_pre regs m RI RB S16 NEW TP K TSDA PT T mm1 mm2 ->
  scs_denot SEGS m (Ez regs (VALS_gpc1b RI RB S16 NEW TP K TSDA PT T mm1 mm2)) (snd (fst AXF_gpc1b.RES_ppc1b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x425c0) m rom) (mkst R (wa 0x449fc) (gpc1b_mem_ppc1b m regs RI RB S16 NEW TP K TSDA PT T mm1 mm2) rom) /\
    getr R 1 = wa 281044 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48) /\ getr R 4 = wa TP /\ getr R 8 = wa RI /\ getr R 9 = wa (4 * NEW) /\ getr R 10 = wa 0 /\ getr R 11 = wa ((RB + (4 * NEW)) + 3758096384) /\ getr R 12 = wa 0 /\ getr R 13 = wa 0 /\ getr R 18 = wa RB /\ getr R 19 = wa NEW /\ getr R 20 = wa 262144 /\ getr R 21 = wa (16 * S16) /\ getr R 22 = wa 923480 /\ (forall k, In k [3; 5; 6; 7; 14; 15; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom RI RB S16 NEW TP K TSDA PT T mm1 mm2 P Hsc. destruct (gpc1b_setup regs m RI RB S16 NEW TP K TSDA PT T mm1 mm2 P) as [HR HK].
  set (E := Ez regs (VALS_gpc1b RI RB S16 NEW TP K TSDA PT T mm1 mm2)) in *. destruct P as [gpc1b_R4 gpc1b_R8 gpc1b_R9 gpc1b_R18 gpc1b_R19 gpc1b_R20 gpc1b_R21 gpc1b_R22 gpc1b_HSTK gpc1b_rng_RI gpc1b_rng_RB gpc1b_rng_S16 gpc1b_rng_NEW gpc1b_rng_TP gpc1b_rng_K gpc1b_rng_TSDA gpc1b_rng_PT gpc1b_rng_T gpc1b_rng_mm1 gpc1b_rng_mm2 gpc1b_ka1 gpc1b_ka3 gpc1b_kr6 gpc1b_kw7 gpc1b_kw8 gpc1b_kw9 gpc1b_kw10 gpc1b_kw11 gpc1b_kw12 gpc1b_kwr13 gpc1b_kw14 gpc1b_kwr15 gpc1b_kwr16 gpc1b_kw17 gpc1b_kw18 gpc1b_kw19 gpc1b_kw20 gpc1b_kw21 gpc1b_kw22].
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = S16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  destruct (run_sound SEGS 120 [0x449fc] AXF_gpc1b.scr_ppc1b 0x425c0 AXF_gpc1b.sr_gpc1b AXF_gpc1b.kn_gpc1b 43 _ _ _ E m rom regs AXF_gpc1b.RES_ppc1b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gpc1b.RES_ppc1b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gpc1b_mem_ppc1b m regs RI RB S16 NEW TP K TSDA PT T mm1 mm2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gpc1b_mem_ppc1b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GPC1B.
End AXF_gpc1bz.


Module AXF_gpc2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_RI := EVar 32.
Definition e_S16 := EVar 33.
Definition e_NEW := EVar 34.
Definition e_FA := EVar 35.
Definition e_REC16 := EVar 36.
Definition e_n := EVar 37.
Definition STK := SA (EVar 2) (-1024).
Definition sr_gpc2 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_RI)) 10 (e_NEW)) 19 (e_NEW)) 21 (EMd M_MUL (ELit 16) e_S16)).
Definition kn_gpc2 : list kentry :=
  [ KRange e_RI 1 (2^47);
    KAlign e_RI 128;
    KRange e_S16 2 4096;
    KRange e_NEW 4 8192;
    KRange e_FA 4096 (2^47);
    KRange e_REC16 1 (2^47);
    KRange e_n 1 8;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA e_RI 16) 8 (ELit 0);
    KWr (SA e_RI 16) (ELit 8);
    KWord (SA e_RI 32) 8 (ELit 0);
    KWr (SA e_RI 32) (ELit 8);
    KWord (SA e_RI 48) 8 (ELit 262144);
    KWord (SA e_RI 40) 8 (ELit 0);
    KWord (SA e_RI 56) 8 (ELit 0);
    KWr (SA e_RI 68) (ELit 1);
    KWord (SA (EVar 2) 56) 8 (ELit 280564);
    KWord (SA (EVar 2) 48) 8 e_RI;
    KWord (SA (EVar 2) 40) 8 (ELit 923480);
    KWord (SA (EVar 2) 32) 8 (EAlu ALU_ADD e_RI (ELit 8));
    KWord (SA (EVar 2) 24) 8 (ELit 2305843009213693952);
    KWord (SA (EVar 2) 16) 8 e_FA;
    KWord (SA (EVar 2) 8) 8 e_REC16;
    KWord (SA (EVar 2) 0) 8 e_n;
    KWr STK (ELit 1024) ].
Definition scr_gpc2 : scripts := SCR [false; false] [] [].
Definition ss_gpc2 := SS 0x44a1c sr_gpc2 [] kn_gpc2 38.
Definition RUN_gpc2 := sym_exec SEGS 80 true [0x446ac] scr_gpc2 ss_gpc2 [].

Definition scr_ppc2 : scripts := SCR [false; false] [] [].
Definition RES_ppc2 := Eval vm_compute in sym_exec SEGS 80 true [0x446ac] scr_ppc2 ss_gpc2 [].
Lemma RES_ppc2_ok : sym_exec SEGS 80 true [0x446ac] scr_ppc2 (SS 0x44a1c sr_gpc2 [] kn_gpc2 38) [] = RES_ppc2.
Proof. vm_compute. reflexivity. Qed.
End AXF_gpc2.


Module AXF_gpc2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section GPC2.
Context {fx : FPState}.

Definition VALS_gpc2 (RI S16 NEW FA REC16 n : Z) : list Z := [RI; S16; NEW; FA; REC16; n].

Record gpc2_pre (regs : bvmap 5 word) (m : word -> option byte) (RI S16 NEW FA REC16 n : Z) : Prop := {
  gpc2_R8 : getr regs 8 = wa RI ;
  gpc2_R10 : getr regs 10 = wa NEW ;
  gpc2_R19 : getr regs 19 = wa NEW ;
  gpc2_R21 : getr regs 21 = wa (16 * S16) ;
  gpc2_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  gpc2_rng_RI : 1 <= RI <= 2^47 ;
  gpc2_rng_S16 : 2 <= S16 <= 4096 ;
  gpc2_rng_NEW : 4 <= NEW <= 8192 ;
  gpc2_rng_FA : 4096 <= FA <= 2^47 ;
  gpc2_rng_REC16 : 1 <= REC16 <= 2^47 ;
  gpc2_rng_n : 1 <= n <= 8 ;
  gpc2_ka1 : RI mod 128 = 0 ;
  gpc2_kr7 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  gpc2_kw8 : rdn SEGS m (wa (RI + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpc2_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 16 + d)) k = true ;
  gpc2_kw10 : rdn SEGS m (wa (RI + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpc2_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 32 + d)) k = true ;
  gpc2_kw12 : rdn SEGS m (wa (RI + 48)) 8 = Some (word_to_le_bytes 8 (wa 262144)) ;
  gpc2_kw13 : rdn SEGS m (wa (RI + 40)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpc2_kw14 : rdn SEGS m (wa (RI + 56)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  gpc2_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (RI + 68 + d)) k = true ;
  gpc2_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa 280564)) ;
  gpc2_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa RI)) ;
  gpc2_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa 923480)) ;
  gpc2_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa (RI + 8))) ;
  gpc2_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa 2305843009213693952)) ;
  gpc2_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa FA)) ;
  gpc2_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa REC16)) ;
  gpc2_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa n))
}.


#[using="Type"] Lemma gpc2_setup : forall regs m RI S16 NEW FA REC16 n, gpc2_pre regs m RI S16 NEW FA REC16 n ->
  regs_ok (Ez regs (VALS_gpc2 RI S16 NEW FA REC16 n)) AXF_gpc2.sr_gpc2 regs /\ know_ok SEGS (Ez regs (VALS_gpc2 RI S16 NEW FA REC16 n)) m AXF_gpc2.kn_gpc2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m RI S16 NEW FA REC16 n P. destruct P as [gpc2_R8 gpc2_R10 gpc2_R19 gpc2_R21 gpc2_HSTK gpc2_rng_RI gpc2_rng_S16 gpc2_rng_NEW gpc2_rng_FA gpc2_rng_REC16 gpc2_rng_n gpc2_ka1 gpc2_kr7 gpc2_kw8 gpc2_kwr9 gpc2_kw10 gpc2_kwr11 gpc2_kw12 gpc2_kw13 gpc2_kw14 gpc2_kwr15 gpc2_kw16 gpc2_kw17 gpc2_kw18 gpc2_kw19 gpc2_kw20 gpc2_kw21 gpc2_kw22 gpc2_kw23].
  set (E := Ez regs (VALS_gpc2 RI S16 NEW FA REC16 n)).
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = FA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = REC16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_gpc2.sr_gpc2.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite gpc2_R8. reflexivity.
    - rewrite gpc2_R10. reflexivity.
    - rewrite gpc2_R19. reflexivity.
    - rewrite gpc2_R21, zeval_sound. cbn [zeval edenot AXF_gpc2.e_RI AXF_gpc2.e_S16 AXF_gpc2.e_NEW AXF_gpc2.e_FA AXF_gpc2.e_REC16 AXF_gpc2.e_n AXF_gpc2.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_gpc2.kn_gpc2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_gpc2.e_RI AXF_gpc2.e_S16 AXF_gpc2.e_NEW AXF_gpc2.e_FA AXF_gpc2.e_REC16 AXF_gpc2.e_n AXF_gpc2.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range RI _ _ gpc2_rng_RI eq_refl eq_refl), ?(mod64_of_range S16 _ _ gpc2_rng_S16 eq_refl eq_refl), ?(mod64_of_range NEW _ _ gpc2_rng_NEW eq_refl eq_refl), ?(mod64_of_range FA _ _ gpc2_rng_FA eq_refl eq_refl), ?(mod64_of_range REC16 _ _ gpc2_rng_REC16 eq_refl eq_refl), ?(mod64_of_range n _ _ gpc2_rng_n eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply gpc2_kwr9 | apply gpc2_kwr11 | apply gpc2_kwr15]; assumption).
  all: try (clear - gpc2_rng_RI gpc2_rng_S16 gpc2_rng_NEW gpc2_rng_FA gpc2_rng_REC16 gpc2_rng_n gpc2_ka1 gpc2_kr7; lia).
  all: first [lia].
Qed.


Definition gpc2_mem_ppc2 (m : word -> option byte) (regs : bvmap 5 word) (RI S16 NEW FA REC16 n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (RI + 16)) (word_to_le_bytes 8 (wa NEW))) (wa (RI + 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + (NEW * (16 * S16)))))) (wa (RI + 68)) (word_to_le_bytes 1 (wa 0))) (wa (RI + 16)) (word_to_le_bytes 8 (wa (NEW + (-1 * n)))).

#[using="Type"] Theorem gpc2_ppc2 : forall regs m rom RI S16 NEW FA REC16 n, gpc2_pre regs m RI S16 NEW FA REC16 n ->
  scs_denot SEGS m (Ez regs (VALS_gpc2 RI S16 NEW FA REC16 n)) (snd (fst AXF_gpc2.RES_ppc2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44a1c) m rom) (mkst R (wa 0x446ac) (gpc2_mem_ppc2 m regs RI S16 NEW FA REC16 n) rom) /\
    getr R 1 = wa 280564 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64) /\ getr R 8 = wa RI /\ getr R 9 = wa 923480 /\ getr R 10 = wa (RI + 8) /\ getr R 11 = wa (REC16 + (4 * n)) /\ getr R 13 = wa REC16 /\ getr R 14 = wa n /\ getr R 15 = wa ((4 * NEW) + (-4 * n)) /\ getr R 18 = wa (RI + 8) /\ getr R 19 = wa 2305843009213693952 /\ getr R 20 = wa ((4 * NEW) + (FA + (-4 * n))) /\ getr R 21 = wa REC16 /\ getr R 22 = wa n /\ (forall k, In k [3; 4; 5; 6; 7; 12; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom RI S16 NEW FA REC16 n P Hsc. destruct (gpc2_setup regs m RI S16 NEW FA REC16 n P) as [HR HK].
  set (E := Ez regs (VALS_gpc2 RI S16 NEW FA REC16 n)) in *. destruct P as [gpc2_R8 gpc2_R10 gpc2_R19 gpc2_R21 gpc2_HSTK gpc2_rng_RI gpc2_rng_S16 gpc2_rng_NEW gpc2_rng_FA gpc2_rng_REC16 gpc2_rng_n gpc2_ka1 gpc2_kr7 gpc2_kw8 gpc2_kwr9 gpc2_kw10 gpc2_kwr11 gpc2_kw12 gpc2_kw13 gpc2_kw14 gpc2_kwr15 gpc2_kw16 gpc2_kw17 gpc2_kw18 gpc2_kw19 gpc2_kw20 gpc2_kw21 gpc2_kw22 gpc2_kw23].
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = S16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = FA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = REC16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 80 [0x446ac] AXF_gpc2.scr_ppc2 0x44a1c AXF_gpc2.sr_gpc2 AXF_gpc2.kn_gpc2 38 _ _ _ E m rom regs AXF_gpc2.RES_ppc2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_gpc2.RES_ppc2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (gpc2_mem_ppc2 m regs RI S16 NEW FA REC16 n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold gpc2_mem_ppc2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GPC2.
End AXF_gpc2z.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition cls_of (nd : Z) : Z := if Z.leb nd 512 then (nd + 31) / 32 else cid nd.
Lemma cls_small : forall nd, 1 <= nd <= 512 -> Z.shiftr ((nd + 31) mod 2^64) 5 = (nd + 31) / 32 /\ 1 <= (nd + 31) / 32 <= 16.
Proof.
  intros nd H. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  split; [reflexivity|]. split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Fixpoint allb (f : Z -> bool) (lo : Z) (k : nat) : bool :=
  match k with O => f lo | S k' => allb f lo k' && allb f (lo + 2 ^ Z.of_nat k') k' end.
Lemma allb_ok : forall f k lo, allb f lo k = true -> forall x, lo <= x < lo + 2 ^ Z.of_nat k -> f x = true.
Proof.
  intros f k. induction k as [|k IH]; intros lo H x Hx; cbn [allb] in H.
  - change (2 ^ Z.of_nat 0) with 1 in Hx. replace x with lo by lia. exact H.
  - apply andb_prop in H as [H1 H2]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    destruct (Z.lt_ge_cases x (lo + 2 ^ Z.of_nat k)) as [Hl|Hg]; [apply (IH lo H1); lia | apply (IH _ H2); lia].
Qed.
Lemma cid_range : forall nd, 513 <= nd <= 65536 -> 17 <= cid nd <= 30.
Proof.
  intros nd H.
  assert (A : allb (fun x => (65536 <? x) || ((17 <=? cid x) && (cid x <=? 30))) 513 16 = true) by (vm_compute; reflexivity).
  pose proof (allb_ok _ _ _ A nd ltac:(change (2 ^ Z.of_nat 16) with 65536; lia)) as B. cbv beta in B.
  apply orb_prop in B as [B|B]; [apply Z.ltb_lt in B; lia|].
  apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

(* [comment removed for export] *)
Record INV_G (m : word -> option byte) (CA SB c sz nc newc j : Z) : Prop := {
  ig_geo : 1 <= c <= 30 /\ 16 <= sz /\ sz mod 16 = 0 /\ 1 <= nc <= 8 /\ 1 <= j /\ j + nc <= newc /\ newc * sz <= 262144 /\ newc <= 16384 ;
  ig_SB : rd m 923512 8 SB ;
  ig_RIB : rd m 923528 8 (SB + 137438953472) ;
  ig_cnt : rd m (REC CA c) 4 (cnt_of nc j) ;
  ig_mc : rd m (REC CA c + 4) 4 (2 * nc) ;
  ig_sz : rd m (REC CA c + 8) 8 sz ;
  ig_chunks : forall i, 0 <= i < cnt_of nc j -> rd m (REC CA c + 16 + 4 * i) 4 ((j + cnt_of nc j - 1 - i) * (sz / 16)) ;
  ig_mutex : rd m (RIX SB c) 8 0 ;
  ig_nf : rd m (RIX SB c + 16) 8 (newc - nc * b_of nc j) ;
  ig_na : exists na, 0 <= na < 2^64 /\ rd m (RIX SB c + 72) 8 na ;
  ig_fa : forall k, 0 <= k < newc - nc * b_of nc j -> rd m (FAX SB c + 4 * k) 4 ((newc - 1 - k) * (sz / 16)) ;
  ig_st : exists st, 0 <= st < 2^64 /\ rd m (CA + 2576) 8 st ;
  ig_wrec : wr m (REC CA c) 80 ;
  ig_wri : wr m (RIX SB c) 128 ;
  ig_wst : wr m (CA + 2560) 32
}.
Lemma INV_C_G : forall m CA SB c sz nc newc j, INV_C m CA SB c sz nc newc j -> INV_G m CA SB c sz nc newc j.
Proof. intros m CA SB c sz nc newc j [G ? ? ? ? ? ? ? ? ? ? ? ? ? ?]. constructor; try assumption. lia. Qed.

(* [comment removed for export] *)
Ltac zlh H := clear - H; lia.
Ltac zat R := repeat match goal with |- context [bv_unsigned (ev (Ez R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia
              end end.
Definition B47 : iv := (4194304, 2^47).
(* [comment removed for export] *)
Definition LOW : iv := (4304, 61648).
Definition HIGH : iv := (6529232, 2^47).
Definition TLOW : iv := (4096, 61440).
Definition THIGH : iv := (6529024, 2^47).
Definition SPr : rfact := (EVar 2, (2^46, 2^47)).
Ltac fact_go R HSPa HX HH :=
  try unfold rf_ok; try unfold df_ok; try unfold SPr; try unfold B47; try unfold LOW; try unfold HIGH; try unfold TLOW; try unfold THIGH; cbn [fst snd zeval edenot]; zat R; rewrite ?HSPa, ?HX; zlh HH.
Ltac facts_go R HSPa HX HH := repeat (first [apply Forall_nil | apply Forall_cons; [fact_go R HSPa HX HH|]]).
Ltac sc_refl rf df R HSPa HX HH :=
  apply (scs_chk_sound rf df); [ facts_go R HSPa HX HH | facts_go R HSPa HX HH | vm_compute; reflexivity ].

Section SCG.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variable SPa : Z.
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.

(* [comment removed for export] *)
#[using="HSPa"] Lemma sc_gnp0t : forall CA CLS cnt sz cp SB st s0o,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 + 256 <= SPa /\ 1 <= CLS <= 30 /\ 1 <= cnt <= 16 ->
  scs_denot SEGS m (Ez R (AXF_gnp0tz.VALS_gnp0t CA CLS cnt sz cp SB st s0o)) (snd (fst AXF_gnp0t.RES_pnp0tp)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS cnt sz cp SB st s0o HH. unfold AXF_gnp0tz.VALS_gnp0t.
  destruct HH as (HS & [HP|HP] & HR); assert (HH2 := conj HS (conj HP HR)); clear HS HP HR.
  - sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 30)); (EVar 34, (1, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH2.
  - sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (1, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH2.
Qed.
#[using="HSPa"] Lemma sc_gnp0rt : forall CA CLS,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 + 256 <= SPa /\ 1 <= CLS <= 30 ->
  scs_denot SEGS m (Ez R (AXF_gnp0rtz.VALS_gnp0rt CA CLS 0)) (snd (fst AXF_gnp0rt.RES_pnp0rt)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS HH. unfold AXF_gnp0rtz.VALS_gnp0rt.
  destruct HH as (HS & [HP|HP] & HR); assert (HH2 := conj HS (conj HP HR)); clear HS HP HR.
  - sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 30)); (EVar 34, (0, 0))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH2.
  - sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (0, 0))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH2.
Qed.
(* [comment removed for export] *)
#[using="HSPa"] Lemma sc_gnpr : forall CA CLS mc,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 + 256 <= SPa /\ 1 <= CLS <= 30 /\ 2 <= mc <= 16 ->
  scs_denot SEGS m (Ez R (AXF_gnprz.VALS_gnpr CA CLS mc)) (snd (fst AXF_gnpr.RES_pnpr)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS mc HH. unfold AXF_gnprz.VALS_gnpr.
  destruct HH as (HS & [HP|HP] & HR); assert (HH2 := conj HS (conj HP HR)); clear HS HP HR.
  - sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 30)); (EVar 34, (2, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH2.
  - sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (2, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH2.
Qed.
#[using="HSPa"] Lemma sc_gnri : forall CA CLS,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 4096 + 256 <= SPa /\ 1 <= CLS <= 30 ->
  scs_denot SEGS m (Ez R (AXF_gnriz.VALS_gnri CA CLS)) (snd (fst AXF_gnri.RES_pnri)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS HH. unfold AXF_gnriz.VALS_gnri.
  destruct HH as (HS & [HP|HP] & HR); assert (HH2 := conj HS (conj HP HR)); clear HS HP HR.
  - sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 30))] [(EVar 2, EVar 32, 4352)] R HSPa HSPa HH2.
  - sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30))] [(EVar 2, EVar 32, 4352)] R HSPa HSPa HH2.
Qed.
#[using="Type"] Lemma sc_gnri2 : forall CA CLS mc, scs_denot SEGS m (Ez R (AXF_gnri2z.VALS_gnri2 CA CLS mc)) (snd (fst AXF_gnri2.RES_pnri2)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. cbn [AXF_gnri2.RES_pnri2 fst snd]. constructor. Qed.
(* [comment removed for export] *)
#[using="HSPa"] Lemma sc_gng0 : forall CA CLS n SB RIB nf,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 + 256 <= SPa /\ 1 <= CLS <= 30 /\ 1 <= n <= 8 /\ n <= nf <= 16384 /\
  4194304 <= RIB /\ RIB + 4096 + 256 <= SPa /\ (CA + 2592 <= RIB \/ RIB + 4096 <= CA) ->
  scs_denot SEGS m (Ez R (AXF_gng0z.VALS_gng0 CA CLS n SB RIB nf)) (snd (fst AXF_gng0.RES_png0)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS n SB RIB nf HH. unfold AXF_gng0z.VALS_gng0.
  assert (HD : CA + 2592 <= RIB \/ RIB + 4096 <= CA) by tauto.
  assert (HPL : (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : CA + 2592 <= RIB) by (clear - HPL HH; lia). assert (HH2 := conj HPL (conj HD1 HH)); clear HH HD HD1 HPL.
    sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 30)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))] [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH2.
  - destruct HD as [HD|HD]; assert (HH2 := conj HPL (conj HD HH)); clear HH HD HPL.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))] [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH2.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))] [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH2.
Qed.
(* [comment removed for export] *)
Definition gp_ok (CA SB RIB : Z) : Prop :=
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 4096 + 512 <= SPa /\ 4194304 <= SB /\ RIB = SB + 137438953472 /\
  SB + 137438953472 + 4096 + 512 <= SPa /\ (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA).
#[using="HSPa"] Lemma sc_gng0ps : forall CA CLS n SB RIB, gp_ok CA SB RIB -> 1 <= CLS <= 16 -> 1 <= n <= 8 ->
  scs_denot SEGS m (Ez R (AXF_gng0psz.VALS_gng0ps CA CLS n SB RIB)) (snd (fst AXF_gng0ps.RES_png0ps)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS n SB RIB HO HC Hn. unfold gp_ok in HO. unfold AXF_gng0psz.VALS_gng0ps.
  assert (HD : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by tauto.
  assert (HPL : (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : CA + 2592 <= SB) by (clear - HPL HO; lia). assert (HH := conj HPL (conj HD1 (conj HC (conj Hn HO)))); clear HO HC Hn HD HD1 HPL.
    sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 16)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HPL (conj HD (conj HC (conj Hn HO)))); clear HO HC Hn HD HPL.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 16)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 16)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 32, EVar 35, 137438957568); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
#[using="HSPa"] Lemma sc_gng0pb : forall CA CLS n SB RIB, gp_ok CA SB RIB -> 17 <= CLS <= 30 -> 1 <= n <= 8 ->
  scs_denot SEGS m (Ez R (AXF_gng0pbz.VALS_gng0pb CA CLS n SB RIB)) (snd (fst AXF_gng0pb.RES_png0pb)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS n SB RIB HO HC Hn. unfold gp_ok in HO. unfold AXF_gng0pbz.VALS_gng0pb.
  assert (HD : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by tauto.
  assert (HPL : (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : CA + 2592 <= SB) by (clear - HPL HO; lia). assert (HH := conj HPL (conj HD1 (conj HC (conj Hn HO)))); clear HO HC Hn HD HD1 HPL.
    sc_refl [SPr; (EVar 32, LOW); (EVar 33, (17, 30)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HPL (conj HD (conj HC (conj Hn HO)))); clear HO HC Hn HD HPL.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (17, 30)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (17, 30)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 32, EVar 35, 137438957568); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="HSPa"] Lemma sc_gngt : forall CA CLS n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 + 256 <= SPa /\ 1 <= CLS <= 30 /\ 1 <= n <= 8 /\
  4194304 <= RIB /\ RIB + 4096 + 256 <= SPa /\ (CA + 2592 <= RIB \/ RIB + 4096 <= CA) ->
  scs_denot SEGS m (Ez R (AXF_gngtz.VALS_gngt CA CLS n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_gngtz.AXF_gngt.RES_pngt)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA CLS n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra HH. unfold AXF_gngtz.VALS_gngt.
  assert (HD : CA + 2592 <= RIB \/ RIB + 4096 <= CA) by tauto.
  assert (HPL : (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : CA + 2592 <= RIB) by (clear - HPL HH; lia). assert (HH2 := conj HPL (conj HD1 HH)); clear HH HD HD1 HPL.
    sc_refl [SPr; (EVar 32, LOW); (EVar 33, (1, 30)); (EVar 34, (1, 8)); (EVar 36, B47)] [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH2.
  - destruct HD as [HD|HD]; assert (HH2 := conj HPL (conj HD HH)); clear HH HD HPL.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (1, 8)); (EVar 36, B47)] [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH2.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (1, 30)); (EVar 34, (1, 8)); (EVar 36, B47)] [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH2.
Qed.

(* [comment removed for export] *)
Definition objs_ok (T RI TP TSDA PT : Z) : Prop :=
  2^46 <= SPa <= 2^47 /\ ((4096 <= T /\ T + 4096 <= 65536) \/ 6529024 <= T) /\ T + 4096 <= SPa - 256 /\ 4194304 <= RI /\ RI + 128 <= SPa - 256 /\ (RI + 128 <= T \/ T + 4096 <= RI) /\
  4096 <= TP /\ TP <= SPa - 256 /\ 1 <= TSDA /\ TSDA + 8192 <= SPa - 256 /\ 1 <= PT /\ PT + 160 <= SPa - 256.
#[using="HSPa"] Lemma sc_gpb2 : forall CA RI RB S16 TP K TSDA PT T mm1 mm2 st2,
  objs_ok T RI TP TSDA PT -> CA = T + 208 -> 0 <= K <= 1023 -> 2 <= S16 <= 4096 ->
  scs_denot SEGS m (Ez R (AXF_gpb2z.VALS_gpb2 CA RI RB S16 TP K TSDA PT T mm1 mm2 st2)) (snd (fst AXF_gpb2.RES_ppb2)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA RI RB S16 TP K TSDA PT T mm1 mm2 st2 HO HCA HK HS. unfold objs_ok in HO. unfold AXF_gpb2z.VALS_gpb2.
  assert (HD : RI + 128 <= T \/ T + 4096 <= RI) by tauto.
  assert (HPL : (4096 <= T /\ T + 4096 <= 65536) \/ 6529024 <= T) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : T + 4096 <= RI) by (clear - HPL HO; lia). assert (HH := conj HPL (conj HD1 (conj HK (conj HCA (conj HS HO))))); clear HO HCA HK HS HD HD1 HPL.
    sc_refl [SPr; (EVar 32, LOW); (EVar 33, B47); (EVar 35, (2, 4096)); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, TLOW)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
             (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 33, EVar 40, 4096); (EVar 33, EVar 32, 3888)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HPL (conj HD (conj HK (conj HCA (conj HS HO))))); clear HO HCA HK HS HD HPL.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, B47); (EVar 35, (2, 4096)); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
             (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 40, EVar 33, 128); (EVar 32, EVar 33, 336)] R HSPa HSPa HH.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, B47); (EVar 35, (2, 4096)); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
             (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 33, EVar 40, 4096); (EVar 33, EVar 32, 3888)] R HSPa HSPa HH.
Qed.
#[using="HSPa"] Lemma sc_gpc1b : forall RI RB S16 NEW TP K TSDA PT T mm1 mm2,
  objs_ok T RI TP TSDA PT -> 0 <= K <= 1023 -> 2 <= S16 <= 4096 -> 4 <= NEW <= 8192 ->
  scs_denot SEGS m (Ez R (AXF_gpc1bz.VALS_gpc1b RI RB S16 NEW TP K TSDA PT T mm1 mm2)) (snd (fst AXF_gpc1b.RES_ppc1b)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros RI RB S16 NEW TP K TSDA PT T mm1 mm2 HO HK HS HN. unfold objs_ok in HO. unfold AXF_gpc1bz.VALS_gpc1b.
  assert (HD : RI + 128 <= T \/ T + 4096 <= RI) by tauto.
  assert (HPL : (4096 <= T /\ T + 4096 <= 65536) \/ 6529024 <= T) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : T + 4096 <= RI) by (clear - HPL HO; lia). assert (HH := conj HPL (conj HD1 (conj HK (conj HS (conj HN HO))))); clear HO HK HS HN HD HD1 HPL.
    sc_refl [SPr; (EVar 32, B47); (EVar 34, (2, 4096)); (EVar 35, (4, 8192)); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, TLOW)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 32, EVar 40, 4096)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HPL (conj HD (conj HK (conj HS (conj HN HO))))); clear HO HK HS HN HD HPL.
    + sc_refl [SPr; (EVar 32, B47); (EVar 34, (2, 4096)); (EVar 35, (4, 8192)); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 40, EVar 32, 128)] R HSPa HSPa HH.
    + sc_refl [SPr; (EVar 32, B47); (EVar 34, (2, 4096)); (EVar 35, (4, 8192)); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 32, EVar 40, 4096)] R HSPa HSPa HH.
Qed.
#[using="HSPa"] Lemma sc_gpc2 : forall RI S16 NEW FA REC16 n, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 13))) = 0 ->
  2^46 <= SPa <= 2^47 /\ 4194304 <= RI /\ RI + 128 <= SPa - 256 /\ NEW * (16 * S16) <= 262144 /\ 2 <= S16 <= 4096 /\ 4 <= NEW <= 8192 /\ 1 <= n <= 8 /\ n <= NEW ->
  scs_denot SEGS m (Ez R (AXF_gpc2z.VALS_gpc2 RI S16 NEW FA REC16 n)) (snd (fst AXF_gpc2.RES_ppc2)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros RI S16 NEW FA REC16 n HX HH. unfold AXF_gpc2z.VALS_gpc2.
  sc_refl [SPr; (EVar 13, (0,0)); (EVar 32, B47); (EVar 33, (2, 4096)); (EVar 34, (4, 8192)); (EVar 37, (1, 8));
           (EMd M_MUL (EVar 34) (EMd M_MUL (ELit 16) (EVar 33)), (0, 262144))]
          [(EVar 2, EVar 32, 384); (EVar 34, EVar 37, 0)] R HSPa HX HH.
Qed.
End SCG.
