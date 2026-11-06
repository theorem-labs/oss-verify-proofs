(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk Frame WalkTac RefMemcpyLib.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Section FIN.
  Context (segs : list Segment) (mem rom : word -> option byte) (ret : word) (R : bvmap 5 word).

  Definition FIN (P : word) (regs : bvmap 5 word) : Prop :=
    exists regs', msteps segs (mkst regs P mem rom) (mkst regs' ret mem rom)
      /\ keeps_cs R regs'.

  Lemma fin_steps : forall (P Q : word) regs regs1,
    msteps segs (mkst regs P mem rom) (mkst regs1 Q mem rom) ->
    FIN Q regs1 -> FIN P regs.
  Proof.
    intros P Q regs regs1 Hrun (regs' & Hrun' & K).
    exists regs'. split; [eapply msteps_trans; eassumption | exact K].
  Qed.

  Lemma fin_done : forall regs, keeps_cs R regs -> FIN ret regs.
  Proof. intros regs K. exists regs. split; [apply mst_refl | exact K]. Qed.

  Lemma fin_ret : forall (P : word) regs regs1,
    msteps segs (mkst regs P mem rom) (mkst regs1 ret mem rom) ->
    keeps_cs R regs1 -> FIN P regs.
  Proof. intros P regs regs1 Hrun K. exists regs1. split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma fin_branch : forall (P : word) regs w c (rs1 rs2 : reg) (imm : bv 13) (v1 v2 : word),
    fetch_word segs P = Some w -> is_ecall w = false ->
    decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = v1 -> getr regs rs2 = v2 ->
    (branch_taken c v1 v2 = true -> FIN (btgt P (bv_signed imm)) regs) ->
    (branch_taken c v1 v2 = false -> FIN (v_addi P 4) regs) ->
    FIN P regs.
  Proof.
    intros P regs w c rs1 rs2 imm v1 v2 Hf He Hd H1 H2 Htk Hft.
    destruct (branch_taken c v1 v2) eqn:Hb.
    - destruct (Htk eq_refl) as (regs' & Hrun & K). exists regs'. split; [|exact K].
      eapply mst_step; [reflexivity | | exact Hrun].
      apply (step_branch_tk_gen segs regs P mem rom w c rs1 rs2 imm Hf He Hd).
      rewrite H1, H2. exact Hb.
    - destruct (Hft eq_refl) as (regs' & Hrun & K). exists regs'. split; [|exact K].
      eapply mst_step; [reflexivity | | exact Hrun].
      apply (step_branch_ft_gen segs regs P mem rom w c rs1 rs2 imm Hf He Hd).
      rewrite H1, H2. exact Hb.
  Qed.
End FIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition envl (regs : bvmap 5 word) (L : list (reg * word)) : Prop :=
  forall r v, In (r, v) L -> getr regs r = v.

Lemma envl_upd : forall regs L (rd : reg) x,
  envl regs L -> ~ In rd (map fst L) -> envl (regupd regs rd x) L.
Proof.
  intros regs L rd x E Hn r v Hin.
  rewrite getr_other.
  - apply E, Hin.
  - intros ->. apply Hn. rewrite in_map_iff. exists (rd, v). split; [reflexivity | exact Hin].
Qed.

Lemma envl_upd_b : forall regs L (rd : reg) x,
  envl regs L -> existsb (bv_eqb rd) (map fst L) = false -> envl (regupd regs rd x) L.
Proof.
  intros regs L rd x E Hb. apply envl_upd; [exact E|].
  intros Hin. assert (Ht : existsb (bv_eqb rd) (map fst L) = true).
  { apply existsb_exists. exists rd. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hb. discriminate Hb.
Qed.

(* [comment removed for export] *)
Lemma envl_upd_same : forall regs L (rd : reg) x,
  envl regs L -> rd <> 0%bv -> (forall v, In (rd, v) L -> v = x) -> envl (regupd regs rd x) L.
Proof.
  intros regs L rd x E Hnz Hs r v Hin.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. apply Hs, Hin.
  - rewrite getr_other by exact Hne. apply E, Hin.
Qed.

Lemma envl_get : forall regs L (r : reg) v, envl regs L -> In (r, v) L -> getr regs r = v.
Proof. intros regs L r v E Hin. apply E, Hin. Qed.

Lemma envl_nil : forall regs, envl regs [].
Proof. intros regs r v []. Qed.

Lemma envl_cons : forall regs (r : reg) v L,
  getr regs r = v -> envl regs L -> envl regs ((r, v) :: L).
Proof.
  intros regs r v L H E r' v' [Hin|Hin].
  - injection Hin as <- <-. exact H.
  - apply E, Hin.
Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac solve_envl :=
  repeat (apply envl_upd_b; [| reflexivity]); assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP2. Context {FP : PropExec.FPState}.
Lemma rdn1_grows : forall segs m m' (a : word) b,
  mem_grows m m' -> rdn segs m a 1 = Some [b] ->
  exists b', rdn segs m' a 1 = Some [b'].
Proof.
  intros segs m m' a b Hg H. cbn [rdn] in *.
  destruct (m a) as [b0|] eqn:Hm.
  - destruct (m' a) as [b1|] eqn:Hm'.
    + exists b1. reflexivity.
    + exfalso. apply (Hg a); [rewrite Hm; discriminate | exact Hm'].
  - destruct (m' a) as [b1|] eqn:Hm'.
    + exists b1. reflexivity.
    + destruct (seg_rom segs a) as [b2|]; [|discriminate H]. exists b2. reflexivity.
Qed.

Lemma rd_byte : forall segs mem (a : word) n bs (j : nat),
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs mem a n bs j H Hj.
  change (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) with (at_ a (Z.of_nat j)). rewrite <- at_nat.
  apply (rdn_nth segs mem n); assumption.
Qed.

(* [comment removed for export] *)
Lemma rd_bytes_grown : forall segs m m' (buf : word) (n : Z) bs,
  rdn segs m buf (Z.to_nat n) = Some bs -> mem_grows m m' ->
  forall i, 0 <= i < n -> exists b, rdn segs m' (Z_to_bv 64 (bv_unsigned buf + i)) 1 = Some [b].
Proof.
  intros segs m m' buf n bs H Hg i Hi.
  pose proof (rd_byte segs m buf (Z.to_nat n) bs (Z.to_nat i) H ltac:(lia)) as H1.
  rewrite Z2Nat.id in H1 by lia.
  eapply rdn1_grows; [exact Hg | exact H1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv64_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_Z : forall x k, v_addi (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof.
  intros x k. unfold v_addi. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite <- Z_to_bv64_mod, Zplus_mod_idemp_l. apply Z_to_bv64_mod.
Qed.

Lemma v_add_Zr : forall (x : word) k, v_add x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof.
  intros x k. unfold v_add. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite <- Z_to_bv64_mod, Zplus_mod_idemp_r. apply Z_to_bv64_mod.
Qed.

Lemma v_add_Zl : forall (x : word) k, v_add (Z_to_bv 64 k) x = Z_to_bv 64 (k + bv_unsigned x).
Proof.
  intros x k. unfold v_add. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite <- Z_to_bv64_mod, Zplus_mod_idemp_l. apply Z_to_bv64_mod.
Qed.

Lemma v_add_ZZ : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. rewrite v_add_Zr. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite <- Z_to_bv64_mod, Zplus_mod_idemp_l. apply Z_to_bv64_mod.
Qed.

Lemma swrap32_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  replace (2 ^ 32 `div` 2) with (2 ^ 31) by reflexivity. lia.
Qed.

Lemma swrap32_mod : forall x, bv_swrap 32 (x mod 2 ^ 64) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as E.
  replace (x mod 2 ^ 64) with ((x + 2 ^ 32 `div` 2) + (- (x / 2 ^ 64) * 2 ^ 32) * 2 ^ 32 - 2 ^ 32 `div` 2) by lia.
  replace (x + 2 ^ 32 `div` 2 + - (x `div` 2 ^ 64) * 2 ^ 32 * 2 ^ 32 - 2 ^ 32 `div` 2 + 2 ^ 32 `div` 2)
    with (x + 2 ^ 32 `div` 2 + (- (x `div` 2 ^ 64) * 2 ^ 32) * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma v_addiw_Z : forall x k, - 2 ^ 31 <= x + k < 2 ^ 31 ->
  v_addiw (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof.
  intros x k H. unfold v_addiw. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite <- swrap32_mod, Zplus_mod_idemp_l, swrap32_mod, swrap32_small by lia. reflexivity.
Qed.

Lemma v_addw_ZZ : forall x y, - 2 ^ 31 <= x + y < 2 ^ 31 ->
  v_addw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y H. unfold v_addw. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- swrap32_mod, <- Z.add_mod, swrap32_mod, swrap32_small by lia. reflexivity.
Qed.

Lemma v_subw_ZZ : forall x y, - 2 ^ 31 <= x - y < 2 ^ 31 ->
  v_subw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
  intros x y H. unfold v_subw. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- swrap32_mod, <- Zminus_mod, swrap32_mod, swrap32_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma signed_Z : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64 `div` 2) with (2 ^ 63) by reflexivity. lia.
Qed.

Lemma lts_ZZ : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold bv_lts. rewrite !signed_Z by lia. reflexivity. Qed.

Lemma ltu_ZZ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma eqb_ZZ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros. unfold bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma eqb_wZ : forall (x : word) y, 0 <= y < 2 ^ 64 -> bv_eqb x (Z_to_bv 64 y) = (bv_unsigned x =? y).
Proof. intros. unfold bv_eqb. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ltu_wZ : forall (x : word) y, 0 <= y < 2 ^ 64 -> bv_ltu x (Z_to_bv 64 y) = (bv_unsigned x <? y).
Proof. intros. unfold bv_ltu. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ltu_Zw : forall x (y : word), 0 <= x < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) y = (x <? bv_unsigned y).
Proof. intros. unfold bv_ltu. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma eqb_neg0 : forall x, - 2 ^ 64 < x < 0 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (x + 2 ^ 64)) by lia. rewrite Z.mod_0_l by lia. apply Z.eqb_neq. lia.
Qed.

(* [comment removed for export] *)
Lemma v_and_ZZ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof. intros. unfold v_and. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_or_ZZ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_andi_Z : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  v_andi (Z_to_bv 64 x) k = Z_to_bv 64 (Z.land x k).
Proof.
  intros x k Hx Hk. unfold v_andi. rewrite u_Z2bv by lia.
  replace (bv_wrap 64 k) with k by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64); lia).
  reflexivity.
Qed.

Lemma v_slliw_Z : forall x s, 0 <= x -> 0 <= s -> x * 2 ^ s < 2 ^ 31 ->
  v_slliw (Z_to_bv 64 x) s = Z_to_bv 64 (x * 2 ^ s).
Proof.
  intros x s Hx Hs Hxs. unfold v_slliw.
  assert (0 <= x * 2 ^ s) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
  assert (x <= x * 2 ^ s).
  { rewrite <- (Z.mul_1_r x) at 1. apply Z.mul_le_mono_nonneg_l; [lia|].
    apply (Z.pow_le_mono_r 2 0 s); lia. }
  rewrite u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma v_srliw_0 : forall x s, 0 <= s -> 0 <= x < 2 ^ s -> 2 ^ s <= 2 ^ 32 ->
  v_srliw (Z_to_bv 64 x) s = Z_to_bv 64 0.
Proof.
  intros x s Hs Hx Hs32. unfold v_srliw. rewrite u_Z2bv by lia.
  replace (bv_wrap 32 x) with x by (symmetry; apply bv_wrap_small; change (bv_modulus 32) with (2^32); lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
  rewrite swrap32_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addw_m31 : forall i, 0 <= i < 2 ^ 31 - 1 ->
  v_addw (Z_to_bv 64 i) (Z_to_bv 64 18446744071562067969) = Z_to_bv 64 (i + 1 - 2 ^ 31).
Proof.
  intros i Hi. unfold v_addw. rewrite !u_Z2bv by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  replace (2 ^ 32 `div` 2) with (2 ^ 31) by reflexivity.
  replace (i + 18446744071562067969 + 2 ^ 31) with ((i + 1) + 2 ^ 32 * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma v_sltu_val : forall x y, v_sltu x y = Z_to_bv 64 (if bv_ltu x y then 1 else 0).
Proof. intros. unfold v_sltu, c_ltu. destruct (bv_ltu x y); reflexivity. Qed.

Lemma v_slti_val : forall x k, v_slti x k = Z_to_bv 64 (if bv_signed x <? k then 1 else 0).
Proof. intros. unfold v_slti, zsig. destruct (bv_signed x <? k); reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_63 : forall x, 0 <= Z.land x 63 < 64.
Proof. intros x. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma land_31 : forall x, 0 <= Z.land 31 x < 32.
Proof. intros x. rewrite Z.land_comm. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma land_15 : forall x, 0 <= Z.land 15 x < 16.
Proof. intros x. rewrite Z.land_comm. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma land_7 : forall x, 0 <= Z.land 7 x < 8.
Proof. intros x. rewrite Z.land_comm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma cp_pow_le19 : forall rem, 1 <= rem <= 3 -> 2 ^ (25 - 6 * rem) <= 2 ^ 19.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.

Lemma cp_pow_step : forall rem, 1 <= rem <= 3 -> 2 ^ (25 - 6 * rem) * 64 = 2 ^ (25 - 6 * (rem - 1)).
Proof.
  intros. change 64 with (2 ^ 6). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma cp_pow_ge64 : forall rem, 1 <= rem <= 3 -> 64 <= 2 ^ (25 - 6 * (rem - 1)).
Proof. intros. change 64 with (2 ^ 6). apply Z.pow_le_mono_r; lia. Qed.

Lemma lor_range : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hp : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [apply Z.lor_eq_0_iff in E; lia|].
    pose proof (Z.lor_nonneg a b). lia. }
  apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma sp_back : forall (sp : word) k, v_addi (Z_to_bv 64 (bv_unsigned sp - k)) k = sp.
Proof.
  intros sp k. rewrite v_addi_Z. replace (bv_unsigned sp - k + k) with (bv_unsigned sp) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma keeps_cs_intro : forall R regs,
  getr regs 1 = getr R 1 -> getr regs 2 = getr R 2 -> getr regs 3 = getr R 3 -> getr regs 4 = getr R 4 ->
  getr regs 8 = getr R 8 -> getr regs 9 = getr R 9 ->
  getr regs 18 = getr R 18 -> getr regs 19 = getr R 19 -> getr regs 20 = getr R 20 ->
  getr regs 21 = getr R 21 -> getr regs 22 = getr R 22 -> getr regs 23 = getr R 23 ->
  getr regs 24 = getr R 24 -> getr regs 25 = getr R 25 -> getr regs 26 = getr R 26 ->
  getr regs 27 = getr R 27 ->
  keeps_cs R regs.
Proof.
  intros R regs ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? r Hr.
  cbv [callee_saved In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
Qed.
End WithFP2.

