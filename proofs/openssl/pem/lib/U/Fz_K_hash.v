(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

Definition FZ_LH_STRHASH : Z := 0xe99dc.
Definition FZ_PROPERTY_HASH : Z := 0xf0a5c.
Definition FZ_PROP_HASHW : Z := 0xf0fa4.

(* [comment removed for export] *)
Definition sh_r (c : Z) : Z := Z.land (Z.lxor (Z.shiftr c 2) c) 15.
Definition sh_mix (ret n c : Z) : Z :=
  Z.lxor ((Z.lor (Z.shiftr ret (32 - sh_r c)) ((Z.shiftl ret (sh_r c)) mod 2 ^ 64)) mod 2 ^ 32) (((n + c) * (n + c)) mod 2 ^ 64).
Fixpoint sh_loop (ret n : Z) (s : list byte) : Z :=
  match s with
  | [] => ret
  | c :: s' => sh_loop (sh_mix ret n (bv_unsigned c)) (n + 256) s'
  end.
Definition sh_fin (ret : Z) : Z := Z.lxor (Z.shiftr ret 16) ret.
Definition lh_strhash (s : list byte) : Z := sh_fin (sh_loop 0 256 s).

Lemma sh_mix_range : forall ret n c, 0 <= sh_mix ret n c < 2 ^ 64.
Proof.
  intros ret n c. unfold sh_mix.
  pose proof (Z.mod_pos_bound (Z.lor (Z.shiftr ret (32 - sh_r c)) ((Z.shiftl ret (sh_r c)) mod 2 ^ 64)) (2 ^ 32) ltac:(lia)) as H1.
  pose proof (Z.mod_pos_bound ((n + c) * (n + c)) (2 ^ 64) ltac:(lia)) as H2.
  apply Z_lxor_range; lia.
Qed.

Lemma sh_loop_range : forall s ret n, 0 <= ret < 2 ^ 64 -> 0 <= sh_loop ret n s < 2 ^ 64.
Proof. induction s as [|c s IH]; intros ret n H; cbn [sh_loop]; [exact H|]. apply IH. apply sh_mix_range. Qed.

Lemma lh_strhash_range : forall s, 0 <= lh_strhash s < 2 ^ 64.
Proof.
  intros s. unfold lh_strhash, sh_fin. pose proof (sh_loop_range s 0 256 ltac:(lia)) as H.
  apply Z_lxor_range; [| lia]. split; [apply Z.shiftr_nonneg; lia|].
  apply Z.le_lt_trans with (sh_loop 0 256 s); [| lia]. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma sh_r_range : forall c, 0 <= sh_r c <= 15.
Proof.
  intros c. unfold sh_r. change 15 with (2 ^ 4 - 1) at 1 2. rewrite zb_land_mask by lia.
  pose proof (Z.mod_pos_bound (Z.lxor (Z.shiftr c 2) c) (2 ^ 4) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma sh_mix_eq : forall ret n c,
  Z.lxor ((Z.lor (Z.shiftr ret ((bv_swrap 32 (32 - Z.land (Z.lxor (Z.shiftr c 2) c) 15) mod 2 ^ 64) mod 64))
                 ((Z.shiftl ret (Z.land (Z.lxor (Z.shiftr c 2) c) 15 mod 64)) mod 2 ^ 64)) mod 2 ^ 32)
         (((n + c) * (n + c)) mod 2 ^ 64)
  = sh_mix ret n c.
Proof.
  intros ret n c. unfold sh_mix. fold (sh_r c). pose proof (sh_r_range c) as R.
  replace ((bv_swrap 32 (32 - sh_r c) mod 2 ^ 64) mod 64) with (32 - sh_r c).
  2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
      rewrite (Z.mod_small (32 - sh_r c + 2 ^ 31)) by lia. replace (32 - sh_r c + 2 ^ 31 - 2 ^ 31) with (32 - sh_r c) by lia. rewrite (Z.mod_small _ (2 ^ 64)) by lia. rewrite Z.mod_small by lia. reflexivity. }
  rewrite (Z.mod_small (sh_r c) 64) by lia. reflexivity.
Qed.
Lemma lor_byte : forall n c, 0 <= n -> n mod 256 = 0 -> 0 <= c < 256 -> Z.lor n c = n + c.
Proof.
  intros n c Hn Hm Hc.
  assert (D : Z.land n c = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [L|G].
    - replace n with ((n / 256) * 2 ^ 8) by (change (2 ^ 8) with 256; lia). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit c i) with false; [apply Bool.andb_false_r|].
      symmetry. apply (proj2 (Z.testbit_false c i ltac:(lia))). rewrite Z.div_small; [reflexivity|]. split; [lia|].
      apply Z.lt_le_trans with 256; [lia|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.
Lemma testbit_byte_add : forall n c j, 0 <= n -> n mod 256 = 0 -> 0 <= c < 256 -> 0 <= j < 8 -> Z.testbit (n + c) j = Z.testbit c j.
Proof.
  intros n c j Hn Hm Hc Hj.
  rewrite !Z.testbit_eqb by lia.
  assert (P8 : 2 ^ 8 = 2 ^ j * 2 ^ (8 - j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  change 256 with (2 ^ 8) in Hm.
  assert (E : n + c = (n / 2 ^ 8 * 2 ^ (8 - j)) * 2 ^ j + c) by (rewrite <- Z.mul_assoc, (Z.mul_comm (2 ^ (8 - j))), <- P8; pose proof (Z.div_mod n (2 ^ 8) ltac:(lia)); lia).
  rewrite E. rewrite Z.div_add_l by lia.
  replace ((n / 2 ^ 8 * 2 ^ (8 - j) + c / 2 ^ j) mod 2) with ((c / 2 ^ j) mod 2); [reflexivity|].
  replace (2 ^ (8 - j)) with (2 * 2 ^ (8 - j - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Z.add_comm, (Z.mul_comm 2), Z.mul_assoc, Z.mod_add by lia. reflexivity.
Qed.
Lemma sh_r_of_v : forall n c, 0 <= n -> n mod 256 = 0 -> 0 <= c < 256 ->
  Z.land (Z.lxor (Z.shiftr (n + c) 2) (n + c)) 15 = sh_r c.
Proof.
  intros n c Hn Hm Hc. unfold sh_r. apply Z.bits_inj'. intros j Hj.
  rewrite !Z.land_spec, !Z.lxor_spec, !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases j 4) as [L|G].
  - rewrite !testbit_byte_add by lia. reflexivity.
  - replace (Z.testbit 15 j) with false; [rewrite !Bool.andb_false_r; reflexivity|].
    symmetry. apply (proj2 (Z.testbit_false 15 j ltac:(lia))). rewrite Z.div_small; [reflexivity|]. split; [lia|].
    apply Z.lt_le_trans with 16; [lia|]. change 16 with (2 ^ 4). apply Z.pow_le_mono_r; lia.
Qed.
Lemma sh_mix_eqU : forall ret n c, 0 <= n -> n mod 256 = 0 -> 0 <= c < 256 ->
  Z.lxor ((Z.lor (Z.shiftr ret ((bv_swrap 32 (32 - Z.land (Z.lxor (Z.shiftr (n + c) 2) (n + c)) 15) mod 2 ^ 64) mod 64))
                 ((Z.shiftl ret (Z.land (Z.lxor (Z.shiftr (n + c) 2) (n + c)) 15 mod 64)) mod 2 ^ 64)) mod 2 ^ 32)
         (((n + c) * (n + c)) mod 2 ^ 64)
  = sh_mix ret n c.
Proof.
  intros ret n c Hn Hm Hc. rewrite (sh_r_of_v n c Hn Hm Hc). exact (sh_mix_eq ret n c).
Qed.

Section StrHash.
  Variables (gp tp t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (str : list byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis STR : bytes_at usegs m A (str ++ [Z_to_bv 8 0]).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis LEN : Z.of_nat (length str) < 2 ^ 40.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ [Z_to_bv 8 0]).

  Lemma shA_bound : 0 <= A /\ A + len + 1 <= 2 ^ 64.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B. lia. Qed.

  Lemma sh_nth_lt : forall i, 0 <= i < len -> exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split; [rewrite nth_error_app1 by lia; exact E|]. split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; exact E|]. apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.
  Lemma sh_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma skipn_cons_nth : forall (l : list byte) i c, nth_error l i = Some c -> skipn i l = c :: skipn (S i) l.
  Proof. induction l as [|x l IH]; intros [|i] c H; cbn in *; try discriminate; [injection H as ->; reflexivity|]. exact (IH i c H). Qed.

  (* [comment removed for export] *)
  Definition sh_loop_post (rax spx s0x : word) (h : Z) : machine_state -> Prop :=
    fun ms' => exists t0' a0' a4' a5' a6' a7',
      ms' = MS (mkR rax spx gp tp t0' t1 t2 s0x s1 a0' (Z_to_bv 64 h) (Z_to_bv 64 (-1)) (Z_to_bv 64 32) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0xe9a54) fc None m (seg_rom usegs).

  Lemma sh_loop_walk : forall (k : nat) (i ret n : Z) (c : byte) (rax spx s0x t0 a5 a7 : word),
    Z.to_nat (len - i) = S k -> nth_error str (Z.to_nat i) = Some c -> bv_unsigned c <> 0 -> 0 <= i ->
    0 <= ret < 2 ^ 64 -> 0 <= n <= 256 * (i + 1) -> n mod 256 = 0 ->
    evt usegs (sh_loop_post rax spx s0x (sh_loop ret n (skipn (Z.to_nat i) str)))
      (MS (mkR rax spx gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 (A + i)) (Z_to_bv 64 ret) (Z_to_bv 64 (-1)) (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned c)) a5 (Z_to_bv 64 n) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe9a08) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i ret n c rax spx s0x t0 a5 a7 Hk NTH C0 I0 RET NB NM; pose proof shA_bound as AB;
      pose proof (bv_unsigned_in_range _ c) as CR; change (bv_modulus 8) with 256 in CR;
      assert (IL : i < len) by (apply Z.nle_gt; intros X; rewrite (proj2 (nth_error_None str (Z.to_nat i))) in NTH by lia; discriminate).
    - (* [comment removed for export] *)
      assert (Ei : i + 1 = len) by lia.
      zstep. zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?Z_to_bv_signed, ?bv_swrap_small in KU by (change (bv_half_modulus 64) with (2 ^ 63); lia). lia. } clear KU.
      zstep. if_cases KV; zify_cond KV. { exfalso. clear - KV AB IL I0. lia. } clear KV.
      zstep. rewrite ?unsigned_lit by lia. rewrite (lor_byte n (bv_unsigned c)) by lia.
      pose proof (u8ro_read usegs m A full (i + 1) (Z_to_bv 8 0) (wa (A + i + 1)) STR ltac:(rewrite Ei; exact sh_nth_len) ltac:(lia) ltac:(f_equal; lia)) as RD.
      zstep. clear RD.
      do 12 zstep. rewrite ?unsigned_lit by lia. rewrite sh_mix_eqU by lia. zstep. zstep. th_if_lit.
      apply evt_done. unfold sh_loop_post.
      rewrite (skipn_cons_nth str (Z.to_nat i) c NTH). replace (S (Z.to_nat i)) with (Z.to_nat len) by lia.
      rewrite Nat2Z.id, skipn_all. cbn [sh_loop].
      do 6 eexists. reflexivity.
    - destruct (sh_nth_lt (i + 1) ltac:(lia)) as (c2 & F2 & N2 & C2).
      zstep. zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?Z_to_bv_signed, ?bv_swrap_small in KU by (change (bv_half_modulus 64) with (2 ^ 63); lia). lia. } clear KU.
      zstep. if_cases KV; zify_cond KV. { exfalso. clear - KV AB IL I0. lia. } clear KV.
      zstep. rewrite ?unsigned_lit by lia. rewrite (lor_byte n (bv_unsigned c)) by lia.
      pose proof (u8ro_read usegs m A full (i + 1) c2 (wa (A + i + 1)) STR F2 ltac:(lia) ltac:(f_equal; lia)) as RD.
      zstep. clear RD.
      do 12 zstep. rewrite ?unsigned_lit by lia. rewrite sh_mix_eqU by lia. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. exact (C2 K). }
      rewrite (skipn_cons_nth str (Z.to_nat i) c NTH). cbn [sh_loop].
      replace (A + i + 1) with (A + (i + 1)) by lia. replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
      apply (IH (i + 1)); first [exact N2| exact C2| apply sh_mix_range| lia].
  Qed.
End StrHash.

Definition strhash_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (h lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma lh_strhash_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (A lo : Z) (str : list byte),
  a0 = Z_to_bv 64 A -> 0 < A -> bytes_at usegs m A (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
  stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (strhash_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (lh_strhash str) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_LH_STRHASH) fc None m (seg_rom usegs)).
Proof.
  intros until str. intros -> A0 STR NONUL NE LEN SEP ST LO0 LO MI. unfold FZ_LH_STRHASH.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct str as [|c0 str'] eqn:ES; [congruence|]. rewrite <- ES in *. clear NE.
  assert (C0 : bv_unsigned c0 <> 0). { intros X. apply NONUL. rewrite ES. left. apply bv_eq. rewrite X. reflexivity. }
  assert (N0 : nth_error str 0 = Some c0) by (rewrite ES; reflexivity).
  zstep. th_frame 16%nat [8; 8]%nat ST. do 3 ths.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  pose proof (u8ro_read usegs _ A (str ++ [Z_to_bv 8 0]) 0 c0 _ STR ltac:(rewrite nth_error_app1 by (rewrite ES; cbn; lia); exact N0) ltac:(lia) ltac:(rewrite Z.add_0_r; reflexivity)) as RD.
  zstep. clear RD. zstep. if_cases K1; zify_cond K1. { exfalso. exact (C0 K1). }
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
  eapply evt_cut.
  { eapply (sh_loop_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 A str STR NONUL LEN (length str') 0 0 256 c0);
      [rewrite ES; cbn [length]; lia| exact N0| exact C0| lia| lia| lia| reflexivity]. }
  intros ms' (t0' & a0' & a4' & a5' & a6' & a7' & ->). replace (skipn (Z.to_nat 0) str) with str by reflexivity.
  pose proof (sh_loop_range str 0 256 ltac:(lia)) as HR.
  zstep. zstep. zstep.
  do 2 ths. zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  zstep.
  apply evt_done. unfold strhash_post, lh_strhash, sh_fin. do 9 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

(* [comment removed for export] *)
Lemma prop_hashw_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (d S lo : Z) (str : list byte),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 FZ_PROPERTY_HASH ->
  rw_cells usegs m d [C8 (Z_to_bv 64 S)] -> (d + 8 <= lo \/ bv_unsigned sp <= d) ->
  0 < S -> bytes_at usegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) ->
  stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m -> 0 < d -> d mod 8 = 0 ->
  evt usegs (strhash_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (lh_strhash str) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PROP_HASHW) fc None m (seg_rom usegs)).
Proof.
  intros until str. intros -> -> DC DSEP S0 STR NONUL NE LEN SEP ST LO0 LO MI D0 DAL. unfold FZ_PROP_HASHW, FZ_PROPERTY_HASH.
  pose proof (rw_cells_bound _ _ _ _ DC) as DB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. do 3 ths. do 2 ths. zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  zstep.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. do 3 ths. zstep. ubs_if. zstep. zstep. ubs_if. zstep. do 2 ths. zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  zstep.
  call (lh_strhash_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S lo str). all: try first [eassumption | reflexivity | lia].
  finish.
Qed.
