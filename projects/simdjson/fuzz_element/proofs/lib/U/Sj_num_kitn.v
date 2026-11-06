(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition limbz (bs : list byte) (k : Z) : word := le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs)).

Lemma list_eq_nth_error : forall (A : Type) (a b : list A), length a = length b ->
  (forall i, (i < length a)%nat -> nth_error a i = nth_error b i) -> a = b.
Proof.
  intros A a. induction a as [|x a IH]; intros b L H; destruct b as [|y b]; cbn in L; try lia; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(cbn; lia)). cbn in H. congruence.
  - apply IH; [lia|]. intros i Hi. apply (H (S i)). cbn. lia.
Qed.

Lemma slice_upd_other : forall (bs xs : list byte) (j k n : nat),
  (j + length xs <= length bs)%nat -> (k + n <= length bs)%nat -> (j + length xs <= k \/ k + n <= j)%nat ->
  firstn n (skipn k (upd_bytes bs j xs)) = firstn n (skipn k bs).
Proof.
  intros bs xs j k n Hj Hk D.
  apply list_eq_nth_error.
  - rewrite !length_firstn, !length_skipn, upd_bytes_length by lia. reflexivity.
  - intros i Hi. rewrite length_firstn, length_skipn, upd_bytes_length in Hi by lia.
    rewrite !nth_error_firstn. destruct (Nat.ltb_spec0 i n); [|reflexivity].
    rewrite !nth_error_skipn. rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 j (k + i)); destruct (Nat.ltb_spec0 (k + i) (j + length xs)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Lemma slice_upd_same : forall (bs xs : list byte) (j : nat),
  (j + length xs <= length bs)%nat -> firstn (length xs) (skipn j (upd_bytes bs j xs)) = xs.
Proof.
  intros bs xs j Hj.
  apply list_eq_nth_error.
  - rewrite length_firstn, length_skipn, upd_bytes_length by lia. lia.
  - intros i Hi. rewrite length_firstn, length_skipn, upd_bytes_length in Hi by lia.
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i (length xs)); [|exfalso; lia].
    rewrite nth_error_skipn. rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 j (j + i)); destruct (Nat.ltb_spec0 (j + i) (j + length xs)); cbn [andb]; try (exfalso; lia).
    f_equal. lia.
Qed.

Lemma limbz_upd_same : forall bs k (v : word), (0 <= k)%Z -> (k + 8 <= Z.of_nat (length bs))%Z ->
  limbz (upd_bytes bs (Z.to_nat k) (le8 v)) k = v.
Proof.
  intros bs k v Hk Hl. unfold limbz.
  pose proof (slice_upd_same bs (le8 v) (Z.to_nat k)) as E. rewrite length_le8 in E. rewrite E by lia.
  apply le_bytes_to_word_le8.
Qed.

Lemma limbz_upd_other : forall bs xs j k, (0 <= j)%Z -> (0 <= k)%Z ->
  (j + Z.of_nat (length xs) <= Z.of_nat (length bs))%Z -> (k + 8 <= Z.of_nat (length bs))%Z ->
  (j + Z.of_nat (length xs) <= k \/ k + 8 <= j)%Z ->
  limbz (upd_bytes bs (Z.to_nat j) xs) k = limbz bs k.
Proof.
  intros bs xs j k Hj Hk Lj Lk D. unfold limbz. f_equal. apply slice_upd_other; lia.
Qed.

Lemma limbz_eq : forall bs k k', k = k' -> limbz bs k = limbz bs k'.
Proof. intros; subst; reflexivity. Qed.

Lemma limbz_u64s : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  limbz (u64s ws) (8 * Z.of_nat i) = nth i ws (Z_to_bv 64 0).
Proof.
  intros ws i Hi. unfold limbz.
  destruct (nth_error ws i) as [w|] eqn:E; [|apply nth_error_None in E; lia].
  rewrite (nth_error_nth _ _ _ E).
  destruct (u64s_split ws i w E) as (pre & post & _ & _ & S & LP). rewrite S.
  replace (Z.to_nat (8 * Z.of_nat i)) with (length (u64s pre)) by lia.
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app]. change (skipn 0 (le8 w ++ u64s post)) with (le8 w ++ u64s post).
  rewrite firstn_app. rewrite length_le8. cbn [Nat.sub firstn]. rewrite app_nil_r.
  rewrite firstn_all2 by (rewrite length_le8; lia). apply le_bytes_to_word_le8.
Qed.

Definition bignorm (ws : list word) (len : Z) : Prop :=
  (len = 0 \/ bv_unsigned (nth (Z.to_nat (len - 1)) ws (Z_to_bv 64 0)) <> 0)%Z.
Definition bignorm_b (bs : list byte) (len : Z) : Prop :=
  (len = 0 \/ bv_unsigned (limbz bs (8 * (len - 1))) <> 0)%Z.

Lemma bignorm_b_of : forall ws len, bignorm ws len -> (0 <= len <= Z.of_nat (length ws))%Z -> bignorm_b (u64s ws) len.
Proof.
  intros ws len [E|NZ] L; [left; exact E|]. destruct (Z.eq_dec len 0) as [E|NE]; [left; exact E|]. right.
  replace (8 * (len - 1))%Z with (8 * Z.of_nat (Z.to_nat (len - 1)))%Z by lia. rewrite limbz_u64s by lia. exact NZ.
Qed.
Lemma bignorm_of_b : forall ws len, bignorm_b (u64s ws) len -> (0 <= len <= Z.of_nat (length ws))%Z -> bignorm ws len.
Proof.
  intros ws len [E|NZ] L; [left; exact E|]. destruct (Z.eq_dec len 0) as [E|NE]; [left; exact E|]. right.
  replace (8 * (len - 1))%Z with (8 * Z.of_nat (Z.to_nat (len - 1)))%Z in NZ by lia. rewrite limbz_u64s in NZ by lia. exact NZ.
Qed.

Definition hi64u_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' tb,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(T, T + 1)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' T [C1 (Z_to_bv 8 tb)] /\ (0 <= tb <= 1)%Z.
Definition hi64u_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X T : Z) ws len (tb0 : byte),
  mem_inv segs m -> bigint_at segs m X ws len -> bignorm ws len -> (X + 498 <= 2^64)%Z ->
  rw_cells segs m T [C1 tb0] -> (0 <= T)%Z -> (T + 1 <= X)%Z ->
  evt segs (hi64u_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 T) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Ltac num_abstract_data_p :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_swrap 32 ?t)] =>
      match t with
      | context [bv_unsigned ?v] => num_is_data_var v
      end;
      let z := fresh "z" in let Hz := fresh "Hz" in
      assert (Hz : (-2147483648 <= bv_swrap 32 t < 2147483648)%Z) by (rewrite bv_swrap32; apply swrap32_range);
      generalize Hz; generalize (bv_swrap 32 t); clear Hz; intros z Hz
  | |- context [Z_to_bv 64 ?t] =>
      match t with
      | context [bv_unsigned ?v] => num_is_data_var v
      end;
      let w := fresh "w" in generalize (Z_to_bv 64 t); intro w;
      let M := fresh "DM" in assert (M : IsData w) by exact I
  end.
Lemma shr_u64_range : forall (w : word) n, (0 <= n <= 64)%Z -> (0 <= Z.shiftr (bv_unsigned w) n < 2 ^ (64 - n))%Z.
Proof.
  intros w n Hn. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (Z.of_N 64) with 64%Z in R.
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (64 - n))%Z with 64%Z by lia. lia.
Qed.

Ltac num_abstract_bits :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Z.b2z ?b)] =>
      match b with context [bv_unsigned ?v] => num_is_data_var v end;
      let t := fresh "tb" in let Ht := fresh "Htb" in
      assert (Ht : (0 <= Z.b2z b <= 1)%Z) by (destruct b; cbn; lia);
      generalize Ht; generalize (Z.b2z b); clear Ht; intros t Ht
  | |- context [Z.shiftr (bv_unsigned ?w) ?n] =>
      num_is_data_var w;
      lazymatch n with 48%Z => idtac | 49%Z => idtac | 50%Z => idtac | 51%Z => idtac | 52%Z => idtac | 53%Z => idtac | 54%Z => idtac | 55%Z => idtac
                     | 56%Z => idtac | 57%Z => idtac | 58%Z => idtac | 59%Z => idtac | 60%Z => idtac | 61%Z => idtac | 62%Z => idtac | 63%Z => idtac end;
      let B := eval vm_compute in (2 ^ (64 - n))%Z in
      let t := fresh "hf" in let Ht := fresh "Hhf" in
      assert (Ht : (0 <= Z.shiftr (bv_unsigned w) n < B)%Z) by (apply (shr_u64_range w n); lia);
      generalize Ht; generalize (Z.shiftr (bv_unsigned w) n); clear Ht; intros t Ht
  end.
Ltac num_abstract_data_u := num_abstract_bits; num_abstract_data_p.

Lemma lor_bit : forall a b, (0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= Z.lor a b <= 1)%Z.
Proof. intros a b Ha Hb. assert (A : (a = 0 \/ a = 1)%Z) by lia. assert (B : (b = 0 \/ b = 1)%Z) by lia. destruct A as [A|A], B as [B|B]; subst a b; vm_compute; split; discriminate. Qed.

Ltac ukb2z :=
  repeat match goal with
  | |- context [Z.b2z ?b] =>
      lazymatch b with
      | context [bv_unsigned _] => fail
      | _ => let v := eval vm_compute in (Z.b2z b) in
             lazymatch v with 0%Z => idtac | 1%Z => idtac end;
             change (Z.b2z b) with v
      end
  end.
Ltac ukstep :=
  zstep; nnorm;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (Z_to_le_bytes ?n ?z)) _) =>
      lazymatch n with
      | 8%nat => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
      | 4%nat => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
      | 2%nat => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
      | 1%nat => change (Z_to_le_bytes 1 z) with (le1 (Z_to_bv 64 z))
      end;
      mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (le1 ?v)) _) =>
      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => num_store_done
  | |- _ => idtac
  end.
Ltac ukwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "ukwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (ukstep; ukwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; unorm_in H;
          first [ solve [exfalso; lia] | ukwalk_fuel n' K ]
      end
  end.
Ltac ukwalk K := ukwalk_fuel 200%nat K.

Ltac fold_limbz :=
  repeat match goal with
  | |- context [le_bytes_to_word (firstn 8 (skipn (Z.to_nat ?k) ?bs))] => change (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs))) with (limbz bs k)
  | H : context [le_bytes_to_word (firstn 8 (skipn (Z.to_nat ?k) ?bs))] |- _ => change (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs))) with (limbz bs k) in H
  end.

Ltac u_clz_dead NB KB :=
  exfalso; fold_limbz; destruct NB as [NB|NB]; [lia|]; apply NB;
  lazymatch type of KB with
  | bv_unsigned (limbz ?bs ?k) = _ =>
      lazymatch goal with |- bv_unsigned (limbz bs ?k') = _ => replace k' with k by lia; exact KB end
  end.

Lemma num_cb1_c1 : forall segs (m : mem) A bs, rw_cells segs m A [CB 1 bs] -> exists b, rw_cells segs m A [C1 b].
Proof.
  intros segs m A bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
  destruct bs as [|b [|? ?]]; cbn in HL; try lia. exists b.
  split; [split|]; [cbn; split; exact I | exact Hb | exact Hw].
Qed.

Lemma u8arr_of_u64arr_s : forall segs (m : mem) X ws, u64arr segs m X ws -> u8arr segs m X (u64s ws).
Proof.
  intros segs m X ws [HB HW]. split; [exact HB|]. rewrite u64s_length.
  replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact HW.
Qed.
Lemma u64arr_of_u8arr_s : forall segs (m : mem) X bs, u8arr segs m X bs -> length bs = 496%nat ->
  exists ws, length ws = 62%nat /\ u64s ws = bs /\ u64arr segs m X ws.
Proof.
  intros segs m X bs [HB HW] L. destruct (u64s_of_bytes 62 bs L) as (ws & LW & EW). exists ws. split; [exact LW|]. split; [exact EW|].
  split; [rewrite EW; exact HB|]. rewrite L in HW. rewrite LW. exact HW.
Qed.

Definition biguN_post_g (STACK : Z) (G : word -> list word -> Z -> Prop) (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ stk segs m' lo (bv_unsigned sp) /\ G a0 ws' len'.

Lemma biguN_post_weak : forall STACK G segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m ms,
  biguN_post_g STACK G segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m ms ->
  bigu_post_g STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m ms.
Proof.
  intros until ms. intros (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & ws' & len' & E & H1 & H2 & H3 & H4 & H5 & _).
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', ws', len'. repeat (split; [assumption|]). assumption.
Qed.

Definition p5uN_G (ws : list word) (len e : Z) : word -> list word -> Z -> Prop :=
  fun a0 ws' len' => bignorm ws len -> (len + 15 <= 62)%Z -> (0 <= e <= 328)%Z ->
                     a0 = Z_to_bv 64 1 /\ bignorm ws' len' /\ (len' <= len + 15)%Z.
Definition p5uN_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + P5U_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z ->
  (-2147483648 <= e < 2147483648)%Z ->
  evt segs (biguN_post_g P5U_STACK (p5uN_G ws len e) segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition shluN_G (ws : list word) (len : Z) (n : word) : word -> list word -> Z -> Prop :=
  fun a0 ws' len' => bignorm ws len -> (len + bv_unsigned n / 64 + 1 <= 62)%Z ->
                     a0 = Z_to_bv 64 1 /\ bignorm ws' len' /\ (len' <= len + bv_unsigned n / 64 + 1)%Z.
Definition shluN_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + SHLU_STACK <= bv_unsigned sp)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z -> (0 < X)%Z -> (X mod 8 = 0)%Z ->
  evt segs (biguN_post_g SHLU_STACK (shluN_G ws len a1) segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition pdcu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + PDCU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z -> (X mod 8 = 0)%Z ->
  bignorm ws len -> (len + 21 <= 62)%Z -> (0 <= e <= 328)%Z ->
  evt segs (bigu_post_g PDCU_STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Definition NDCU_RANGE : Z := 1048576.
Definition ndcu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X p2 e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + NDCU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z ->
  (- NDCU_RANGE <= p2 <= NDCU_RANGE)%Z -> (- NDCU_RANGE <= e <= NDCU_RANGE)%Z ->
  evt segs (bigu_post_g NDCU_STACK segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 (Z_to_bv 64 (p2 mod 4294967296)) (Z_to_bv 64 e) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Lemma swrap32_zext_add : forall p k, (-2147483648 <= p + k < 2147483648)%Z -> bv_swrap 32 (p mod 4294967296 + k) = (p + k)%Z.
Proof. intros p k H. rewrite bv_swrap32. unfold swrap32. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_zext : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (p mod 4294967296) = p.
Proof. intros p H. rewrite bv_swrap32. unfold swrap32. Z.div_mod_to_equations. lia. Qed.

Definition PMU_NORM_DG : Z := 500.
Definition pmu_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X IP IL FPT FL lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len' dg',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - PMU_STACK, bv_unsigned sp); (X, X + 498); (X + 504, X + 512)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ rw_cells segs m' (X + 504) [C8 (Z_to_bv 64 dg')]
    /\ rw_cells segs m' (X - 40) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)]
    /\ stk segs m' lo (bv_unsigned sp)
    /\ (0 <= dg' <= 770)%Z /\ (19 * len' <= 2 * dg' + 76)%Z /\ (dg' < PMU_NORM_DG -> bignorm ws' len')%Z.
Definition pmu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X A IP IL FPT FL lo : Z) ws (txt jd : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + PMU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bigint_at segs m X ws 0 -> (bv_unsigned sp <= X - 40)%Z -> (X + 512 <= 2^64)%Z ->
  rw_cells segs m (X + 504) [CB 8 jd] ->
  rw_cells segs m (X - 40) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z -> (0 < A)%Z ->
  pm_spans_ok A txt IP IL FPT FL ->
  evt segs (pmu_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X IP IL FPT FL lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (X - 72)) (Z_to_bv 64 PM_MAXD) (Z_to_bv 64 (X + 504)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Lemma bignorm_b_upd_other : forall bs xs j len, bignorm_b bs len -> (0 <= j)%Z -> (j + Z.of_nat (length xs) <= 8 * (len - 1))%Z ->
  (8 * len <= Z.of_nat (length bs))%Z -> bignorm_b (upd_bytes bs (Z.to_nat j) xs) len.
Proof.
  intros bs xs j len [E|NZ] Hj Hk Hl; [left; exact E|]. right. rewrite limbz_upd_other; [exact NZ | lia ..].
Qed.
Lemma bignorm_b_upd_top : forall bs (v : word) k len, (1 <= len)%Z -> (8 * len <= Z.of_nat (length bs))%Z -> k = (8 * (len - 1))%Z ->
  bv_unsigned v <> 0%Z -> bignorm_b (upd_bytes bs (Z.to_nat k) (le8 v)) len.
Proof. intros bs v k len H1 Hl -> NZ. right. rewrite limbz_upd_same by lia. exact NZ. Qed.

Lemma bignorm_b_push : forall bs (v : word) k len, (0 <= len)%Z -> (8 * (len + 1) <= Z.of_nat (length bs))%Z -> k = (8 * len)%Z ->
  bv_unsigned v <> 0%Z -> bignorm_b (upd_bytes bs (Z.to_nat k) (le8 v)) (len + 1).
Proof. intros bs v k len H0 Hl -> NZ. apply bignorm_b_upd_top; [lia | lia | lia | exact NZ]. Qed.

Lemma bignorm_b_mul_nocarry : forall bs k len (ys c : word),
  bignorm_b bs len -> (1 <= len)%Z -> (8 * len <= Z.of_nat (length bs))%Z -> k = (8 * (len - 1))%Z -> (0 < bv_unsigned ys)%Z ->
  ((Z.shiftr (bv_unsigned (limbz bs k) * bv_unsigned ys) 64 +
    Z.b2z ((bv_unsigned (limbz bs k) * bv_unsigned ys + bv_unsigned c) mod 18446744073709551616 <?
           (bv_unsigned (limbz bs k) * bv_unsigned ys) mod 18446744073709551616)) mod 18446744073709551616 = 0)%Z ->
  bignorm_b (upd_bytes bs (Z.to_nat k) (le8 (Z_to_bv 64 (bv_unsigned (limbz bs k) * bv_unsigned ys + bv_unsigned c)))) len.
Proof.
  intros bs k len ys c [E|NZ] H1 Hl -> HY H; [exfalso; lia|].
  apply bignorm_b_upd_top; [lia | lia | reflexivity|].
  rewrite unsigned_lit_wrap. change (2 ^ 64)%Z with 18446744073709551616%Z.
  pose proof (bv_unsigned_in_range 64 (limbz bs (8 * (len - 1)))) as RA. pose proof (bv_unsigned_in_range 64 ys) as RY.
  pose proof (bv_unsigned_in_range 64 c) as RC. unfold bv_modulus in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in *.
  apply small_mul_top_nz; [lia | lia | lia | exact H].
Qed.

Ltac unorm_in_n H :=
  repeat match type of H with
  | context [Z.shiftl ?k 48 mod 18446744073709551616] => rewrite (shl48_small k) in H by lia
  | context [Z.land ?x 255] => rewrite (Z.land_ones x 8 ltac:(lia) : Z.land x 255 = x mod 2 ^ 8)%Z in H
  | context [Z.b2z (?a <? ?b)] =>
      first [ replace (a <? b)%Z with true in H by (symmetry; apply Z.ltb_lt; lia)
            | replace (a <? b)%Z with false in H by (symmetry; apply Z.ltb_ge; lia) ];
      cbn [Z.b2z] in H
  | context [Z.lxor ?a ?b] =>
      lazymatch a with 0%Z => idtac | 1%Z => idtac end; lazymatch b with 0%Z => idtac | 1%Z => idtac end;
      let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  end.

Definition lafuN_G (len ny st : Z) : word -> list word -> Z -> Prop :=
  fun a0 ws' len' => (len <= 61)%Z -> (ny + st <= 61)%Z -> a0 = Z_to_bv 64 1 /\ (len' <= Z.max len (ny + st) + 1)%Z /\ (Z.max len (ny + st) <= len')%Z.
Definition lafuN_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X Y ny st lo : Z) ws len (ybs : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + LAFU_STACK <= bv_unsigned sp)%Z ->
  bigint_at segs m X ws len -> (X + 498 <= 2^64)%Z ->
  bytes_at segs m Y ybs -> Z.of_nat (length ybs) = (8 * ny)%Z -> (bv_unsigned sp <= Y)%Z -> (Y + 8 * ny <= X)%Z -> (0 < Y)%Z -> (Y mod 8 = 0)%Z ->
  (0 <= ny <= 62)%Z -> (0 <= st <= 62)%Z ->
  evt segs (biguN_post_g LAFU_STACK (lafuN_G len ny st) segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).
Definition lmuN_G (len ny : Z) : word -> list word -> Z -> Prop :=
  fun a0 ws' len' => (len + ny + 1 <= 62)%Z -> a0 = Z_to_bv 64 1 /\ bignorm ws' len' /\ (len' <= len + ny + 1)%Z.
Definition lmuN_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X Y ny lo : Z) ws len (ybs : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + LMU_STACK <= bv_unsigned sp)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z -> (X + 498 <= 2^64)%Z ->
  bytes_at segs m Y ybs -> Z.of_nat (length ybs) = (8 * ny)%Z -> (Y + 8 * ny <= lo)%Z -> (0 < Y)%Z -> (Y mod 8 = 0)%Z -> (0 <= ny <= 62)%Z ->
  evt segs (biguN_post_g LMU_STACK (lmuN_G len ny) segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Lemma bignorm_b_shl_nocarry : forall bs k len (p sh : Z),
  bignorm_b bs len -> (1 <= len)%Z -> (8 * len <= Z.of_nat (length bs))%Z -> k = (8 * (len - 1))%Z -> (1 <= sh <= 63)%Z ->
  (Z.shiftr (bv_unsigned (limbz bs k)) ((64 - sh) mod 64) = 0)%Z ->
  bignorm_b (upd_bytes bs (Z.to_nat k) (le8 (Z_to_bv 64 (Z.lor (Z.shiftl (bv_unsigned (limbz bs k)) (sh mod 64) mod 18446744073709551616) p)))) len.
Proof.
  intros bs k len p sh [E|NZ] H1 Hl -> Hs H; [exfalso; lia|].
  apply bignorm_b_upd_top; [lia | lia | reflexivity|].
  rewrite unsigned_lit_wrap. change (2 ^ 64)%Z with 18446744073709551616%Z.
  pose proof (bv_unsigned_in_range 64 (limbz bs (8 * (len - 1)))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RA.
  apply shl_top_nz; [lia | lia | exact H].
Qed.
