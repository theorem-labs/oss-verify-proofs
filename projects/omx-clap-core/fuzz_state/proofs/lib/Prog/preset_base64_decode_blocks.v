From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memchr_c WriterSpec WriterSpecFacts.
Import ListNotations.
Open Scope Z_scope.

Definition b64r (c : Z) : Z :=
  match b64v c with Some v => 0x104a4 + v | None => 0 end.

Definition b64_M (tb : list Z) : Z := Z.of_nat (length tb) / 4 * 3 + 3.

Definition dec_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition scan_out (pad : Z) (six rest : list Z) : option (list Z) :=
  match b64_scan pad six rest with
  | Some (six', pad') => if (pad' <=? 2) && six_tail_ok six' then Some (six_bytes six') else None
  | None => None
  end.

Definition dec_ok_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo lenp q : Z) (tb bs : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' lenp (le8 (Z_to_bv 64 (Z.of_nat (length bs)))) /\
    bytes_at rsegs m' q (map (Z_to_bv 8) bs) /\
    munch [(q, q + b64_M tb); (lenp, lenp + 8)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition dec_fail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo lenp q : Z) (tb : list Z) (lb : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 q) (Z_to_bv 64 q)
                  a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14f94) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' lenp lb /\
    rw_cells rsegs m' (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) /\
    munch [(q, q + b64_M tb)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp - 96).

Definition dec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo lenp q : Z) (tb : list Z) (lb : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => match b64_dec tb with
             | Some bs => dec_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo lenp q tb bs m ms'
             | None => dec_fail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo lenp q tb lb m ms'
             end.

Lemma zxb_lit : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. cbn. lia.
Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. rewrite bv_ltu_Z, !unsigned_lit by lia. reflexivity. Qed.

Lemma lts_lit : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (a <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. assert (E : bv_half_modulus 32 = 2^31) by reflexivity. rewrite E. lia.
Qed.

Lemma addiw_lit : forall x k, 0 <= x < 2^31 -> -2^31 <= x + k < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + k)) = Z_to_bv 64 (x + k).
Proof. intros x k H1 H2. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma subw_v : forall v, 0 <= v < 64 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 (0x104a4 + v)) - 0x104a4) = v.
Proof.
  intros v Hv. rewrite unsigned_lit by lia. replace (0x104a4 + v - 0x104a4) with v by lia.
  apply swrap32_id. lia.
Qed.

Lemma ws_lem : forall c, 0 <= c <= 61 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (Z_to_bv 64 c) mod 64)))) 1))
    (Z_to_bv 64 0) = negb (b64_ws c).
Proof.
  intros c Hc. rewrite (unsigned_lit c) by lia. rewrite (Z.mod_small c 64) by lia.
  assert (A : forallb (fun n => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64
      (Z.shiftr 4294977024 (Z.of_nat n)))) 1)) (Z_to_bv 64 0)) (negb (b64_ws (Z.of_nat n)))) (seq 0 62) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat c)). rewrite Z2Nat.id in A by lia.
  apply Bool.eqb_prop. apply A. apply in_seq. lia.
Qed.

Lemma ws_big : forall c, 61 < c -> b64_ws c = false.
Proof.
  intros c H. unfold b64_ws.
  destruct (Z.eqb_spec c 32), (Z.eqb_spec c 9), (Z.eqb_spec c 10), (Z.eqb_spec c 13); try lia; reflexivity.
Qed.

Lemma memchr_ok_b64 : forall A c, memchr_ok A c 65 (map (Z_to_bv 8) b64_table).
Proof.
  intros A c. unfold memchr_ok. rewrite length_map, b64_table_length.
  destruct (find_byte c (firstn (Z.to_nat 65) (map (Z_to_bv 8) b64_table))); [left|]; lia.
Qed.

Lemma res_b64 : forall c, 1 <= c <= 255 ->
  memchr_res (bv_unsigned (Z_to_bv 64 0x104a4)) (bv_unsigned (Z_to_bv 64 c) mod 256) (bv_unsigned (Z_to_bv 64 65))
    (map (Z_to_bv 8) b64_table) = b64r c.
Proof.
  intros c Hc. rewrite !unsigned_lit by lia. rewrite (Z.mod_small c 256) by lia.
  assert (A : forallb (fun n => memchr_res 0x104a4 (Z.of_nat n) 65 (map (Z_to_bv 8) b64_table) =? b64r (Z.of_nat n))
      (seq 1 255) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat c)). rewrite Z2Nat.id in A by lia.
  apply Z.eqb_eq. apply A. apply in_seq. lia.
Qed.

Lemma lor_add64 : forall x y, 0 <= x < 64 -> 0 <= y -> y mod 64 = 0 -> Z.lor x y = x + y.
Proof.
  intros x y Hx Hy Hm.
  assert (L : Z.land x y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 6).
    - replace (Z.testbit y i) with false; [apply andb_false_r|].
      symmetry. rewrite <- (Z.mod_pow2_bits_low y 6 i) by lia. change (2^6) with 64. rewrite Hm. apply Z.bits_0.
    - replace (Z.testbit x i) with false; [reflexivity|].
      symmetry. rewrite <- (Z.mod_small x 64) by lia. change 64 with (2^6). apply Z.mod_pow2_bits_high. lia. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma wacc : forall (w : word) v, 0 <= v < 64 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 v))
    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned w) 6)))))) mod 4096
  = (bv_unsigned w mod 64) * 64 + v.
Proof.
  intros w v Hv. rewrite (unsigned_lit v) by lia.
  pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw. change (2 ^ Z.of_N 64) with (2^64) in Rw.
  set (W := bv_unsigned w) in *.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^6) with 64.
  rewrite (unsigned_lit_wrap (bv_swrap 32 (W * 64))).
  set (B := bv_swrap 32 (W * 64) mod 2^64).
  assert (HB : B mod 4096 = (W mod 64) * 64 /\ 0 <= B < 2^64).
  { subst B. unfold bv_swrap, bv_wrap. assert (E1 : bv_half_modulus 32 = 2^31) by reflexivity.
    assert (E2 : bv_modulus 32 = 2^32) by reflexivity. rewrite E1, E2.
    split; [Z.div_mod_to_equations; lia | apply Z.mod_pos_bound; lia]. }
  destruct HB as [HB1 HB2].
  assert (HB0 : B mod 64 = 0) by (Z.div_mod_to_equations; lia).
  rewrite lor_add64 by lia. rewrite unsigned_lit_wrap.
  Z.div_mod_to_equations; lia.
Qed.

Lemma le1_one : forall x : word, le1 x = [Z_to_bv 8 (bv_unsigned x)].
Proof. reflexivity. Qed.

Lemma store_byte : forall (w' : word) b, 0 <= b <= 4 ->
  le1 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w')) (bv_unsigned (Z_to_bv 64 b) mod 32))))
  = [Z_to_bv 8 (Z.shiftr (bv_unsigned w' mod 4096) b mod 256)].
Proof.
  intros w' b Hb. rewrite (unsigned_lit b) by lia. rewrite (Z.mod_small b 32) by lia.
  rewrite le1_one. apply (f_equal (fun y => [y])). apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 8 ?x) with (x mod 2^8). change (bv_wrap 64 ?x) with (x mod 2^64).
  change (bv_wrap 32 ?x) with (x mod 2^32).
  set (Y := Z.shiftr (bv_unsigned w' mod 2 ^ 32) b).
  assert (E : bv_swrap 32 Y mod 2^64 mod 2^8 = Y mod 2^8).
  { unfold bv_swrap, bv_wrap. assert (E1 : bv_half_modulus 32 = 2^31) by reflexivity.
    assert (E2 : bv_modulus 32 = 2^32) by reflexivity. rewrite E1, E2. Z.div_mod_to_equations; lia. }
  rewrite E. subst Y.
  rewrite (shiftr_mod_mod8 (bv_unsigned w') b 32) by lia.
  change 256 with (2^8). rewrite Z.mod_mod by lia. change 4096 with (2^12).
  rewrite (shiftr_mod_mod8 (bv_unsigned w') b 12) by lia. reflexivity.
Qed.

Lemma exit_and : forall (w : word) b, 0 <= b <= 5 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned w) (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64
    (bv_swrap 32 (Z.shiftl 18446744073709551615 (bv_unsigned (Z_to_bv 64 b) mod 32))))) 18446744073709551615)))))
    (Z_to_bv 64 0) = (bv_unsigned w mod 2 ^ b =? 0).
Proof.
  intros w b Hb.
  match goal with |- context [bv_unsigned (Z_to_bv 64 (Z.lxor ?X ?Y))] =>
    assert (M : bv_unsigned (Z_to_bv 64 (Z.lxor X Y)) = 2 ^ b - 1) end.
  { assert (B : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5) by lia.
    destruct B as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity. }
  rewrite M. rewrite zb_land_mask by lia.
  assert (P : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (P5 : 2 ^ b <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia). change (2 ^ 5) with 32 in P5.
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ b) P).
  apply eqb_lit; lia.
Qed.

Definition snoc_byte (k l v : Z) : list Z :=
  if k mod 4 =? 1 then [l * 4 + v / 16]
  else if k mod 4 =? 2 then [(l mod 16) * 16 + v / 4]
  else if k mod 4 =? 3 then [(l mod 4) * 64 + v]
  else [].

Lemma six_bytes_snoc : forall six v,
  six_bytes (six ++ [v]) = six_bytes six ++ snoc_byte (Z.of_nat (length six)) (last six 0) v.
Proof.
  intros six v. induction six as [|a|a b|a b c|a b c d l IH] using list4_ind.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (E : snoc_byte (Z.of_nat (length (a :: b :: c :: d :: l))) (last (a :: b :: c :: d :: l) 0) v
                = snoc_byte (Z.of_nat (length l)) (last l 0) v).
    { unfold snoc_byte.
      replace (Z.of_nat (length (a :: b :: c :: d :: l))) with (Z.of_nat (length l) + 1 * 4) by (cbn [length]; lia).
      rewrite Z.mod_add by lia. destruct l as [|e l]; reflexivity. }
    rewrite E. cbn [app six_bytes]. rewrite IH. reflexivity.
Qed.

Lemma snoc_code : forall k l v, 0 <= k -> 0 <= l < 64 -> 0 <= v < 64 -> 2 <= 6 * k mod 8 ->
  snoc_byte k l v = [Z.shiftr (l * 64 + v) (6 * k mod 8 + -2) mod 256].
Proof.
  intros k l v Hk Hl Hv Hb. unfold snoc_byte.
  assert (H4 : k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|H]]; rewrite H.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (6 + -2) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. f_equal.
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (4 + -2) with 2. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4. f_equal.
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (2 + -2) with 0. rewrite Z.shiftr_0_r. f_equal.
    Z.div_mod_to_equations; lia.
Qed.

Lemma mod64_16 : forall W, (W mod 64) mod 16 = W mod 16.
Proof. intros W. Z.div_mod_to_equations; lia. Qed.

Lemma mod64_4 : forall W, (W mod 64) mod 4 = W mod 4.
Proof. intros W. Z.div_mod_to_equations; lia. Qed.

Lemma tail_code : forall six W, W mod 64 = last six 0 ->
  six_tail_ok six = (6 * Z.of_nat (length six) mod 8 <=? 5) && (W mod 2 ^ (6 * Z.of_nat (length six) mod 8) =? 0).
Proof.
  intros six W HW. unfold six_tail_ok. cbv zeta. rewrite <- HW. rewrite mod64_16, mod64_4.
  remember (Z.of_nat (length six)) as k eqn:Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]]; rewrite H.
  - replace (6 * k mod 8) with 0 by (Z.div_mod_to_equations; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia).
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). change (2 ^ 4) with 16.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). change (2 ^ 2) with 4.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
Qed.

Lemma nb_bound : forall k L, 0 <= k -> k <= L -> 6 * k / 8 <= L / 4 * 3 + 2.
Proof. intros k L H1 H2. Z.div_mod_to_equations; lia. Qed.

Lemma bits_lt2 : forall k, 0 <= k -> 6 * k mod 8 < 2 -> 6 * (k + 1) mod 8 = 6 * k mod 8 + 6.
Proof. intros k H1 H2. Z.div_mod_to_equations; lia. Qed.

Lemma bits_ge2 : forall k, 0 <= k -> 2 <= 6 * k mod 8 -> 6 * (k + 1) mod 8 = 6 * k mod 8 + -2.
Proof. intros k H1 H2. Z.div_mod_to_equations; lia. Qed.

Lemma mod4096_64 : forall X l v, 0 <= v < 64 -> X mod 4096 = l * 64 + v -> X mod 64 = v.
Proof. intros X l v Hv H. Z.div_mod_to_equations; lia. Qed.

Lemma scan_nil : forall pad six,
  scan_out pad six [] = if (pad <=? 2) && six_tail_ok six then Some (six_bytes six) else None.
Proof. reflexivity. Qed.

Lemma scan_ws : forall c pad six rest, b64_ws c = true -> scan_out pad six (c :: rest) = scan_out pad six rest.
Proof. intros c pad six rest H. unfold scan_out. cbn [b64_scan]. rewrite H. reflexivity. Qed.

Lemma scan_61 : forall pad six rest, scan_out pad six (61 :: rest) = scan_out (pad + 1) six rest.
Proof. reflexivity. Qed.

Lemma scan_bad : forall c pad six rest, b64_ws c = false -> c <> 61 -> b64v c = None ->
  scan_out pad six (c :: rest) = None.
Proof.
  intros c pad six rest H1 H2 H3. unfold scan_out. cbn [b64_scan]. rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3.
  reflexivity.
Qed.

Lemma scan_padbad : forall c v pad six rest, b64_ws c = false -> c <> 61 -> b64v c = Some v -> pad <> 0 ->
  scan_out pad six (c :: rest) = None.
Proof.
  intros c v pad six rest H1 H2 H3 H4. unfold scan_out. cbn [b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3, (proj2 (Z.eqb_neq pad 0) H4). reflexivity.
Qed.

Lemma scan_val : forall c v six rest, b64_ws c = false -> c <> 61 -> b64v c = Some v ->
  scan_out 0 six (c :: rest) = scan_out 0 (six ++ [v]) rest.
Proof.
  intros c v six rest H1 H2 H3. unfold scan_out. cbn [b64_scan]. rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3.
  reflexivity.
Qed.

Lemma skipn_len_app : forall {A} (l1 l2 : list A), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros A l1 l2. induction l1 as [|x l1 IH]; [reflexivity|]. cbn. exact IH. Qed.

Lemma dec_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo : Z),
  lo <= bv_unsigned sp - 96 ->
  stk rsegs m lo (bv_unsigned sp - 96) ->
  rw_cells rsegs m (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x9 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs) /\
                stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14f9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 m lo HLO ST FR.
  assert (ST' : stk rsegs m lo (bv_unsigned sp)).
  { pose proof (stk_release rsegs m lo _ _ ST FR HLO) as S'.
    change (Z.of_nat (cells_size (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10))) with 96 in S'.
    replace (bv_unsigned sp - 96 + 96) with (bv_unsigned sp) in S' by lia. exact S'. }
  unfold dec_cells in FR.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  replace (bv_unsigned sp - 96 + 96) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  step.
  apply evt_done. split; [reflexivity | exact ST'].
Qed.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo lenp q tx : Z) (tb : list Z) (lb : list byte) (m0 : word -> option byte).
  Hypothesis MC : memchr_contract.
  Hypothesis HLO : lo <= bv_unsigned sp - 96.
  Hypothesis HLEN : Z.of_nat (length tb) <= 2^31 - 1.
  Hypothesis NZ : no_zero tb.
  Hypothesis BOK : bytes_ok tb.
  Hypothesis LB8 : length lb = 8%nat.
  Hypothesis DQT : q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q.
  Hypothesis DQG : q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q.
  Hypothesis DQL : q + b64_M tb <= lenp \/ lenp + 8 <= q.
  Hypothesis DQS : q + b64_M tb <= bv_unsigned sp - 96 \/ bv_unsigned sp <= q.
  Hypothesis DLS : lenp + 8 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= lenp.

  Definition QD : machine_state -> Prop :=
    dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo lenp q tb lb m0.

  Definition dmem (m : word -> option byte) (six : list Z) : Prop :=
    bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) /\
    bytes_at rsegs m 0x104a4 (map (Z_to_bv 8) b64_table) /\
    bytes_at rsegs m lenp lb /\ wr_at rsegs m lenp 8 /\
    bytes_at rsegs m q (map (Z_to_bv 8) (six_bytes six)) /\ wr_at rsegs m q (b64_M tb) /\
    rw_cells rsegs m (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) /\
    stk rsegs m lo (bv_unsigned sp - 96) /\ mem_inv rsegs m /\
    munch [(q, q + b64_M tb)] m0 m /\ wmono rsegs m0 m.

  Lemma char_range : forall pre c rest, tb = pre ++ c :: rest -> 1 <= c <= 255.
  Proof.
    intros pre c rest E. assert (I : In c tb) by (rewrite E; apply in_or_app; right; left; reflexivity).
    unfold no_zero in NZ. unfold bytes_ok in BOK.
    pose proof (proj1 (Forall_forall _ _) NZ c I) as H1. pose proof (proj1 (Forall_forall _ _) BOK c I) as H2.
    cbv beta in H1, H2. lia.
  Qed.

  Lemma dmem_six : forall m six six', six_bytes six' = six_bytes six -> dmem m six -> dmem m six'.
  Proof. intros m six six' E DM. unfold dmem in *. rewrite E. exact DM. Qed.

  Lemma dmem_read : forall m six pre rest, dmem m six -> tb = pre ++ rest ->
    ov_read_bytes rsegs m (wa (tx + Z.of_nat (length pre))) 1 = Some [Z_to_bv 8 (hd 0 (rest ++ [0]))].
  Proof.
    intros m six pre rest DM E. destruct DM as (TX & _).
    assert (L : length (map (Z_to_bv 8) (tb ++ [0])) = (length pre + length rest + 1)%nat)
      by (rewrite length_map, length_app, E, length_app; cbn [length]; lia).
    rewrite (bytes_at_read rsegs m tx _ (Z.of_nat (length pre)) 1 TX) by (rewrite ?L; lia).
    rewrite Nat2Z.id. rewrite E, <- app_assoc, map_app.
    rewrite <- (length_map (Z_to_bv 8) pre). rewrite skipn_len_app.
    destruct rest as [|c rest]; reflexivity.
  Qed.

  Lemma dmem_call : forall m m' six, dmem m six -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    dmem m' six.
  Proof.
    intros m m' six (TX & TB & L & WL & QB & WQ & FR & ST & MI & MU & WM) MU' WM' MI'.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj MI' (conj _ _)))))))))).
    - eapply bytes_at_transport; [exact TX|exact MU'|exact I].
    - eapply bytes_at_transport; [exact TB|exact MU'|exact I].
    - eapply bytes_at_transport; [exact L|exact MU'|exact I].
    - eapply wr_at_transport; [exact WL|exact WM'].
    - eapply bytes_at_transport; [exact QB|exact MU'|exact I].
    - eapply wr_at_transport; [exact WQ|exact WM'].
    - eapply rw_cells_transport; [exact FR|exact MU'|exact WM'|exact I].
    - eapply stk_transport_disjoint; [exact ST|exact MU'|exact WM'|exact I].
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x _. exact I.
    - eapply wmono_trans; eassumption.
  Qed.

  Lemma dmem_store : forall m six v b, dmem m six ->
    six_bytes (six ++ [v]) = six_bytes six ++ [b] ->
    Z.of_nat (length (six_bytes six)) + 1 <= b64_M tb ->
    dmem (write_to_mem m (wa (q + Z.of_nat (length (six_bytes six)))) [Z_to_bv 8 b]) (six ++ [v]).
  Proof.
    intros m six v b (TX & TB & L & WL & QB & WQ & FR & ST & MI & MU & WM) SN HN.
    pose proof WQ as (Q0 & Q1 & _).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    - apply bytes_at_write_other; [exact TX|lia|cbn [length]; lia|].
      rewrite length_map, length_app. cbn [length]. lia.
    - apply bytes_at_write_other; [exact TB|lia|cbn [length]; lia|].
      rewrite length_map, b64_table_length. cbn [length]. lia.
    - apply bytes_at_write_other; [exact L|lia|cbn [length]; lia|]. rewrite LB8. cbn [length]. lia.
    - apply wr_at_write. exact WL.
    - rewrite SN, map_app. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
      + apply bytes_at_write_other; [exact QB|lia|cbn [length]; lia|]. rewrite length_map. cbn [length]. lia.
      + rewrite length_map. apply bytes_at_write_same; cbn [length map]; lia.
    - apply wr_at_write. exact WQ.
    - apply rw_cells_frame; [exact FR|lia|cbn [length]; lia|].
      change (Z.of_nat (cells_size (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10))) with 96. cbn [length]. lia.
    - apply stk_write; [exact ST|lia|cbn [length]; lia].
    - apply mem_inv_store; [exact MI|].
      apply (wr_at_store_ok rsegs m q (b64_M tb) (Z.of_nat (length (six_bytes six))) 1 WQ); lia.
    - apply munch_write; [exact MU|lia|cbn [length]; lia|]. cbn [inside length]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  Lemma fail_done : forall six m (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word),
    b64_dec tb = None -> dmem m six ->
    evt rsegs QD (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 q) (Z_to_bv 64 q)
          a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f94) fc None m (seg_rom rsegs)).
  Proof.
    intros six m x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 HN DM.
    destruct DM as (_ & _ & L & _ & _ & _ & FR & ST & MI & MU & WM).
    apply evt_done. unfold QD, dec_post. rewrite HN. unfold dec_fail_post.
    exists x1, t0, t1, t2, x8, a1, a2, a3, a4, a5, a6, a7, x18, x19, x20, x21, x22, x23, x24, x25, x26, t3, t4, t5, t6, m.
    exact (conj eq_refl (conj L (conj FR (conj MU (conj WM (conj MI ST)))))).
  Qed.

  Definition at_head (rest pre : list Z) : Prop :=
    forall six pad (w : word) (m : word -> option byte) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tb = pre ++ rest ->
    b64_dec tb = scan_out pad six rest ->
    Z.of_nat (length six) <= Z.of_nat (length pre) ->
    0 <= pad <= Z.of_nat (length pre) ->
    bv_unsigned w mod 64 = last six 0 ->
    dmem m six ->
    evt rsegs QD (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) (Z_to_bv 64 q)
          a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (tx + Z.of_nat (length pre))) (Z_to_bv 64 0x104a4)
          (Z_to_bv 64 (Z.of_nat (length (six_bytes six)))) w (Z_to_bv 64 (6 * Z.of_nat (length six) mod 8))
          (Z_to_bv 64 pad) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 0x100002600) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f18) fc None m (seg_rom rsegs)).

  Lemma six_bound : forall six pre rest, tb = pre ++ rest ->
    Z.of_nat (length six) <= Z.of_nat (length pre) ->
    Z.of_nat (length (six_bytes six)) <= b64_M tb.
  Proof.
    intros six pre rest E HS. rewrite six_bytes_length. unfold b64_M.
    assert (HL : Z.of_nat (length pre) <= Z.of_nat (length tb)) by (rewrite E, length_app; lia).
    pose proof (nb_bound (Z.of_nat (length six)) (Z.of_nat (length tb)) ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma head_nil : forall pre, at_head [] pre.
  Proof.
    intros pre. unfold at_head.
    intros six pad w m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 E HD HS HP HW DM.
    pose proof (dmem_read m six pre [] DM E) as HR. cbn [app hd] in HR.
    pose proof (six_bound six pre [] E HS) as HN.
    rewrite scan_nil, (tail_code six (bv_unsigned w) HW) in HD.
    remember (6 * Z.of_nat (length six) mod 8) as bb eqn:HBB.
    assert (Rbb : 0 <= bb < 8) by (rewrite HBB; apply Z.mod_pos_bound; lia).
    assert (HL : Z.of_nat (length tb) = Z.of_nat (length pre)) by (rewrite E, app_nil_r; reflexivity).
    assert (HS8 : store_ok rsegs m (wa lenp) 8 = true).
    { destruct DM as (_ & _ & _ & WL & _). rewrite <- (Z.add_0_r lenp).
      apply (wr_at_store_ok rsegs m lenp 8 0 8 WL); lia. }
    step. rewrite (zxb_lit 0) by lia.
    step. if_false.
    step. step. step. if_false.
    step. if_true.
    step. if_true.
    step. step. if_cases H1; rewrite (lts_lit 5 bb) in H1 by lia; zify_bool H1.
    - step. step. step. step. step.
      if_cases H2; rewrite (exit_and w bb) in H2 by lia; zify_bool H2.
      + step. eapply fail_done; [|exact DM]. rewrite HD.
        rewrite (proj2 (Z.eqb_neq _ 0) H2). destruct (pad <=? 2), (bb <=? 5); reflexivity.
      + step. step. if_cases H3; rewrite (lts_lit 2 pad) in H3 by lia; zify_bool H3.
        * step. eapply fail_done; [|exact DM]. rewrite HD.
          rewrite (proj2 (Z.leb_gt pad 2) H3). reflexivity.
        * assert (HD' : b64_dec tb = Some (six_bytes six)).
          { rewrite HD, (proj2 (Z.leb_le pad 2) H3), (proj2 (Z.leb_le bb 5) H1), (proj2 (Z.eqb_eq _ 0) H2).
            reflexivity. }
          step. step.
          destruct DM as (TX & TB & L & WL & QB & WQ & FR & ST & MI & MU & WM).
          pose proof WL as (L0 & L1 & _). pose proof WQ as (Q0 & Q1 & _).
          eapply evt_mono.
          { eapply (dec_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo);
              [exact HLO| |].
            - apply stk_write; [exact ST|lia|rewrite length_le8; lia].
            - apply rw_cells_frame; [exact FR|lia|rewrite length_le8; lia|].
              change (Z.of_nat (cells_size (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10))) with 96.
              rewrite length_le8. lia. }
          intros ms' [-> ST2].
          unfold QD, dec_post. rewrite HD'. unfold dec_ok_post. cbv beta.
          do 15 eexists. split; [reflexivity|].
          refine (conj _ (conj _ (conj _ (conj _ (conj _ ST2))))).
          -- apply bytes_at_write_same; [lia|rewrite length_le8; lia].
          -- apply bytes_at_write_other; [exact QB|lia|rewrite length_le8; lia|].
             rewrite length_map, length_le8. lia.
          -- apply munch_write; [|lia|rewrite length_le8; lia|].
             ++ eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. tauto.
             ++ rewrite length_le8. cbn [inside]. right. left. lia.
          -- apply wmono_write. exact WM.
          -- apply mem_inv_store; [exact MI|]. rewrite length_le8. exact HS8.
    - step. eapply fail_done; [|exact DM]. rewrite HD.
      rewrite (proj2 (Z.leb_gt bb 5) H1). destruct (pad <=? 2); reflexivity.
  Qed.

  Lemma mc_path : forall c rest pre six pad (w : word) (m : word -> option byte)
      (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    at_head rest (pre ++ [c]) ->
    1 <= c <= 255 -> b64_ws c = false -> c <> 61 ->
    tb = pre ++ c :: rest ->
    b64_dec tb = scan_out pad six (c :: rest) ->
    Z.of_nat (length six) <= Z.of_nat (length pre) ->
    0 <= pad <= Z.of_nat (length pre) ->
    bv_unsigned w mod 64 = last six 0 ->
    dmem m six ->
    evt rsegs QD (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) (Z_to_bv 64 q)
          a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (tx + Z.of_nat (length pre))) (Z_to_bv 64 0x104a4)
          (Z_to_bv 64 (Z.of_nat (length (six_bytes six)))) w (Z_to_bv 64 (6 * Z.of_nat (length six) mod 8))
          (Z_to_bv 64 pad) (Z_to_bv 64 61) (Z_to_bv 64 2) (Z_to_bv 64 0x100002600) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f3c) fc None m (seg_rom rsegs)).
  Proof.
    intros c rest pre six pad w m x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 IH Hc HWs H61 E HD HS HP HW DM.
    unfold at_head in IH.
    assert (HL : Z.of_nat (length tb) = Z.of_nat (length pre) + 1 + Z.of_nat (length rest))
      by (rewrite E, length_app; cbn [length]; lia).
    assert (E' : tb = (pre ++ [c]) ++ rest) by (rewrite <- app_assoc; exact E).
    assert (HP1 : Z.of_nat (length (pre ++ [c])) = Z.of_nat (length pre) + 1) by (rewrite length_app; cbn [length]; lia).
    pose proof (six_bound six pre (c :: rest) E HS) as HN.
    pose proof DM as (_ & TAB & _ & _ & _ & _ & _ & _ & MI & _ & _).
    step. step. step.
    pose proof MC as MC'. unfold memchr_contract in MC'.
    eapply evt_cut.
    { eapply MC' with (buf := map (Z_to_bv 8) b64_table).
      - rewrite (unsigned_lit 0x104a4) by lia. exact TAB.
      - rewrite (unsigned_lit 65) by lia. apply memchr_ok_b64.
      - exact MI. }
    clear TAB MI.
    intros ms' POST. unfold memchr_post in POST.
    destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & _).
    rewrite (res_b64 c) by lia.
    rewrite (ret_pc_even 0x14f48) by (first [lia | reflexivity]).
    pose proof (dmem_call m m' six DM MU WM MI') as DM'. clear DM MU WM MI'.
    unfold b64r. destruct (b64v c) as [v|] eqn:HV.
    - pose proof (b64v_range c v HV) as Rv.
      step. if_cases H1; rewrite (eqb_lit (0x104a4 + v) 0) in H1 by lia; zify_bool H1; [lia|].
      step. if_cases H2; rewrite (eqb_lit pad 0) in H2 by lia; zify_bool H2.
      + step. eapply fail_done; [|exact DM']. rewrite HD. apply (scan_padbad c v); assumption.
      + subst pad. assert (RB : 0 <= 6 * Z.of_nat (length six) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
        step. step. rewrite (subw_v v) by lia. step.
        match goal with |- context [Z_to_bv 64 (Z.lor ?A ?B)] => set (w' := Z_to_bv 64 (Z.lor A B)) end.
        assert (HW' : bv_unsigned w' mod 4096 = (bv_unsigned w mod 64) * 64 + v) by (unfold w'; apply wacc; lia).
        assert (HW1 : bv_unsigned w' mod 64 = last (six ++ [v]) 0).
        { rewrite last_last. apply (mod4096_64 _ (bv_unsigned w mod 64)); assumption. }
        clearbody w'.
        assert (HD1 : b64_dec tb = scan_out 0 (six ++ [v]) rest) by (rewrite HD; apply scan_val; assumption).
        assert (HS1 : Z.of_nat (length (six ++ [v])) <= Z.of_nat (length (pre ++ [c])))
          by (rewrite HP1, length_app; cbn [length]; lia).
        assert (HP0 : 0 <= 0 <= Z.of_nat (length (pre ++ [c]))) by lia.
        assert (HK : Z.of_nat (length (six ++ [v])) = Z.of_nat (length six) + 1) by (rewrite length_app; cbn [length]; lia).
        step. step. if_cases H3; rewrite (lts_lit (6 * Z.of_nat (length six) mod 8) 2) in H3 by lia; zify_bool H3.
        * step. rewrite (addiw_lit (6 * Z.of_nat (length six) mod 8) 6) by lia.
          step. step.
          assert (SN : six_bytes (six ++ [v]) = six_bytes six).
          { rewrite six_bytes_snoc. unfold snoc_byte.
            assert (K0 : Z.of_nat (length six) mod 4 = 0) by (Z.div_mod_to_equations; lia).
            rewrite K0. apply app_nil_r. }
          replace (tx + Z.of_nat (length pre) + 1) with (tx + Z.of_nat (length (pre ++ [c]))) by lia.
          replace (6 * Z.of_nat (length six) mod 8 + 6) with (6 * Z.of_nat (length (six ++ [v])) mod 8)
            by (rewrite HK; apply bits_lt2; lia).
          rewrite <- SN.
          eapply IH; [exact E' | exact HD1 | exact HS1 | exact HP0 | exact HW1 | ].
          apply (dmem_six m' six); [exact SN | exact DM'].
        * step. rewrite (addiw_lit (6 * Z.of_nat (length six) mod 8) (-2)) by lia.
          step. step. step.
          assert (HSN : six_bytes (six ++ [v]) =
            six_bytes six ++ [Z.shiftr ((bv_unsigned w mod 64) * 64 + v) (6 * Z.of_nat (length six) mod 8 + -2) mod 256]).
          { rewrite six_bytes_snoc, HW. f_equal. apply snoc_code; [lia | rewrite <- HW; apply Z.mod_pos_bound; lia | lia | lia]. }
          assert (HN1 : Z.of_nat (length (six_bytes six)) + 1 <= b64_M tb).
          { pose proof (six_bound (six ++ [v]) (pre ++ [c]) rest E' HS1) as B1.
            rewrite HSN, length_app in B1. cbn [length] in B1. lia. }
          assert (HSq : store_ok rsegs m' (wa (q + Z.of_nat (length (six_bytes six)))) 1 = true).
          { destruct DM' as (_ & _ & _ & _ & _ & WQ & _). apply (wr_at_store_ok rsegs m' q (b64_M tb) _ 1 WQ); lia. }
          step. step. step. step.
          rewrite (store_byte w' (6 * Z.of_nat (length six) mod 8 + -2)) by lia.
          rewrite HW'.
          remember (Z.shiftr (bv_unsigned w mod 64 * 64 + v) (6 * Z.of_nat (length six) mod 8 + -2) mod 256)
            as bt eqn:Hbt.
          replace (tx + Z.of_nat (length pre) + 1) with (tx + Z.of_nat (length (pre ++ [c]))) by lia.
          replace (6 * Z.of_nat (length six) mod 8 + -2) with (6 * Z.of_nat (length (six ++ [v])) mod 8)
            by (rewrite HK; apply bits_ge2; lia).
          replace (Z.of_nat (length (six_bytes six)) + 1) with (Z.of_nat (length (six_bytes (six ++ [v]))))
            by (rewrite HSN, length_app; cbn [length]; lia).
          eapply IH; [exact E' | exact HD1 | exact HS1 | exact HP0 | exact HW1 | ].
          apply dmem_store; [exact DM' | exact HSN | exact HN1].
    - step. if_true. step. eapply fail_done; [|exact DM']. rewrite HD. apply scan_bad; assumption.
  Qed.

  Lemma head_cons : forall c rest pre, at_head rest (pre ++ [c]) -> at_head (c :: rest) pre.
  Proof.
    intros c rest pre IH. pose proof IH as IH0. unfold at_head in IH0 |- *.
    intros six pad w m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 E HD HS HP HW DM.
    pose proof (char_range pre c rest E) as Hc.
    pose proof (dmem_read m six pre (c :: rest) DM E) as HR. cbn [app hd] in HR.
    assert (E' : tb = (pre ++ [c]) ++ rest) by (rewrite <- app_assoc; exact E).
    assert (HP1 : Z.of_nat (length (pre ++ [c])) = Z.of_nat (length pre) + 1) by (rewrite length_app; cbn [length]; lia).
    assert (HL : Z.of_nat (length tb) = Z.of_nat (length pre) + 1 + Z.of_nat (length rest))
      by (rewrite E, length_app; cbn [length]; lia).
    step. rewrite (zxb_lit c) by lia.
    step. if_cases H1; rewrite (ltu_lit 61 c) in H1 by lia; zify_bool H1.
    - eapply (mc_path c rest pre six pad w m); [exact IH|lia|apply ws_big; lia|lia|exact E|exact HD|exact HS|exact HP|exact HW|exact DM].
    - step. step. step. if_cases H2; rewrite (ws_lem c) in H2 by lia; rewrite negb_involutive in H2.
      + step. step.
        replace (tx + Z.of_nat (length pre) + 1) with (tx + Z.of_nat (length (pre ++ [c]))) by lia.
        eapply IH0; [exact E' | rewrite HD; apply scan_ws; exact H2 | lia | lia | exact HW | exact DM].
      + step. if_cases H3; rewrite (eqb_lit c 61) in H3 by lia; zify_bool H3.
        * step. if_cases H4; rewrite (eqb_lit c 0) in H4 by lia; zify_bool H4; [lia|].
          eapply (mc_path c rest pre six pad w m); [exact IH|lia|exact H2|exact H3|exact E|exact HD|exact HS|exact HP|exact HW|exact DM].
        * subst c. step. rewrite (addiw_lit pad 1) by lia. step. step. step.
          replace (tx + Z.of_nat (length pre) + 1) with (tx + Z.of_nat (length (pre ++ [61]))) by lia.
          eapply IH0; [exact E' | rewrite HD; apply scan_61 | lia | lia | exact HW | exact DM].
  Qed.

  Lemma head_all : forall rest pre, at_head rest pre.
  Proof.
    induction rest as [|c rest IH]; intros pre.
    - apply head_nil.
    - apply head_cons. apply IH.
  Qed.

  Lemma dec_main_sec : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word),
    dmem m0 [] ->
    evt rsegs QD (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) (Z_to_bv 64 q)
          a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eec) fc None m0 (seg_rom rsegs)).
  Proof.
    intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 DM.
    do 11 step.
    replace (Z_to_bv 64 tx) with (Z_to_bv 64 (tx + Z.of_nat (length (@nil Z))))
      by (cbn [length Z.of_nat]; rewrite Z.add_0_r; reflexivity).
    eapply (head_all tb [] [] 0 (Z_to_bv 64 0)); [reflexivity|reflexivity|cbn; lia|cbn; lia|reflexivity|exact DM].
  Qed.
End Loop.

Theorem dec_loop : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo lenp q tx : Z) (tb : list Z) (lb : list byte),
  memchr_contract ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2^31 - 1 ->
  bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) ->
  bytes_at rsegs m 0x104a4 (map (Z_to_bv 8) b64_table) ->
  bytes_at rsegs m lenp lb -> length lb = 8%nat -> wr_at rsegs m lenp 8 ->
  wr_at rsegs m q (b64_M tb) ->
  rw_cells rsegs m (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  stk rsegs m lo (bv_unsigned sp - 96) -> lo <= bv_unsigned sp - 96 ->
  mem_inv rsegs m ->
  q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q ->
  q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q ->
  q + b64_M tb <= lenp \/ lenp + 8 <= q ->
  q + b64_M tb <= bv_unsigned sp - 96 \/ bv_unsigned sp <= q ->
  lenp + 8 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= lenp ->
  evt rsegs (dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo lenp q tb lb m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) (Z_to_bv 64 q)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 m lo lenp q tx tb lb
    MC NZ BOK HLEN TX TB L LB8 WL WQ FR ST HLO MI DQT DQG DQL DQS DLS.
  pose proof WQ as (Q0 & Q1 & _).
  eapply dec_main_sec; try eassumption.
  unfold dmem.
  refine (conj TX (conj TB (conj L (conj WL (conj _ (conj WQ (conj FR (conj ST (conj MI
    (conj (munch_refl _ m) (wmono_refl rsegs m))))))))))).
  apply bytes_at_nil. unfold b64_M in Q1. lia.
Qed.

Theorem dec_loop_ok : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo lenp q tx : Z) (tb bs : list Z) (lb : list byte),
  memchr_contract -> b64_dec tb = Some bs ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2^31 - 1 ->
  bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) ->
  bytes_at rsegs m 0x104a4 (map (Z_to_bv 8) b64_table) ->
  bytes_at rsegs m lenp lb -> length lb = 8%nat -> wr_at rsegs m lenp 8 ->
  wr_at rsegs m q (b64_M tb) ->
  rw_cells rsegs m (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  stk rsegs m lo (bv_unsigned sp - 96) -> lo <= bv_unsigned sp - 96 ->
  mem_inv rsegs m ->
  q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q ->
  q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q ->
  q + b64_M tb <= lenp \/ lenp + 8 <= q ->
  q + b64_M tb <= bv_unsigned sp - 96 \/ bv_unsigned sp <= q ->
  lenp + 8 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= lenp ->
  evt rsegs (dec_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo lenp q tb bs m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) (Z_to_bv 64 q)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 m lo lenp q tx tb bs lb MC HB. intros.
  eapply evt_mono; [eapply dec_loop; eassumption|].
  intros ms' HQ. unfold dec_post in HQ. rewrite HB in HQ. exact HQ.
Qed.

Theorem dec_loop_fail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo lenp q tx : Z) (tb : list Z) (lb : list byte),
  memchr_contract -> b64_dec tb = None ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2^31 - 1 ->
  bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) ->
  bytes_at rsegs m 0x104a4 (map (Z_to_bv 8) b64_table) ->
  bytes_at rsegs m lenp lb -> length lb = 8%nat -> wr_at rsegs m lenp 8 ->
  wr_at rsegs m q (b64_M tb) ->
  rw_cells rsegs m (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  stk rsegs m lo (bv_unsigned sp - 96) -> lo <= bv_unsigned sp - 96 ->
  mem_inv rsegs m ->
  q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q ->
  q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q ->
  q + b64_M tb <= lenp \/ lenp + 8 <= q ->
  q + b64_M tb <= bv_unsigned sp - 96 \/ bv_unsigned sp <= q ->
  lenp + 8 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= lenp ->
  evt rsegs (dec_fail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo lenp q tb lb m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) (Z_to_bv 64 q)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 m lo lenp q tx tb lb MC HB. intros.
  eapply evt_mono; [eapply dec_loop; eassumption|].
  intros ms' HQ. unfold dec_post in HQ. rewrite HB in HQ. exact HQ.
Qed.

Theorem dec_null : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp - 96) (dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  stk rsegs m lo (bv_unsigned sp - 96) -> lo <= bv_unsigned sp - 96 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs) /\
                stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14ee4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 m lo FR ST HLO.
  step. if_true. step.
  eapply dec_epi; eassumption.
Qed.
