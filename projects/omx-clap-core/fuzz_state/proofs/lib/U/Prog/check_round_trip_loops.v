From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts B64Canon.
Import ListNotations.
Open Scope Z_scope.

Definition crt_chr (v : Z) : Z :=
  if v <? 26 then v + 65 else if v <? 52 then v + 71 else if v <? 62 then v + 252 else if v =? 62 then 43 else 47.

Lemma crt_cmp51 : forall x y, 0 <= y < 4 -> (51 < x * 4 <-> 51 < x * 4 + y).
Proof. intros x y Hy. lia. Qed.

Ltac chr_fin := unfold crt_chr; decide_tests; first [ reflexivity | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

Lemma chA : forall (Q : machine_state -> Prop)
  (x1 x2 x3 x4 x5 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
  0 <= v < 256 ->
  (forall d : word, Z_to_bv 64 (crt_chr (v / 4)) = d ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 62) (Z_to_bv 64 207) x8 x9 x10 x11 x12 x13 (Z_to_bv 64 103) x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 v) d x27 (Z_to_bv 64 247) x29 x30 x31)
                    F (Z_to_bv 64 0x13b00) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 62) (Z_to_bv 64 207) x8 x9 x10 x11 x12 x13 (Z_to_bv 64 103) x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 v) (Z_to_bv 64 (Z.shiftr v 2)) x27 (Z_to_bv 64 247) x29 x30 x31)
                  F (Z_to_bv 64 0x13acc) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x29 x30 x31 F fc m v Hv K.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  zstep. if_cases B1; zify_cond B1.
  - zstep. if_cases B2; zify_cond B2.
    + zstep. if_cases B3; zify_cond B3.
      * zstep. if_cases B4; zify_cond B4.
        -- zstep. apply K. chr_fin.
        -- zstep. zstep. apply K. chr_fin.
      * zstep. zstep. apply K. chr_fin.
    + zstep. zstep. apply K. chr_fin.
  - zstep. zstep. apply K. chr_fin.
Qed.

Lemma chB : forall (Q : machine_state -> Prop)
  (x1 x2 x3 x4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
  0 <= v < 64 ->
  (forall d : word, Z_to_bv 64 (crt_chr v) = d ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 61) (Z_to_bv 64 62) x7 x8 x9 x10 x11 x12 x13 x14 x15
                    (Z_to_bv 64 25) (Z_to_bv 64 51) x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 v) d x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x13b4c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 61) (Z_to_bv 64 62) x7 x8 x9 x10 x11 x12 x13 x14 x15
                  (Z_to_bv 64 25) (Z_to_bv 64 51) x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 v) x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x13b18) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x2 x3 x4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 F fc m v Hv K.
  zstep. if_cases B1; zify_cond B1.
  - zstep. if_cases B2; zify_cond B2.
    + zstep. if_cases B3; zify_cond B3.
      * zstep. if_cases B4; zify_cond B4.
        -- zstep. apply K. chr_fin.
        -- zstep. zstep. apply K. chr_fin.
      * zstep. zstep. apply K. chr_fin.
    + zstep. zstep. apply K. chr_fin.
  - zstep. zstep. apply K. chr_fin.
Qed.

Lemma chC : forall (Q : machine_state -> Prop)
  (x1 x2 x3 x4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x y : Z),
  0 <= x < 16 -> 0 <= y < 4 ->
  (forall d : word, Z_to_bv 64 (crt_chr (x * 4 + y)) = d ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 61) (Z_to_bv 64 62) x7 x8 x9 x10 x11 x12 x13 x14 x15
                    (Z_to_bv 64 25) (Z_to_bv 64 51) x18 x19 x20 x21 x22 d (Z_to_bv 64 (x * 4)) x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x13b7c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 61) (Z_to_bv 64 62) x7 x8 x9 x10 x11 x12 x13 x14 x15
                  (Z_to_bv 64 25) (Z_to_bv 64 51) x18 x19 x20 x21 x22 (Z_to_bv 64 (x * 4 + y)) (Z_to_bv 64 (x * 4))
                  x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x13b6c) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x2 x3 x4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 F fc m x y Hx Hy K.
  zstep. if_cases B1; zify_cond B1.
  - zstep. if_cases B2; zify_cond B2.
    + apply (crt_cmp51 x y Hy) in B2.
      zstep. if_cases B3; zify_cond B3.
      * zstep. if_cases B4; zify_cond B4.
        -- zstep. zstep. apply K. chr_fin.
        -- zstep. zstep. apply K. chr_fin.
      * zstep. zstep. apply K. chr_fin.
    + assert (B2' : x * 4 + y <= 51) by (pose proof (crt_cmp51 x y Hy); lia).
      zstep. zstep. apply K. chr_fin.
  - zstep. zstep. apply K. chr_fin.
Qed.

Lemma chD : forall (Q : machine_state -> Prop)
  (x1 x2 x3 x4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
  0 <= v < 64 ->
  (forall d : word, Z_to_bv 64 (crt_chr v) = d ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 61) (Z_to_bv 64 62) x7 x8 x9 x10 x11 x12 x13 x14 x15
                    (Z_to_bv 64 25) (Z_to_bv 64 51) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 d x31)
                    F (Z_to_bv 64 0x13ba0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 61) (Z_to_bv 64 62) x7 x8 x9 x10 x11 x12 x13 x14 x15
                  (Z_to_bv 64 25) (Z_to_bv 64 51) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 v) x31)
                  F (Z_to_bv 64 0x13b90) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x2 x3 x4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31 F fc m v Hv K.
  zstep. if_cases B1; zify_cond B1.
  - zstep. if_cases B2; zify_cond B2.
    + zstep. if_cases B3; zify_cond B3.
      * zstep. if_cases B4; zify_cond B4.
        -- zstep. zstep. apply K. chr_fin.
        -- zstep. zstep. apply K. chr_fin.
      * zstep. zstep. apply K. chr_fin.
    + zstep. zstep. apply K. chr_fin.
  - zstep. zstep. apply K. chr_fin.
Qed.

Ltac br_t := let B := fresh "BR" in
  if_cases B; zify_cond B; [ | exfalso; first [ lia | discriminate | Z.div_mod_to_equations; lia ] ].
Ltac br_f := let B := fresh "BR" in
  if_cases B; zify_cond B; [ exfalso; first [ lia | discriminate | Z.div_mod_to_equations; lia ] | ].
Ltac nb := let B := fresh "BR" in
  if_cases B; zify_cond B; [ exfalso; first [ lia | Z.div_mod_to_equations; lia ] | clear B ].

Lemma byte_rng : forall c : byte, 0 <= bv_unsigned c < 256.
Proof. intros c. pose proof (bv_unsigned_in_range 8 c) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma byte_nz : forall c : byte, c <> Z_to_bv 8 0 -> bv_unsigned c <> 0.
Proof. intros c H E. apply H. apply bv_eq. rewrite E. reflexivity. Qed.

Lemma byte_rt : forall c : byte, Z_to_bv 8 (bv_unsigned c) = c.
Proof. intros c. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma chr_rng : forall v, 0 <= v < 64 -> 0 <= crt_chr v < 2^64.
Proof.
  intros v Hv. unfold crt_chr.
  destruct (Z.ltb_spec v 26), (Z.ltb_spec v 52), (Z.ltb_spec v 62), (Z.eqb_spec v 62); lia.
Qed.

Lemma chr_mod : forall v, 0 <= v < 64 -> crt_chr v mod 256 = b64c v.
Proof.
  intros v Hv.
  assert (C : forallb (fun n => Z.eqb (crt_chr (Z.of_nat n) mod 256) (b64c (Z.of_nat n))) (seq 0 64) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat v) ltac:(apply in_seq; lia)).
  apply Z.eqb_eq in C. rewrite Z2Nat.id in C by lia. exact C.
Qed.

Lemma le1_chr : forall v, 0 <= v < 64 -> le1 (Z_to_bv 64 (crt_chr v)) = [Z_to_bv 8 (b64c v)].
Proof.
  intros v Hv. unfold le1. rewrite unsigned_lit by (apply chr_rng; exact Hv).
  cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. change (2 ^ 8) with 256.
  rewrite chr_mod by exact Hv. destruct (b64c_range v Hv) as [Hc _].
  rewrite (Z.mod_small (b64c v)) by lia. reflexivity.
Qed.

Lemma le1_lit : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma le1_byte : forall c : byte, le1 (Z_to_bv 64 (bv_unsigned c)) = [c].
Proof. intros c. exact (le1_zxb c). Qed.

Lemma lor_low : forall x y k, 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y -> Z.lor x (y * 2 ^ k) = x + y * 2 ^ k.
Proof.
  intros x y k Hk Hx Hy.
  assert (D : Z.land x (y * 2 ^ k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    destruct (Z.ltb_spec i k).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small x (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma lor_p : forall x y k p, 0 <= k -> p = 2 ^ k -> 0 <= x < p -> 0 <= y -> Z.lor x (y * p) = x + y * p.
Proof. intros x y k p Hk -> Hx Hy. apply lor_low; assumption. Qed.

Lemma sh62 : forall x, 0 <= x < 256 -> Z.shiftr (Z.shiftl x 62 mod 18446744073709551616) 58 = x mod 4 * 16.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 62) with 4611686018427387904. change (2 ^ 58) with 288230376151711744.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sh60 : forall x, 0 <= x < 256 -> Z.shiftr (Z.shiftl x 60 mod 18446744073709551616) 58 = x mod 16 * 4.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 60) with 1152921504606846976. change (2 ^ 58) with 288230376151711744.
  Z.div_mod_to_equations. lia.
Qed.

Lemma vB : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (Z.shiftr y 4) (Z.shiftr (Z.shiftl x 62 mod 18446744073709551616) 58) = x mod 4 * 16 + y / 16.
Proof.
  intros x y Hx Hy. rewrite sh62 by exact Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (lor_p (y / 16) (x mod 4) 4 16) by (try reflexivity; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma vB0 : forall x, 0 <= x < 256 ->
  Z.lor 0 (Z.shiftr (Z.shiftl x 62 mod 18446744073709551616) 58) = x mod 4 * 16.
Proof. intros x Hx. rewrite sh62 by exact Hx. apply Z.lor_0_l. Qed.

Lemma vC : forall y z, 0 <= y < 256 -> 0 <= z < 256 ->
  Z.lor (Z.shiftr z 6) (y mod 16 * 4) = y mod 16 * 4 + z / 64.
Proof.
  intros y z Hy Hz. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
  rewrite (lor_p (z / 64) (y mod 16) 2 4) by (try reflexivity; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma vC0 : forall y, Z.lor 0 (y mod 16 * 4) = y mod 16 * 4 + 0.
Proof. intros y. rewrite Z.lor_0_l. lia. Qed.

Lemma vD : forall z, 0 <= z -> Z.land z 63 = z mod 64.
Proof. intros z Hz. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma firstn1_skipn : forall {A} (l : list A) n d, (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l d].
Proof. induction l as [|a l IH]; intros [|n] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma rd1 : forall m a (L : list byte) i c, bytes_at rsegs m a L -> 0 <= i < Z.of_nat (length L) ->
  nth (Z.to_nat i) L (Z_to_bv 8 0) = c -> ov_read_bytes rsegs m (wa (a + i)) 1 = Some [c].
Proof.
  intros m a L i c H Hi Hc.
  rewrite (bytes_at_read rsegs m a L i 1 H) by lia.
  rewrite (firstn1_skipn L (Z.to_nat i) (Z_to_bv 8 0)) by lia. rewrite Hc. reflexivity.
Qed.

Lemma nth_bz : forall (L : list byte) n, nth n (map bv_unsigned L) 0 = bv_unsigned (nth n L (Z_to_bv 8 0)).
Proof. induction L as [|c L IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma firstn_snoc : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof. induction l as [|a l IH]; intros [|n] H; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.

Lemma b64_enc_app3 : forall n l1 l2, length l1 = (3 * n)%nat -> b64_enc (l1 ++ l2) = b64_enc l1 ++ b64_enc l2.
Proof.
  induction n as [|n IH]; intros l1 l2 H.
  - destruct l1; [reflexivity|cbn in H; lia].
  - destruct l1 as [|x0 [|x1 [|x2 l1]]]; cbn in H; try lia.
    cbn [app b64_enc]. rewrite (IH l1 l2) by lia. reflexivity.
Qed.

Lemma enc_len_Z : forall L : list Z, Z.of_nat (length (b64_enc L)) = (Z.of_nat (length L) + 2) / 3 * 4.
Proof. intros L. rewrite b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add. reflexivity. Qed.

Lemma strip_app : forall l1 l2, b64_strip (l1 ++ l2) = b64_strip l1 ++ b64_strip l2.
Proof. intros l1 l2. unfold b64_strip. apply filter_app. Qed.

Lemma strip_len : forall l, (length (b64_strip l) <= length l)%nat.
Proof. induction l as [|c l IH]; [cbn; lia|]. rewrite b64_strip_cons. destruct (b64_ws c); cbn [length]; lia. Qed.

Lemma pfx_store : forall m q (pre : list byte) a bs,
  bytes_at rsegs m q pre -> a = q + Z.of_nat (length pre) -> a + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa a) bs) q (pre ++ bs).
Proof.
  intros m q pre a bs H Ha Hb. pose proof (bytes_at_bound _ _ _ _ H) as Hq.
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact H | lia | lia | left; lia].
  - subst a. apply bytes_at_write_same; lia.
Qed.

Lemma bytes_at_skipn_S : forall m a (L : list byte) j, bytes_at rsegs m a (skipn j L) -> (j < length L)%nat ->
  bytes_at rsegs m (a + 1) (skipn (S j) L).
Proof.
  intros m a L j H Hj.
  assert (E : skipn j L = firstn 1 (skipn j L) ++ skipn (S j) L).
  { rewrite <- (firstn_skipn 1 (skipn j L)) at 1. rewrite skipn_skipn. reflexivity. }
  rewrite E in H. apply bytes_at_app in H as [_ H2].
  rewrite firstn_length_le in H2 by (rewrite length_skipn; lia). exact H2.
Qed.

Lemma rw_cells_one : forall m a n (L : list byte), bytes_at rsegs m a L -> length L = n ->
  wr_at rsegs m a (Z.of_nat n) -> rw_cells rsegs m a [CB n L].
Proof.
  intros m a n L H HL W. split; [split|].
  - cbn. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma rw_cells_two : forall m a n1 n2 (L1 L2 : list byte), bytes_at rsegs m a (L1 ++ L2) -> length L1 = n1 ->
  length L2 = n2 -> wr_at rsegs m a (Z.of_nat (n1 + n2)) -> rw_cells rsegs m a [CB n1 L1; CB n2 L2].
Proof.
  intros m a n1 n2 L1 L2 H H1 H2 W. split; [split|].
  - cbn. split; [exact H1 | split; [exact H2 | exact I]].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Ltac crt_out PRE :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     end);
    lazymatch type of PRE with bytes_at _ _ ?qq ?pre =>
      let S1 := fresh "S" in let S2 := fresh "S" in let P' := fresh "P" in
      assert (S1 : E = qq + Z.of_nat (length pre)) by (rewrite ?length_app, ?length_le1, ?length_map; lia);
      assert (S2 : E + Z.of_nat (length bs) <= 2^64) by (rewrite ?length_le1; lia);
      pose proof (pfx_store m qq pre E bs PRE S1 S2) as P';
      clear PRE S1 S2; rename P' into PRE
    end;
    store_done
  end.

Section ExpectedText.
  Variables (ra sp gp tp s0 s2 s5 s6 : word) (F : bvmap 5 word) (fc : bv 32)
    (want b l En : Z) (bs : list byte) (m0 : word -> option byte).
  Hypothesis HN : Z.of_nat (length bs) = l.
  Hypothesis HL : l < 2^60.
  Hypothesis HE : En = (l + 2) / 3 * 4.
  Hypothesis DATA0 : bytes_at rsegs m0 b bs.
  Hypothesis WR0 : wr_at rsegs m0 want (En + 1).
  Hypothesis DJ : want + (En + 1) <= b \/ b + l <= want.

  Definition et_pre (k : Z) : list byte :=
    map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * k)) (map bv_unsigned bs))).

  Definition et_facts (m : word -> option byte) (k : Z) : Prop :=
    munch [(want, want + (En + 1))] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ bytes_at rsegs m want (et_pre k).

  Definition et_post : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 want) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 l) (Z_to_bv 64 b) s5 s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
               F (Z_to_bv 64 0x13c1c) fc None m' (seg_rom rsegs) /\
      munch [(want, want + (En + 1))] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' want [CB (Z.to_nat (En + 1)) (map (Z_to_bv 8) (b64_enc (map bv_unsigned bs)) ++ [Z_to_bv 8 0])].

  Abbreviation XS pc x10 x23 x24 x25 x26 x27 x29 x30 x31 m :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 61) (Z_to_bv 64 62) (Z_to_bv 64 207) s0 (Z_to_bv 64 want) x10
       (Z_to_bv 64 (18446744073709551615 - b)) (Z_to_bv 64 (b + 2)) (Z_to_bv 64 (b + 1)) (Z_to_bv 64 103)
       (Z_to_bv 64 (-1)) (Z_to_bv 64 25) (Z_to_bv 64 51)
       s2 (Z_to_bv 64 l) (Z_to_bv 64 b) s5 s6 x23 x24 x25 x26 x27 (Z_to_bv 64 247) x29 x30 x31)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma et_pre_len : forall k, 0 <= k -> 3 * k <= l -> Z.of_nat (length (et_pre k)) = 4 * k.
  Proof.
    intros k Hk Hkl. unfold et_pre. rewrite length_map, enc_len_Z, firstn_length_le.
    - rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
    - rewrite length_map. lia.
  Qed.

  Lemma et_step3 : forall k, 0 <= k -> 3 * k + 3 <= l ->
    et_pre (k + 1) = et_pre k ++ map (Z_to_bv 8) (b64_enc
      [bv_unsigned (nth (Z.to_nat (3 * k)) bs (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (3 * k + 1)) bs (Z_to_bv 8 0));
       bv_unsigned (nth (Z.to_nat (3 * k + 2)) bs (Z_to_bv 8 0))]).
  Proof.
    intros k Hk Hkl. unfold et_pre.
    assert (LB : Z.of_nat (length (map bv_unsigned bs)) = l) by (rewrite length_map; exact HN).
    replace (Z.to_nat (3 * (k + 1))) with (S (S (S (Z.to_nat (3 * k))))) by lia.
    rewrite !firstn_snoc by lia. rewrite <- !app_assoc. cbn [app].
    rewrite (b64_enc_app3 (Z.to_nat k)) by (rewrite firstn_length_le; lia).
    rewrite map_app, !nth_bz.
    replace (S (Z.to_nat (3 * k))) with (Z.to_nat (3 * k + 1)) by lia.
    replace (S (Z.to_nat (3 * k + 1))) with (Z.to_nat (3 * k + 2)) by lia.
    reflexivity.
  Qed.

  Lemma et_step2 : forall k, 0 <= k -> l = 3 * k + 2 ->
    et_pre (k + 1) = et_pre k ++ map (Z_to_bv 8) (b64_enc
      [bv_unsigned (nth (Z.to_nat (3 * k)) bs (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (3 * k + 1)) bs (Z_to_bv 8 0))]).
  Proof.
    intros k Hk Hkl. unfold et_pre.
    assert (LB : Z.of_nat (length (map bv_unsigned bs)) = l) by (rewrite length_map; exact HN).
    replace (firstn (Z.to_nat (3 * (k + 1))) (map bv_unsigned bs))
      with (firstn (S (S (Z.to_nat (3 * k)))) (map bv_unsigned bs)) by (rewrite !firstn_all2 by lia; reflexivity).
    rewrite !firstn_snoc by lia. rewrite <- !app_assoc. cbn [app].
    rewrite (b64_enc_app3 (Z.to_nat k)) by (rewrite firstn_length_le; lia).
    rewrite map_app, !nth_bz.
    replace (S (Z.to_nat (3 * k))) with (Z.to_nat (3 * k + 1)) by lia.
    reflexivity.
  Qed.

  Lemma et_step1 : forall k, 0 <= k -> l = 3 * k + 1 ->
    et_pre (k + 1) = et_pre k ++ map (Z_to_bv 8) (b64_enc [bv_unsigned (nth (Z.to_nat (3 * k)) bs (Z_to_bv 8 0))]).
  Proof.
    intros k Hk Hkl. unfold et_pre.
    assert (LB : Z.of_nat (length (map bv_unsigned bs)) = l) by (rewrite length_map; exact HN).
    replace (firstn (Z.to_nat (3 * (k + 1))) (map bv_unsigned bs))
      with (firstn (S (Z.to_nat (3 * k))) (map bv_unsigned bs)) by (rewrite !firstn_all2 by lia; reflexivity).
    rewrite !firstn_snoc by lia.
    rewrite (b64_enc_app3 (Z.to_nat k)) by (rewrite firstn_length_le; lia).
    rewrite map_app, !nth_bz.
    reflexivity.
  Qed.

  Ltac et_st WR PRE off :=
    let H := fresh "HS" in
    pose proof (wr_at_store_ok rsegs _ _ _ off 1 WR ltac:(lia) ltac:(lia)) as H;
    zstep; crt_out PRE.

  Lemma et_iter : forall (Q : machine_state -> Prop) (k : Z) (m : word -> option byte)
    (y23 y24 y25 y26 y27 y29 y31 : word),
    0 <= k -> 3 * k < l -> et_facts m k ->
    (forall (m' : word -> option byte) (z23 z24 z25 z26 z27 z29 z30 z31 : word),
       z29 = Z_to_bv 64 (want + 4 * k) -> z30 = Z_to_bv 64 (want + 4 * k + 4) -> et_facts m' (k + 1) ->
       evt rsegs Q (XS 0x13bb4 (Z_to_bv 64 (3 * k + 3)) z23 z24 z25 z26 z27 z29 z30 z31 m')) ->
    evt rsegs Q (XS 0x13a80 (Z_to_bv 64 (3 * k)) y23 y24 y25 y26 y27 y29 (Z_to_bv 64 (want + 4 * k)) y31 m).
  Proof.
    intros Q k m y23 y24 y25 y26 y27 y29 y31 Hk Hkl (MU & WM & MI & PRE) CONT.
    pose proof (bytes_at_bound _ _ _ _ DATA0) as BD. rewrite HN in BD.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    assert (HM : 4 * k + 4 <= En) by (rewrite HE; Z.div_mod_to_equations; lia).
    assert (DATA : bytes_at rsegs m b bs).
    { eapply bytes_at_transport; [exact DATA0 | exact MU |]. cbn [disjoint_from]. rewrite HN. lia. }
    pose proof (wr_at_transport rsegs m0 m want (En + 1) WR0 WM) as WR.
    pose proof (et_pre_len k Hk ltac:(lia)) as LP.
    remember (nth (Z.to_nat (3 * k)) bs (Z_to_bv 8 0)) as c0 eqn:EC0.
    pose proof (rd1 m b bs (3 * k) c0 DATA ltac:(lia) (eq_sym EC0)) as RD0.
    pose proof (byte_rng c0) as R0.
    destruct (Z_lt_ge_dec (3 * k + 1) l) as [L1 | L1].
    - remember (nth (Z.to_nat (3 * k + 1)) bs (Z_to_bv 8 0)) as c1 eqn:EC1.
      pose proof (rd1 m b bs (3 * k + 1) c1 DATA ltac:(lia) (eq_sym EC1)) as RD1.
      pose proof (byte_rng c1) as R1.
      destruct (Z_lt_ge_dec (3 * k + 2) l) as [L2 | L2].
      + remember (nth (Z.to_nat (3 * k + 2)) bs (Z_to_bv 8 0)) as c2 eqn:EC2.
        pose proof (rd1 m b bs (3 * k + 2) c2 DATA ltac:(lia) (eq_sym EC2)) as RD2.
        pose proof (byte_rng c2) as R2.
        clear DATA.
        zstep. nb.
        zstep. zstep. zstep.
        zstep. zstep. br_f.
        zstep. nb.
        zstep. zstep. zstep.
        zstep. zstep. br_f.
        zstep. nb.
        zstep. zstep. zstep.
        zstep.
        apply chA; [exact R0 |]. intros d Hd. subst d.
        zstep. nb.
        zstep. zstep. zstep. zstep.
        et_st WR PRE (4 * k).
        rewrite (vB (bv_unsigned c0) (bv_unsigned c1) R0 R1).
        apply chB; [Z.div_mod_to_equations; lia |]. intros d Hd. subst d.
        zstep. zstep. nb.
        et_st WR PRE (4 * k + 1).
        zstep. br_f.
        zstep. zstep. zstep. zstep.
        rewrite (sh60 (bv_unsigned c1) R1), (vC (bv_unsigned c1) (bv_unsigned c2) R1 R2).
        apply chC; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |]. intros d Hd. subst d.
        zstep. zstep. nb.
        et_st WR PRE (4 * k + 2).
        zstep. br_f.
        zstep. rewrite (vD (bv_unsigned c2) ltac:(lia)).
        apply chD; [Z.div_mod_to_equations; lia |]. intros d Hd. subst d.
        zstep. zstep. nb.
        et_st WR PRE (4 * k + 3).
        zstep. zstep.
        eapply CONT; [f_equal; lia | f_equal; lia |].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        eapply bytes_at_ext; [exact PRE|].
        rewrite (et_step3 k Hk ltac:(lia)), <- EC0, <- EC1, <- EC2. cbn [b64_enc map].
        rewrite !le1_chr by (Z.div_mod_to_equations; lia). rewrite <- !app_assoc. reflexivity.
      + assert (EL : l = 3 * k + 2) by lia.
        clear DATA.
        zstep. nb.
        zstep. zstep. zstep.
        zstep. zstep. br_f.
        zstep. nb.
        zstep. zstep. zstep.
        zstep. zstep. br_t.
        zstep.
        zstep.
        apply chA; [exact R0 |]. intros d Hd. subst d.
        zstep. nb.
        zstep. zstep. zstep. zstep.
        et_st WR PRE (4 * k).
        rewrite (vB (bv_unsigned c0) (bv_unsigned c1) R0 R1).
        apply chB; [Z.div_mod_to_equations; lia |]. intros d Hd. subst d.
        zstep. zstep. nb.
        et_st WR PRE (4 * k + 1).
        zstep. br_f.
        zstep. zstep. zstep. zstep.
        rewrite (sh60 (bv_unsigned c1) R1), (vC0 (bv_unsigned c1)).
        apply chC; [Z.div_mod_to_equations; lia | lia |]. intros d Hd. subst d.
        zstep. zstep. nb.
        et_st WR PRE (4 * k + 2).
        zstep. br_t.
        zstep.
        zstep. zstep. nb.
        et_st WR PRE (4 * k + 3).
        zstep. zstep.
        eapply CONT; [f_equal; lia | f_equal; lia |].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        eapply bytes_at_ext; [exact PRE|].
        rewrite (et_step2 k Hk EL), <- EC0, <- EC1. cbn [b64_enc map].
        rewrite ?Z.add_0_r, !le1_chr by (Z.div_mod_to_equations; lia). rewrite (le1_lit 61) by lia.
        rewrite <- !app_assoc. reflexivity.
    - assert (EL : l = 3 * k + 1) by lia.
      clear DATA.
      zstep. nb.
      zstep. zstep. zstep.
      zstep. zstep. br_t.
      zstep.
      zstep. zstep. br_t.
      zstep.
      zstep.
      apply chA; [exact R0 |]. intros d Hd. subst d.
      zstep. nb.
      zstep. zstep. zstep. zstep.
      et_st WR PRE (4 * k).
      rewrite (vB0 (bv_unsigned c0) R0).
      apply chB; [Z.div_mod_to_equations; lia |]. intros d Hd. subst d.
      zstep. zstep. nb.
      et_st WR PRE (4 * k + 1).
      zstep. br_t.
      zstep.
      zstep. zstep. nb.
      et_st WR PRE (4 * k + 2).
      zstep. br_t.
      zstep.
      zstep. zstep. nb.
      et_st WR PRE (4 * k + 3).
      zstep. zstep.
      eapply CONT; [f_equal; lia | f_equal; lia |].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      eapply bytes_at_ext; [exact PRE|].
      rewrite (et_step1 k Hk EL), <- EC0. cbn [b64_enc map].
      rewrite !le1_chr by (Z.div_mod_to_equations; lia). rewrite (le1_lit 61) by lia.
      rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma et_fin : forall (m : word -> option byte)
    (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    x29 = Z_to_bv 64 (want + En) ->
    munch [(want, want + (En + 1))] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    bytes_at rsegs m want (map (Z_to_bv 8) (b64_enc (map bv_unsigned bs))) ->
    evt rsegs et_post (MS (mkR ra sp gp tp x5 x6 x7 s0 (Z_to_bv 64 want) x10 x11 x12 x13 x14 x15 x16 x17
                            s2 (Z_to_bv 64 l) (Z_to_bv 64 b) s5 s6 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x13c18) fc None m (seg_rom rsegs)).
  Proof.
    intros m x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 -> MU WM MI PRE.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    assert (HE0 : 0 <= En) by (rewrite HE; Z.div_mod_to_equations; lia).
    pose proof (wr_at_transport rsegs m0 m want (En + 1) WR0 WM) as WR.
    assert (LQ : Z.of_nat (length (b64_enc (map bv_unsigned bs))) = En)
      by (rewrite enc_len_Z, length_map, HN, HE; reflexivity).
    assert (LP : Z.of_nat (length (map (Z_to_bv 8) (b64_enc (map bv_unsigned bs)))) = En)
      by (rewrite length_map; exact LQ).
    pose proof (wr_at_store_ok rsegs _ _ _ En 1 WR ltac:(lia) ltac:(lia)) as HS.
    zstep. crt_out PRE.
    apply evt_done. unfold et_post. do 21 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply rw_cells_one.
    - eapply bytes_at_ext; [exact PRE|]. rewrite (le1_lit 0) by lia. reflexivity.
    - rewrite length_app, length_map. cbn [length]. lia.
    - rewrite Z2Nat.id by lia. exact WR.
  Qed.

  Lemma et_loop : forall (n : nat) (k i p : Z) (m : word -> option byte) (y23 y24 y25 y26 y27 y29 y31 : word),
    Z.to_nat (l - 3 * k) = n -> 0 <= k -> 3 * k < l -> p = want + 4 * k -> i = 3 * k -> et_facts m k ->
    evt rsegs et_post (XS 0x13a80 (Z_to_bv 64 i) y23 y24 y25 y26 y27 y29 (Z_to_bv 64 p) y31 m).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros k i p m y23 y24 y25 y26 y27 y29 y31 Hn Hk Hkl -> -> FA.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    apply (et_iter _ k m y23 y24 y25 y26 y27 y29 y31 Hk Hkl FA).
    intros m' z23 z24 z25 z26 z27 z29 z30 z31 -> -> FA'.
    zstep. if_cases BR; zify_cond BR.
    - eapply (IH (Z.to_nat (l - 3 * (k + 1))) ltac:(lia) (k + 1)); [reflexivity | lia | lia | ring | ring | exact FA'].
    - zstep. zstep.
      destruct FA' as (MU & WM & MI & PRE).
      eapply et_fin; [ | exact MU | exact WM | exact MI | ].
      + f_equal. rewrite HE. Z.div_mod_to_equations. lia.
      + eapply bytes_at_ext; [exact PRE|]. unfold et_pre. rewrite firstn_all2; [reflexivity|].
        rewrite length_map. lia.
  Qed.

  Lemma et_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    mem_inv rsegs m0 ->
    evt rsegs et_post (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7
                            s2 (Z_to_bv 64 l) (Z_to_bv 64 b) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x13a44) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 MI.
    pose proof (bytes_at_bound _ _ _ _ DATA0) as BD. rewrite HN in BD.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    zstep. zstep. if_cases BZ; zify_cond BZ.
    - assert (EN : En = 0) by (rewrite HE, BZ; reflexivity).
      assert (EB : bs = []) by (apply length_zero_iff_nil; lia).
      eapply et_fin; [ | apply munch_refl | apply wmono_refl | exact MI | ].
      + rewrite EN, Z.add_0_r. reflexivity.
      + rewrite EB. apply bytes_at_nil. lia.
    - do 13 zstep.
      rewrite (zb_lxor_ones b) by lia.
      eapply (et_loop (Z.to_nat (l - 3 * 0)) 0); [reflexivity | lia | lia | ring | ring | ].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
      change (et_pre 0) with (@nil byte). apply bytes_at_nil. lia.
  Qed.

End ExpectedText.

Theorem crt_expected_text :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (want b l : Z) (bs junk : list byte),
    Z.of_nat (length bs) = l -> l < 2^60 ->
    bytes_at rsegs m b bs ->
    rw_cells rsegs m want [CB (Z.to_nat ((l + 2) / 3 * 4 + 1)) junk] ->
    want + ((l + 2) / 3 * 4 + 1) <= b \/ b + l <= want ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 want) a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 l) (Z_to_bv 64 b) s5 s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13c1c) fc None m' (seg_rom rsegs) /\
         munch [(want, want + ((l + 2) / 3 * 4 + 1))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' want
           [CB (Z.to_nat ((l + 2) / 3 * 4 + 1)) (map (Z_to_bv 8) (b64_enc (map bv_unsigned bs)) ++ [Z_to_bv 8 0])])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 l) (Z_to_bv 64 b) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a44) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m want b l bs junk
    HN HL DATA RW DJ MI.
  destruct RW as [_ WR]. cbn [cells_size csize] in WR.
  rewrite Nat.add_0_r, Z2Nat.id in WR by (Z.div_mod_to_equations; lia).
  exact (et_main ra sp gp tp s0 s2 s5 s6 F fc want b l ((l + 2) / 3 * 4) bs m HN HL eq_refl DATA WR DJ
           t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 MI).
Qed.

Lemma ws_bit : forall c, 0 <= c <= 32 ->
  (Z.land (Z.shiftr 4294977024 (c mod 64)) 1 = 0 <-> b64_ws c = false).
Proof.
  intros c Hc.
  assert (C : forallb (fun n => Bool.eqb (Z.land (Z.shiftr 4294977024 (Z.of_nat n mod 64)) 1 =? 0)
                                         (negb (b64_ws (Z.of_nat n)))) (seq 0 33) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat c) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. apply Bool.eqb_prop in C.
  destruct (Z.eqb_spec (Z.land (Z.shiftr 4294977024 (c mod 64)) 1) 0) as [E|E]; destruct (b64_ws c);
    cbn in C; split; intros; congruence.
Qed.

Lemma land3 : forall z, 0 <= z -> Z.land z 3 = z mod 4.
Proof. intros z Hz. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Section Canonical.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (same t : Z) (tb junk : list byte) (m0 : word -> option byte).
  Hypothesis NZ : ~ In (Z_to_bv 8 0) tb.
  Hypothesis TXT0 : bytes_at rsegs m0 t (tb ++ [Z_to_bv 8 0]).
  Hypothesis JK0 : bytes_at rsegs m0 same junk.
  Hypothesis LJ : length junk = S (length tb).
  Hypothesis WR0 : wr_at rsegs m0 same (Z.of_nat (length tb) + 1).
  Hypothesis DJ : same + Z.of_nat (length tb) + 1 <= t \/ t + Z.of_nat (length tb) + 1 <= same.

  Definition cs_pre (i : Z) : list Z := b64_strip (firstn (Z.to_nat i) (map bv_unsigned tb)).
  Definition cs_j (i : Z) : Z := Z.of_nat (length (cs_pre i)).

  Definition cs_facts (m : word -> option byte) (i : Z) : Prop :=
    munch [(same, same + Z.of_nat (length tb) + 1)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
    bytes_at rsegs m same (map (Z_to_bv 8) (cs_pre i)) /\
    bytes_at rsegs m (same + cs_j i) (skipn (length (cs_pre i)) junk).

  Definition cs_post : machine_state -> Prop :=
    fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length (b64_strip (map bv_unsigned tb))) mod 4))
                    a1' a2' a3' a4' a5' a6' a7 (Z_to_bv 64 same) s3 s4 (Z_to_bv 64 (t + Z.of_nat (length tb) - 1))
                    s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13c94) fc None m' (seg_rom rsegs) /\
      munch [(same, same + Z.of_nat (length tb) + 1)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' same
        [CB (S (length (b64_strip (map bv_unsigned tb))))
            (map (Z_to_bv 8) (b64_strip (map bv_unsigned tb)) ++ [Z_to_bv 8 0]);
         CB (length tb - length (b64_strip (map bv_unsigned tb)))
            (skipn (S (length (b64_strip (map bv_unsigned tb)))) junk)].

  Abbreviation CS pc x10 x15 x16 x21 m :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 (18446744073709551615 - same)) (Z_to_bv 64 32)
       (Z_to_bv 64 (-1)) (Z_to_bv 64 4294977024) x15 x16 a7
       (Z_to_bv 64 same) s3 s4 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma cs_len_le : forall i, 0 <= i -> (length (cs_pre i) <= Z.to_nat i)%nat.
  Proof.
    intros i Hi. unfold cs_pre. eapply Nat.le_trans; [apply strip_len|].
    rewrite length_firstn. lia.
  Qed.

  Lemma cs_step : forall i, 0 <= i < Z.of_nat (length tb) ->
    cs_pre (i + 1) = cs_pre i ++ (if b64_ws (bv_unsigned (nth (Z.to_nat i) tb (Z_to_bv 8 0))) then []
                                  else [bv_unsigned (nth (Z.to_nat i) tb (Z_to_bv 8 0))]).
  Proof.
    intros i Hi. unfold cs_pre.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite firstn_snoc by (rewrite length_map; lia).
    rewrite strip_app, nth_bz, b64_strip_cons. destruct (b64_ws _); reflexivity.
  Qed.

  Lemma cs_iter : forall (Q : machine_state -> Prop) (i : Z) (m : word -> option byte) (x15 x16 : word),
    0 <= i < Z.of_nat (length tb) -> cs_facts m i ->
    (forall (m' : word -> option byte) (z10 z15 z16 z21 : word), z10 = Z_to_bv 64 (cs_j (i + 1)) ->
       z21 = Z_to_bv 64 (t + i) -> cs_facts m' (i + 1) ->
       evt rsegs Q (CS 0x13c4c z10 z15 z16 z21 m')) ->
    evt rsegs Q (CS 0x13c4c (Z_to_bv 64 (cs_j i)) x15 x16 (Z_to_bv 64 (t + i - 1)) m).
  Proof.
    intros Q i m x15 x16 Hi (MU & WM & MI & PRE & TAIL) CONT.
    pose proof (bytes_at_bound _ _ _ _ TXT0) as BT. rewrite length_app in BT. cbn [length] in BT.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    assert (TXT : bytes_at rsegs m t (tb ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact TXT0 | exact MU |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    pose proof (wr_at_transport rsegs m0 m same _ WR0 WM) as WR.
    pose proof (cs_len_le i ltac:(lia)) as SL.
    assert (Hj : 0 <= cs_j i <= i) by (unfold cs_j; lia).
    assert (LPi : Z.of_nat (length (cs_pre i)) = cs_j i) by reflexivity.
    remember (nth (Z.to_nat i) tb (Z_to_bv 8 0)) as c eqn:EC.
    pose proof (rd1 m t (tb ++ [Z_to_bv 8 0]) i c TXT ltac:(rewrite length_app; cbn [length]; lia)
                  ltac:(rewrite app_nth1 by lia; exact (eq_sym EC))) as RD.
    clear TXT.
    assert (CNZ : bv_unsigned c <> 0).
    { apply byte_nz. intros E. apply NZ. rewrite <- E, EC. apply nth_In. lia. }
    pose proof (byte_rng c) as RC.
    pose proof (cs_step i Hi) as STEP. rewrite <- EC in STEP.
    zstep. zstep. if_cases B1; zify_cond B1.
    - assert (WS : b64_ws (bv_unsigned c) = false) by (unfold b64_ws; decide_tests; reflexivity).
      rewrite WS in STEP.
      zstep. nb.
      zstep. zstep.
      pose proof (bytes_at_skipn_S m (same + cs_j i) junk (length (cs_pre i)) TAIL ltac:(lia)) as TAIL1. clear TAIL.
      pose proof (wr_at_store_ok rsegs _ _ _ (cs_j i) 1 WR ltac:(lia) ltac:(lia)) as HS.
      zstep. crt_out PRE.
      zstep. zstep. zstep. br_t.
      eapply CONT.
      + f_equal. unfold cs_j. rewrite STEP, length_app. cbn [length]. lia.
      + f_equal. lia.
      + split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split.
        * eapply bytes_at_ext; [exact PRE|]. rewrite STEP, map_app, le1_byte. cbn [map].
          rewrite byte_rt. reflexivity.
        * replace (cs_j (i + 1)) with (cs_j i + 1) by (unfold cs_j; rewrite STEP, length_app; cbn [length]; lia).
          replace (length (cs_pre (i + 1))) with (S (length (cs_pre i))) by (rewrite STEP, length_app; cbn [length]; lia).
          rewrite Z.add_assoc. exact TAIL1.
    - zstep. zstep. zstep. if_cases B2; zify_cond B2.
      + assert (WS : b64_ws (bv_unsigned c) = false) by (apply (ws_bit (bv_unsigned c) ltac:(lia)); exact B2).
        rewrite WS in STEP.
        zstep. br_f.
        zstep. nb.
        zstep. zstep.
        pose proof (bytes_at_skipn_S m (same + cs_j i) junk (length (cs_pre i)) TAIL ltac:(lia)) as TAIL1. clear TAIL.
        pose proof (wr_at_store_ok rsegs _ _ _ (cs_j i) 1 WR ltac:(lia) ltac:(lia)) as HS.
        zstep. crt_out PRE.
        zstep. zstep. zstep. br_t.
        eapply CONT.
        * f_equal. unfold cs_j. rewrite STEP, length_app. cbn [length]. lia.
        * f_equal. lia.
        * split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split.
          -- eapply bytes_at_ext; [exact PRE|]. rewrite STEP, map_app, le1_byte. cbn [map].
             rewrite byte_rt. reflexivity.
          -- replace (cs_j (i + 1)) with (cs_j i + 1) by (unfold cs_j; rewrite STEP, length_app; cbn [length]; lia).
             replace (length (cs_pre (i + 1))) with (S (length (cs_pre i))) by (rewrite STEP, length_app; cbn [length]; lia).
             rewrite Z.add_assoc. exact TAIL1.
      + assert (WS : b64_ws (bv_unsigned c) = true).
        { destruct (b64_ws (bv_unsigned c)) eqn:W; [reflexivity|]. exfalso. apply B2.
          apply (ws_bit (bv_unsigned c) ltac:(lia)). exact W. }
        rewrite WS, app_nil_r in STEP.
        zstep. zstep. br_t.
        eapply CONT.
        * f_equal. unfold cs_j. rewrite STEP. reflexivity.
        * f_equal. lia.
        * split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
          unfold cs_j. rewrite STEP. split; [exact PRE | exact TAIL].
  Qed.

  Lemma cs_exit : forall (m : word -> option byte) (x15 x16 : word),
    cs_facts m (Z.of_nat (length tb)) ->
    evt rsegs cs_post (CS 0x13c4c (Z_to_bv 64 (cs_j (Z.of_nat (length tb)))) x15 x16
                         (Z_to_bv 64 (t + Z.of_nat (length tb) - 1)) m).
  Proof.
    intros m x15 x16 (MU & WM & MI & PRE & TAIL).
    pose proof (bytes_at_bound _ _ _ _ TXT0) as BT. rewrite length_app in BT. cbn [length] in BT.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    assert (TXT : bytes_at rsegs m t (tb ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact TXT0 | exact MU |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    pose proof (wr_at_transport rsegs m0 m same _ WR0 WM) as WR.
    assert (EP : cs_pre (Z.of_nat (length tb)) = b64_strip (map bv_unsigned tb)).
    { unfold cs_pre. rewrite Nat2Z.id, firstn_all2 by (rewrite length_map; lia). reflexivity. }
    pose proof (strip_len (map bv_unsigned tb)) as SL. rewrite length_map in SL.
    assert (HJ : cs_j (Z.of_nat (length tb)) = Z.of_nat (length (b64_strip (map bv_unsigned tb))))
      by (unfold cs_j; rewrite EP; reflexivity).
    rewrite HJ. rewrite HJ, EP in TAIL. rewrite EP in PRE.
    pose proof (rd1 m t (tb ++ [Z_to_bv 8 0]) (Z.of_nat (length tb)) (Z_to_bv 8 0) TXT
                  ltac:(rewrite length_app; cbn [length]; lia)
                  ltac:(rewrite app_nth2 by lia; rewrite Nat2Z.id, Nat.sub_diag; reflexivity)) as RD.
    clear TXT.
    pose proof (bytes_at_skipn_S m (same + Z.of_nat (length (b64_strip (map bv_unsigned tb)))) junk
                  (length (b64_strip (map bv_unsigned tb))) TAIL ltac:(lia)) as TAIL1. clear TAIL.
    pose proof (wr_at_store_ok rsegs _ _ _ (Z.of_nat (length (b64_strip (map bv_unsigned tb)))) 1 WR
                  ltac:(lia) ltac:(lia)) as HS.
    zstep. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    zstep. br_f.
    zstep. zstep. zstep. br_t.
    zstep. br_t.
    zstep. nb.
    zstep. zstep.
    zstep. crt_out PRE.
    rewrite land3 by lia.
    apply evt_done. unfold cs_post. do 7 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply rw_cells_two.
    - apply bytes_at_app. split.
      + eapply bytes_at_ext; [exact PRE|]. rewrite (le1_lit 0) by lia. reflexivity.
      + rewrite length_app, length_map. cbn [length].
        replace (same + Z.of_nat (length (b64_strip (map bv_unsigned tb)) + 1))
          with (same + Z.of_nat (length (b64_strip (map bv_unsigned tb))) + 1) by lia.
        exact TAIL1.
    - rewrite length_app, length_map. cbn [length]. lia.
    - rewrite length_skipn. lia.
    - replace (Z.of_nat (S (length (b64_strip (map bv_unsigned tb))) +
                         (length tb - length (b64_strip (map bv_unsigned tb)))))
        with (Z.of_nat (length tb) + 1) by lia.
      exact WR.
  Qed.

  Lemma cs_loop : forall (n : nat) (i p q : Z) (m : word -> option byte) (x15 x16 : word),
    Z.to_nat (Z.of_nat (length tb) - i) = n -> 0 <= i <= Z.of_nat (length tb) -> p = cs_j i -> q = t + i - 1 ->
    cs_facts m i ->
    evt rsegs cs_post (CS 0x13c4c (Z_to_bv 64 p) x15 x16 (Z_to_bv 64 q) m).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros i p q m x15 x16 Hn Hi -> -> FA.
    destruct (Z.eq_dec i (Z.of_nat (length tb))) as [-> | Hne].
    - apply cs_exit. exact FA.
    - apply (cs_iter _ i m x15 x16 ltac:(lia) FA).
      intros m' z10 z15 z16 z21 -> -> FA'.
      eapply (IH (Z.to_nat (Z.of_nat (length tb) - (i + 1))) ltac:(lia) (i + 1));
        [reflexivity | lia | reflexivity | ring | exact FA'].
  Qed.

  Lemma cs_main : forall (a0 a1 a2 a3 a4 a5 a6 : word),
    mem_inv rsegs m0 ->
    evt rsegs cs_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 same) s3 s4
                            (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x13c2c) fc None m0 (seg_rom rsegs)).
  Proof.
    intros a0 a1 a2 a3 a4 a5 a6 MI.
    pose proof (bytes_at_bound _ _ _ _ TXT0) as BT. rewrite length_app in BT. cbn [length] in BT.
    pose proof (proj1 WR0) as Hw0. pose proof (proj1 (proj2 WR0)) as HwE.
    do 8 zstep.
    rewrite (zb_lxor_ones same) by lia.
    eapply (cs_loop _ 0); [reflexivity | lia | reflexivity | ring | ].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    change (cs_pre 0) with (@nil Z). change (cs_j 0) with 0. cbn [map length skipn].
    split; [apply bytes_at_nil; lia|]. rewrite Z.add_0_r. exact JK0.
  Qed.
End Canonical.

Theorem crt_canonical :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (same t : Z) (tb junk : list byte),
    ~ In (Z_to_bv 8 0) tb ->
    bytes_at rsegs m t (tb ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs m same [CB (S (length tb)) junk] ->
    same + Z.of_nat (length tb) + 1 <= t \/ t + Z.of_nat (length tb) + 1 <= same ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (Z.of_nat (length (b64_strip (map bv_unsigned tb))) mod 4))
                       a1' a2' a3' a4' a5' a6' a7 (Z_to_bv 64 same) s3 s4 (Z_to_bv 64 (t + Z.of_nat (length tb) - 1))
                       s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c94) fc None m' (seg_rom rsegs) /\
         munch [(same, same + Z.of_nat (length tb) + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' same
           [CB (S (length (b64_strip (map bv_unsigned tb))))
               (map (Z_to_bv 8) (b64_strip (map bv_unsigned tb)) ++ [Z_to_bv 8 0]);
            CB (length tb - length (b64_strip (map bv_unsigned tb)))
               (skipn (S (length (b64_strip (map bv_unsigned tb)))) junk)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 same) s3 s4 (Z_to_bv 64 t)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c2c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m same t tb junk
    NZ TXT RW DJ MI.
  destruct RW as [[[LJ _] JK] WR]. cbn [cells_bytes cbytes] in JK. rewrite app_nil_r in JK.
  cbn [cells_size csize] in WR. rewrite Nat.add_0_r, Nat2Z.inj_succ in WR. rewrite <- Z.add_1_r in WR.
  exact (cs_main ra sp gp tp t0 t1 t2 s0 s1 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc same t tb junk m
           NZ TXT JK LJ WR DJ a0 a1 a2 a3 a4 a5 a6 MI).
Qed.
