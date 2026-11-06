From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts.
Import ListNotations.
Open Scope Z_scope.

Definition asw_post (ra sp gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t want six n : Z) (tb : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 r : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 six) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 want) s3 r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13910) fc None m' (seg_rom rsegs) /\
    munch [(six, six + Z.max n 1); (want, want + (n / 4 * 3 + 3))] m m' /\ wmono rsegs m m' /\
    bytes_at rsegs m' t (tb ++ [Z_to_bv 8 0]) /\
    match b64_dec (map (fun b : byte => bv_unsigned b) tb) with
    | Some bs => r = Z_to_bv 64 (Z.of_nat (length bs)) /\ bytes_at rsegs m' want (map (Z_to_bv 8) bs)
    | None => r = Z_to_bv 64 (2^64 - 1)
    end.

Lemma bv8_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma map_bv8 : forall l : list byte, map (fun x : byte => Z_to_bv 8 (bv_unsigned x)) l = l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite bv8_self, IH. reflexivity. Qed.

Lemma u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^8) with 256. lia. Qed.

Lemma land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land15 : forall x, Z.land x 15 = x mod 16.
Proof. intros x. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma swrap_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma brute1 : forall (N : Z) (f g : Z -> Z),
  forallb (fun x => f x =? g x) (map Z.of_nat (seq 0 (Z.to_nat N))) = true ->
  forall x, 0 <= x < N -> f x = g x.
Proof.
  intros N f g H x Hx. rewrite forallb_forall in H.
  assert (I : In x (map Z.of_nat (seq 0 (Z.to_nat N))))
    by (apply in_map_iff; exists (Z.to_nat x); split; [lia | apply in_seq; lia]).
  apply Z.eqb_eq. exact (H x I).
Qed.

Lemma brute2 : forall (N : Z) (f g : Z -> Z -> Z),
  forallb (fun x => forallb (fun y => f x y =? g x y) (map Z.of_nat (seq 0 (Z.to_nat N))))
    (map Z.of_nat (seq 0 (Z.to_nat N))) = true ->
  forall x y, 0 <= x < N -> 0 <= y < N -> f x y = g x y.
Proof.
  intros N f g H x y Hx Hy. rewrite forallb_forall in H.
  assert (Ix : In x (map Z.of_nat (seq 0 (Z.to_nat N))))
    by (apply in_map_iff; exists (Z.to_nat x); split; [lia | apply in_seq; lia]).
  assert (Iy : In y (map Z.of_nat (seq 0 (Z.to_nat N))))
    by (apply in_map_iff; exists (Z.to_nat y); split; [lia | apply in_seq; lia]).
  specialize (H x Ix). rewrite forallb_forall in H. apply Z.eqb_eq. exact (H y Iy).
Qed.

Lemma t1_val : forall c, 1 <= c <= 255 ->
  Z.lor ((Z.b2z ((c + -47) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616) 63 =
  if c =? 47 then 63 else 18446744073709551615.
Proof.
  intros c Hc.
  exact (brute1 256
    (fun c => Z.lor ((Z.b2z ((c + -47) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616) 63)
    (fun c => if c =? 47 then 63 else 18446744073709551615) ltac:(vm_compute; reflexivity) c ltac:(lia)).
Qed.

Lemma ws_bit : forall c, 0 <= c <= 61 ->
  Z.land (Z.shiftr 4294977024 (c mod 64)) 1 = if b64_ws c then 1 else 0.
Proof.
  intros c Hc.
  exact (brute1 62 (fun c => Z.land (Z.shiftr 4294977024 (c mod 64)) 1) (fun c => if b64_ws c then 1 else 0)
    ltac:(vm_compute; reflexivity) c ltac:(lia)).
Qed.

Lemma ws_bit1 : forall c, 0 <= c <= 61 -> b64_ws c = true -> Z.land (Z.shiftr 4294977024 (c mod 64)) 1 = 1.
Proof. intros c Hc H. rewrite ws_bit by exact Hc. rewrite H. reflexivity. Qed.

Lemma ws_bit0 : forall c, 0 <= c <= 61 -> b64_ws c = false -> Z.land (Z.shiftr 4294977024 (c mod 64)) 1 = 0.
Proof. intros c Hc H. rewrite ws_bit by exact Hc. rewrite H. reflexivity. Qed.

Lemma flag_val : forall pad, 0 <= pad < 2^31 ->
  Z.lxor (Z.b2z (Z.lxor pad 9223372036854775808 <? 9223372036854775811)) 1 = if pad <=? 2 then 0 else 1.
Proof.
  intros pad Hp.
  change 9223372036854775808 with (2^63).
  rewrite zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec (pad + 2^63) 9223372036854775811) as [H|H];
  destruct (Z.leb_spec pad 2) as [H'|H']; cbn; try reflexivity; lia.
Qed.

Lemma sgn64 : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma le1_mod : forall z b, 0 <= b < 256 -> z mod 256 = b -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 b].
Proof.
  intros z b Hb Hz. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256. rewrite Hz.
  symmetry. apply Z.mod_small. exact Hb.
Qed.

Lemma g0 : forall a b, 0 <= a < 64 -> 0 <= b < 64 ->
  Z.lor (Z.shiftr b 4) (Z.shiftl a 2 mod 18446744073709551616) mod 256 = a * 4 + b / 16.
Proof.
  intros a b Ha Hb.
  exact (brute2 64 (fun a b => Z.lor (Z.shiftr b 4) (Z.shiftl a 2 mod 18446744073709551616) mod 256)
    (fun a b => a * 4 + b / 16) ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Lemma g1 : forall a b, 0 <= a < 64 -> 0 <= b < 64 ->
  Z.lor (Z.shiftr b 2) (Z.shiftl a 4 mod 18446744073709551616) mod 256 = a mod 16 * 16 + b / 4.
Proof.
  intros a b Ha Hb.
  exact (brute2 64 (fun a b => Z.lor (Z.shiftr b 2) (Z.shiftl a 4 mod 18446744073709551616) mod 256)
    (fun a b => a mod 16 * 16 + b / 4) ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Lemma g2 : forall a b, 0 <= a < 64 -> 0 <= b < 64 ->
  Z.lor (Z.shiftl a 6 mod 18446744073709551616) b mod 256 = a mod 4 * 64 + b.
Proof.
  intros a b Ha Hb.
  exact (brute2 64 (fun a b => Z.lor (Z.shiftl a 6 mod 18446744073709551616) b mod 256)
    (fun a b => a mod 4 * 64 + b) ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Lemma g2r : forall a b, 0 <= a < 64 -> 0 <= b < 64 ->
  Z.lor b (Z.shiftl a 6 mod 18446744073709551616) mod 256 = a mod 4 * 64 + b.
Proof.
  intros a b Ha Hb.
  exact (brute2 64 (fun a b => Z.lor b (Z.shiftl a 6 mod 18446744073709551616) mod 256)
    (fun a b => a mod 4 * 64 + b) ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Ltac mlia2 := Z.div_mod_to_equations; lia.
Ltac brt := let H := fresh "BR" in if_cases H; zify_cond H; [ | exfalso; mlia2 ].
Ltac brfs := let H := fresh "BR" in if_cases H; [ exfalso; zify_cond H; rewrite ?sgn64 in H by lia; mlia2 | ].
Ltac brf := let H := fresh "BR" in if_cases H; zify_cond H; [ exfalso; mlia2 | ].
Ltac fix_u8 := cbv beta; repeat match goal with |- context [bv_unsigned (Z_to_bv 8 ?x)] => rewrite (u8 x) by lia end.
Ltac fix_le1 B :=
  lazymatch goal with
  | |- context [le1 (Z_to_bv 64 ?z)] =>
      rewrite (le1_mod z B) by (first [ mlia2 | apply g0; lia | apply g1; lia | apply g2; lia | apply g2r; lia ])
  end.
Ltac dec :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => first [ rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia ]
  | |- context [Z.ltb ?x ?y] => first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]
  | |- context [Z.leb ?x ?y] => first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]
  end; cbn [andb orb negb].

Lemma b64v_none : forall c, ~ (65 <= c <= 90) -> ~ (97 <= c <= 122) -> ~ (48 <= c <= 57) -> c <> 43 -> c <> 47 ->
  b64v c = None.
Proof.
  intros c H1 H2 H3 H4 H5. unfold b64v.
  destruct (Z.leb_spec 65 c), (Z.leb_spec c 90), (Z.leb_spec 97 c), (Z.leb_spec c 122),
    (Z.leb_spec 48 c), (Z.leb_spec c 57); cbn [andb]; try (exfalso; lia);
    rewrite (proj2 (Z.eqb_neq c 43) H4), (proj2 (Z.eqb_neq c 47) H5); reflexivity.
Qed.

Lemma b64_ws_false : forall c, c <> 32 -> c <> 9 -> c <> 10 -> c <> 13 -> b64_ws c = false.
Proof.
  intros c H1 H2 H3 H4. unfold b64_ws.
  rewrite (proj2 (Z.eqb_neq c 32) H1), (proj2 (Z.eqb_neq c 9) H2), (proj2 (Z.eqb_neq c 10) H3),
    (proj2 (Z.eqb_neq c 13) H4). reflexivity.
Qed.

Definition tvrel (c tv : Z) : Prop :=
  match b64v c with Some v => tv = v | None => tv = 18446744073709551615 end.

Lemma fs1 : forall {A} (l : list A) j d, (j < length l)%nat -> firstn 1 (skipn j l) = [nth j l d].
Proof. induction l as [|a l IH]; intros [|j] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma rd_at : forall m A xs j, bytes_at rsegs m A (map (Z_to_bv 8) xs) -> (j < length xs)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat j)) 1 = Some [Z_to_bv 8 (nth j xs 0)].
Proof.
  intros m A xs j H Hj.
  rewrite (bytes_at_read rsegs m A _ (Z.of_nat j) 1 H) by (try rewrite length_map; lia).
  rewrite Nat2Z.id. rewrite (fs1 _ _ (Z_to_bv 8 0)) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

Lemma prefix_store : forall m q pre a bs,
  bytes_at rsegs m q pre -> a = q + Z.of_nat (length pre) -> a + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa a) bs) q (pre ++ bs).
Proof.
  intros m q pre a bs H Ha Hb. pose proof (bytes_at_bound _ _ _ _ H) as Hq.
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact H | lia | lia | left; lia].
  - subst a. apply bytes_at_write_same; lia.
Qed.

Lemma nth_rng : forall (l : list Z) j, Forall (fun s => 0 <= s < 64) l -> (j < length l)%nat -> 0 <= nth j l 0 < 64.
Proof. intros l j H Hj. rewrite Forall_forall in H. apply H. apply nth_In. exact Hj. Qed.

Lemma skipn_nth : forall (l : list Z) j, (j < length l)%nat -> skipn j l = nth j l 0 :: skipn (S j) l.
Proof. induction l as [|x l IH]; intros [|j] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma firstn_plus : forall i j (l : list Z), firstn (i + j) l = firstn i l ++ firstn j (skipn i l).
Proof.
  induction i as [|i IH]; intros j l; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity | f_equal; apply IH].
Qed.

Lemma six_bytes_app : forall a b, Z.of_nat (length a) mod 4 = 0 -> six_bytes (a ++ b) = six_bytes a ++ six_bytes b.
Proof.
  intros a b. induction a as [|x|x y|x y z|x y z w l IH] using list4_ind; intros H.
  - reflexivity.
  - exfalso. cbn in H. discriminate.
  - exfalso. cbn in H. discriminate.
  - exfalso. cbn in H. discriminate.
  - cbn [app six_bytes]. rewrite IH; [reflexivity|].
    replace (length (x :: y :: z :: w :: l)) with (S (S (S (S (length l))))) in H by reflexivity. mlia2.
Qed.

Lemma grp_full : forall (l : list Z) j, (j + 4 <= length l)%nat -> Z.of_nat j mod 4 = 0 ->
  six_bytes (firstn (j + 4) l) = six_bytes (firstn j l) ++
    [nth j l 0 * 4 + nth (S j) l 0 / 16; nth (S j) l 0 mod 16 * 16 + nth (S (S j)) l 0 / 4;
     nth (S (S j)) l 0 mod 4 * 64 + nth (S (S (S j))) l 0].
Proof.
  intros l j H Hj. rewrite firstn_plus, six_bytes_app.
  - f_equal. rewrite (skipn_nth l j), (skipn_nth l (S j)), (skipn_nth l (S (S j))), (skipn_nth l (S (S (S j))))
      by lia. reflexivity.
  - rewrite firstn_length_le by lia. exact Hj.
Qed.

Lemma grp_tail2 : forall (l : list Z) j, length l = (j + 2)%nat -> Z.of_nat j mod 4 = 0 ->
  six_bytes l = six_bytes (firstn j l) ++ [nth j l 0 * 4 + nth (S j) l 0 / 16].
Proof.
  intros l j H Hj. rewrite <- (firstn_skipn j l) at 1. rewrite six_bytes_app.
  - f_equal. rewrite (skipn_nth l j), (skipn_nth l (S j)) by lia. rewrite skipn_all2 by (cbn; lia).
    reflexivity.
  - rewrite firstn_length_le by lia. exact Hj.
Qed.

Lemma grp_tail3 : forall (l : list Z) j, length l = (j + 3)%nat -> Z.of_nat j mod 4 = 0 ->
  six_bytes l = six_bytes (firstn j l) ++
    [nth j l 0 * 4 + nth (S j) l 0 / 16; nth (S j) l 0 mod 16 * 16 + nth (S (S j)) l 0 / 4].
Proof.
  intros l j H Hj. rewrite <- (firstn_skipn j l) at 1. rewrite six_bytes_app.
  - f_equal. rewrite (skipn_nth l j), (skipn_nth l (S j)), (skipn_nth l (S (S j))) by lia.
    rewrite skipn_all2 by (cbn; lia). reflexivity.
  - rewrite firstn_length_le by lia. exact Hj.
Qed.

Lemma grp_tail4 : forall (l : list Z) j, length l = (j + 4)%nat -> Z.of_nat j mod 4 = 0 ->
  six_bytes l = six_bytes (firstn j l) ++
    [nth j l 0 * 4 + nth (S j) l 0 / 16; nth (S j) l 0 mod 16 * 16 + nth (S (S j)) l 0 / 4;
     nth (S (S j)) l 0 mod 4 * 64 + nth (S (S (S j))) l 0].
Proof.
  intros l j H Hj. assert (E : firstn (j + 4) l = l) by (apply firstn_all2; lia).
  rewrite <- E at 1. apply grp_full; lia.
Qed.

Lemma last_nth : forall (l : list Z) d, l <> [] -> last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x l IH]; intros d H; [congruence|].
  destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d).
  rewrite IH by discriminate. cbn [length].
  replace (S (S (length l')) - 1)%nat with (S (length l')) by lia.
  replace (S (length l') - 1)%nat with (length l') by lia. reflexivity.
Qed.

Lemma six_tail_ok_eq : forall six k, k = Z.of_nat (length six) ->
  six_tail_ok six =
  negb (k mod 4 =? 1) && (negb (k mod 4 =? 2) || (nth (length six - 1) six 0 mod 16 =? 0)) &&
  (negb (k mod 4 =? 3) || (nth (length six - 1) six 0 mod 4 =? 0)).
Proof.
  intros six k ->. unfold six_tail_ok. destruct six as [|x l].
  - reflexivity.
  - rewrite last_nth by discriminate. reflexivity.
Qed.

Section AswBody.
  Variables (ra sp gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (t want six n : Z) (tb junkw junks : list byte) (cs : list Z)
    (m0 : word -> option byte).
  Hypothesis HCS : cs = map (fun b : byte => bv_unsigned b) tb.
  Hypothesis HN : Z.of_nat (length tb) = n.
  Hypothesis HN31 : n < 2^31.
  Hypothesis NZ : Forall (fun b : byte => bv_unsigned b <> 0) tb.
  Hypothesis TXT0 : bytes_at rsegs m0 t (tb ++ [Z_to_bv 8 0]).
  Hypothesis WNT0 : rw_cells rsegs m0 want [CB (Z.to_nat (n / 4 * 3 + 3)) junkw].
  Hypothesis SIX0 : rw_cells rsegs m0 six [CB (Z.to_nat (Z.max n 1)) junks].
  Hypothesis D_SW : six + Z.max n 1 <= want \/ want + (n / 4 * 3 + 3) <= six.
  Hypothesis D_ST : six + Z.max n 1 <= t \/ t + n + 1 <= six.
  Hypothesis D_WT : want + (n / 4 * 3 + 3) <= t \/ t + n + 1 <= want.

  Abbreviation W := [(six, six + Z.max n 1); (want, want + (n / 4 * 3 + 3))].

  Abbreviation POST := (asw_post ra sp gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 F fc t want six n tb m0).

  Abbreviation ST pc x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 mm :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 six) x11 x12 x13 x14 x15 x16 x17
       (Z_to_bv 64 want) x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
       F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Abbreviation SL pc x7 x28 x29 k pad p mm :=
    (ST pc (Z_to_bv 64 4294977024) (Z_to_bv 64 43) x7 (Z_to_bv 64 (18446744073709551615 - six))
       (Z_to_bv 64 k) (Z_to_bv 64 25) (Z_to_bv 64 61) (Z_to_bv 64 (-1)) (Z_to_bv 64 9) (Z_to_bv 64 pad)
       (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x28 x29 mm).

  Lemma bnds : 0 <= n /\ 0 <= t /\ t + n + 1 <= 2^64 /\ 0 <= six /\ six + Z.max n 1 <= 2^64 /\
    0 <= want /\ want + (n / 4 * 3 + 3) <= 2^64.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ TXT0) as A. rewrite length_app in A. cbn [length] in A.
    pose proof (rw_cells_bound _ _ _ _ SIX0) as B. pose proof (rw_cells_bound _ _ _ _ WNT0) as C.
    cbn [cells_size csize] in B, C. rewrite Nat.add_0_r in B, C.
    assert (0 <= n) by lia.
    rewrite Z2Nat.id in B by lia. rewrite Z2Nat.id in C by mlia2.
    lia.
  Qed.

  Lemma cs_len : Z.of_nat (length cs) = n.
  Proof. rewrite HCS, length_map. exact HN. Qed.

  Lemma cs_rng : Forall (fun c => 1 <= c <= 255) cs.
  Proof.
    rewrite HCS, Forall_map. eapply Forall_impl; [|exact NZ]. intros b Hb. cbv beta in *.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
  Qed.

  Lemma cs_in : forall pre c rest, cs = pre ++ c :: rest -> 1 <= c <= 255.
  Proof.
    intros pre c rest E. pose proof cs_rng as R. rewrite Forall_forall in R. apply R. rewrite E.
    apply in_or_app. right. left. reflexivity.
  Qed.

  Lemma txt0 : bytes_at rsegs m0 t (map (Z_to_bv 8) (cs ++ [0])).
  Proof.
    eapply bytes_at_ext; [exact TXT0|]. rewrite HCS, map_app, map_map, map_bv8. reflexivity.
  Qed.

  Lemma txt_at : forall m, munch W m0 m -> bytes_at rsegs m t (map (Z_to_bv 8) (cs ++ [0])).
  Proof.
    intros m MU. pose proof bnds as B. pose proof cs_len as CL.
    eapply bytes_at_transport; [exact txt0 | exact MU |].
    rewrite length_map, length_app. cbn [disjoint_from length]. lia.
  Qed.

  Lemma rd_txt : forall m pre x post, bytes_at rsegs m t (map (Z_to_bv 8) (cs ++ [0])) ->
    cs ++ [0] = pre ++ x :: post ->
    ov_read_bytes rsegs m (wa (t + Z.of_nat (length pre))) 1 = Some [Z_to_bv 8 x].
  Proof.
    intros m pre x post H E. rewrite E, map_app in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite length_map in H. cbn [map] in H.
    rewrite <- (Z.add_0_r (t + Z.of_nat (length pre))).
    rewrite (bytes_at_read rsegs m _ _ 0 1 H) by (cbn [length]; lia). reflexivity.
  Qed.

  Lemma six_store_ok : forall m j, wmono rsegs m0 m -> 0 <= j < Z.max n 1 -> store_ok rsegs m (wa (six + j)) 1 = true.
  Proof.
    intros m j WM Hj. pose proof SIX0 as [_ WR]. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
    rewrite Z2Nat.id in WR by lia.
    apply (wr_at_store_ok rsegs m six (Z.max n 1) j 1); [eapply wr_at_transport; eassumption | lia | lia].
  Qed.

  Lemma want_store_ok : forall m j, wmono rsegs m0 m -> 0 <= j < n / 4 * 3 + 3 ->
    store_ok rsegs m (wa (want + j)) 1 = true.
  Proof.
    intros m j WM Hj. pose proof bnds as B. pose proof WNT0 as [_ WR]. cbn [cells_size csize] in WR.
    rewrite Nat.add_0_r in WR. rewrite Z2Nat.id in WR by mlia2.
    apply (wr_at_store_ok rsegs m want (n / 4 * 3 + 3) j 1); [eapply wr_at_transport; eassumption | lia | lia].
  Qed.

  Definition sinv (m : word -> option byte) (sixl : list Z) : Prop :=
    munch W m0 m /\ wmono rsegs m0 m /\ bytes_at rsegs m six (map (Z_to_bv 8) sixl) /\
    Forall (fun s => 0 <= s < 64) sixl.

  Lemma sinv0 : sinv m0 [].
  Proof.
    pose proof bnds as B. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [apply bytes_at_nil; lia | constructor].
  Qed.

  Lemma evt_store_s : forall Q R pc m sixl v,
    sinv m sixl -> Z.of_nat (length sixl) < Z.max n 1 -> 0 <= v < 64 ->
    (forall m', sinv m' (sixl ++ [v]) -> evt rsegs Q (MS R F pc fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS R F pc fc None (write_to_mem m (Z_to_bv 64 (six + Z.of_nat (length sixl))) [Z_to_bv 8 v])
                   (seg_rom rsegs)).
  Proof.
    intros Q R pc m sixl v (MU & WM & SX & FR) Hl Hv K. pose proof bnds as B. apply K.
    split; [|split; [|split]].
    - apply (munch_write W m0 m (six + Z.of_nat (length sixl)) [Z_to_bv 8 v] MU); cbn [length inside]; lia.
    - apply wmono_write. exact WM.
    - rewrite map_app. apply prefix_store; [exact SX | rewrite length_map; reflexivity | cbn [length map]; lia].
    - apply Forall_app. split; [exact FR | constructor; [exact Hv | constructor]].
  Qed.

  Lemma evt_store_w : forall Q R pc m (pre : list byte) (sixf : list Z) a b,
    munch W m0 m -> wmono rsegs m0 m -> bytes_at rsegs m six (map (Z_to_bv 8) sixf) ->
    Z.of_nat (length sixf) <= n ->
    bytes_at rsegs m want pre -> a = want + Z.of_nat (length pre) -> Z.of_nat (length pre) < n / 4 * 3 + 3 ->
    0 <= b < 256 ->
    (forall m', munch W m0 m' -> wmono rsegs m0 m' -> bytes_at rsegs m' six (map (Z_to_bv 8) sixf) ->
       bytes_at rsegs m' want (pre ++ [Z_to_bv 8 b]) -> evt rsegs Q (MS R F pc fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS R F pc fc None (write_to_mem m (Z_to_bv 64 a) [Z_to_bv 8 b]) (seg_rom rsegs)).
  Proof.
    intros Q R pc m pre sixf a b MU WM SX Hk WP Ea Hl Hb K. pose proof bnds as B. apply K.
    - apply (munch_write W m0 m a [Z_to_bv 8 b] MU); cbn [length inside]; lia.
    - apply wmono_write. exact WM.
    - apply bytes_at_write_other; [exact SX | lia | cbn [length]; lia | rewrite length_map; cbn [length]; lia].
    - apply prefix_store; [exact WP | exact Ea | cbn [length]; lia].
  Qed.

  Lemma fin_now : forall m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 r,
    munch W m0 m -> wmono rsegs m0 m ->
    match b64_dec cs with
    | Some bs => r = Z_to_bv 64 (Z.of_nat (length bs)) /\ bytes_at rsegs m want (map (Z_to_bv 8) bs)
    | None => r = Z_to_bv 64 (2^64 - 1)
    end ->
    POST (ST 0x13910 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 r x28 x29 m).
  Proof.
    intros m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 r MU WM R.
    unfold asw_post.
    exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x19, x28, x29, t5, t6, r, m.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split.
    - pose proof bnds as B. eapply bytes_at_transport; [exact TXT0 | exact MU |].
      rewrite length_app. cbn [length disjoint_from]. lia.
    - rewrite <- HCS. exact R.
  Qed.

  Lemma fin : forall m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 r,
    munch W m0 m -> wmono rsegs m0 m ->
    match b64_dec cs with
    | Some bs => r = Z_to_bv 64 (Z.of_nat (length bs)) /\ bytes_at rsegs m want (map (Z_to_bv 8) bs)
    | None => r = Z_to_bv 64 (2^64 - 1)
    end ->
    evt rsegs POST (ST 0x13910 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 r x28 x29 m).
  Proof.
    intros m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 r MU WM R.
    apply evt_done. apply fin_now; assumption.
  Qed.

  Definition scan_exit (ms : machine_state) : Prop :=
    (exists (padf : Z) (sixf : list Z) (m : word -> option byte) (x7 x28 x29 : word) (p : Z),
      sinv m sixf /\ 0 <= padf <= n /\ Z.of_nat (length sixf) <= n /\
      b64_scan 0 [] cs = Some (sixf, padf) /\
      ms = SL 0x137e0 x7 x28 x29 (Z.of_nat (length sixf)) padf p m) \/ POST ms.

  Lemma scan_fail : forall m sixl x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29,
    sinv m sixl -> b64_scan 0 [] cs = None ->
    evt rsegs scan_exit (ST 0x13910 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (-1)) x28 x29 m).
  Proof.
    intros m sixl x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 (MU & WM & _ & _) E.
    apply evt_done. right. apply fin_now; [exact MU | exact WM |].
    unfold b64_dec. rewrite E. apply Z_to_bv_eqm. reflexivity.
  Qed.

  Definition kont (pre rest : list Z) : Prop :=
    forall (sixl : list Z) (pad : Z) (m : word -> option byte) (x7 x28 x29 : word) (k p : Z),
      k = Z.of_nat (length sixl) -> p + 1 = t + Z.of_nat (length pre) -> (1 <= length pre)%nat ->
      sinv m sixl -> 0 <= pad <= Z.of_nat (length pre) -> (length sixl <= length pre)%nat ->
      b64_scan 0 [] cs = b64_scan pad sixl rest ->
      evt rsegs scan_exit (SL 0x13798 x7 x28 x29 k pad p m).

  Lemma blk_x : forall pre c rest sixl pad m x7 x29 tv k p,
    cs = pre ++ c :: rest -> k = Z.of_nat (length sixl) -> p = t + Z.of_nat (length pre) ->
    sinv m sixl -> 0 <= pad <= Z.of_nat (length pre) -> (length sixl <= length pre)%nat ->
    b64_scan 0 [] cs = b64_scan pad sixl (c :: rest) -> kont (pre ++ [c]) rest ->
    1 <= c <= 255 -> b64_ws c = false -> c <> 61 -> tvrel c tv ->
    evt rsegs scan_exit (SL 0x137c0 x7 (Z_to_bv 64 tv) x29 k pad p m).
  Proof.
    intros pre c rest sixl pad m x7 x29 tv k p Ecs Ek Ep INV Hpad Hlen SC K Hc Hws H61 TV.
    unfold kont in K. pose proof cs_len as CL. pose proof bnds as B.
    assert (HL : Z.of_nat (length pre) + 1 <= n) by (rewrite <- CL, Ecs, length_app; cbn [length]; lia).
    cbn [b64_scan] in SC. rewrite Hws, (proj2 (Z.eqb_neq c 61) H61) in SC. cbv iota in SC.
    unfold tvrel in TV. destruct (b64v c) as [v|] eqn:Hv.
    - subst tv. pose proof (b64v_range c v Hv) as Rv.
      zstep. brf. zstep. if_cases BZ; zify_cond BZ.
      + eapply scan_fail; [exact INV|]. rewrite SC, (proj2 (Z.eqb_neq pad 0) BZ). reflexivity.
      + subst pad k. pose proof INV as (MU & WM & SX & FR).
        pose proof (six_store_ok m (Z.of_nat (length sixl)) WM ltac:(lia)) as HS.
        zstep. brf. zstep. zstep. zstep. fix_le1 v.
        eapply evt_store_s; [exact INV | lia | exact Rv | intros m1 INV1].
        zstep. zstep.
        eapply (K (sixl ++ [v]) 0 m1);
          [ rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
          | rewrite length_app; cbn [length]; lia | exact INV1
          | rewrite length_app; cbn [length]; lia | rewrite !length_app; cbn [length]; lia | ].
        rewrite SC. reflexivity.
    - subst tv. zstep. brt.
      eapply scan_fail; [exact INV | exact SC].
  Qed.

  Lemma blk_dc : forall pre c rest sixl pad m x29 tv k p,
    cs = pre ++ c :: rest -> k = Z.of_nat (length sixl) -> p = t + Z.of_nat (length pre) ->
    sinv m sixl -> 0 <= pad <= Z.of_nat (length pre) -> (length sixl <= length pre)%nat ->
    b64_scan 0 [] cs = b64_scan pad sixl (c :: rest) -> kont (pre ++ [c]) rest ->
    1 <= c <= 61 -> tvrel c tv ->
    evt rsegs scan_exit (SL 0x1378c (Z_to_bv 64 c) (Z_to_bv 64 tv) x29 k pad p m).
  Proof.
    intros pre c rest sixl pad m x29 tv k p Ecs Ek Ep INV Hpad Hlen SC K Hc TV.
    pose proof K as K'. unfold kont in K'. pose proof cs_len as CL. pose proof bnds as B.
    assert (HL : Z.of_nat (length pre) + 1 <= n) by (rewrite <- CL, Ecs, length_app; cbn [length]; lia).
    destruct (b64_ws c) eqn:Hws.
    - zstep. zstep. rewrite (ws_bit1 c) by (lia || exact Hws).
      zstep. brf.
      cbn [b64_scan] in SC. rewrite Hws in SC. cbv iota in SC.
      eapply (K' sixl pad m); [exact Ek | rewrite Ep, length_app; cbn [length]; lia
        | rewrite length_app; cbn [length]; lia | exact INV
        | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact SC].
    - zstep. zstep. rewrite (ws_bit0 c) by (lia || exact Hws).
      zstep. brt. zstep. if_cases BE; zify_cond BE.
      + eapply (blk_x pre c rest sixl pad m); try eassumption; lia.
      + zstep. rewrite (swrap_small (pad + 1)) by lia.
        zstep. brfs. zstep. zstep.
        cbn [b64_scan] in SC. rewrite Hws, (proj2 (Z.eqb_eq c 61) BE) in SC. cbv iota in SC.
        eapply (K' sixl (pad + 1) m); [exact Ek | rewrite Ep, length_app; cbn [length]; lia
          | rewrite length_app; cbn [length]; lia | exact INV
          | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact SC].
  Qed.

  Lemma char_step : forall pre c rest sixl pad m x28 x29 k p,
    cs = pre ++ c :: rest -> k = Z.of_nat (length sixl) -> p = t + Z.of_nat (length pre) ->
    sinv m sixl -> 0 <= pad <= Z.of_nat (length pre) -> (length sixl <= length pre)%nat ->
    b64_scan 0 [] cs = b64_scan pad sixl (c :: rest) -> kont (pre ++ [c]) rest ->
    evt rsegs scan_exit (SL 0x13728 (Z_to_bv 64 c) x28 x29 k pad p m).
  Proof.
    intros pre c rest sixl pad m x28 x29 k p Ecs Ek Ep INV Hpad Hlen SC K.
    pose proof (cs_in pre c rest Ecs) as Hc.
    zstep. zstep. rewrite (land255 c) by lia.
    zstep. if_cases BU; zify_cond BU.
    - zstep. zstep. if_cases BL; zify_cond BL.
      + zstep. zstep. if_cases BD; zify_cond BD.
        * zstep. if_cases BP; zify_cond BP.
          -- zstep. zstep. zstep. zstep. rewrite (t1_val c Hc).
             zstep. if_cases BG; zify_cond BG.
             ++ assert (C1 : ~ (65 <= c <= 90)) by mlia2. assert (C2 : ~ (97 <= c <= 122)) by mlia2.
                assert (C3 : 61 < c) by mlia2. clear BU BL BD BG.
                eapply (blk_x pre c rest sixl pad m); try eassumption.
                ** apply b64_ws_false; lia.
                ** lia.
                ** unfold tvrel. rewrite (proj2 (Z.eqb_neq c 47)) by lia. rewrite b64v_none by lia. reflexivity.
             ++ assert (C3 : ~ (48 <= c <= 57)) by mlia2. assert (C4 : c <= 61) by mlia2. clear BU BL BD BG.
                eapply (blk_dc pre c rest sixl pad m); try eassumption; [lia|].
                unfold tvrel. destruct (Z.eqb_spec c 47) as [E|E].
                ** rewrite E. vm_compute. reflexivity.
                ** rewrite b64v_none by lia. reflexivity.
          -- zstep. zstep. brt.
             eapply (blk_dc pre c rest sixl pad m); try eassumption; [lia|].
             unfold tvrel. rewrite BP. vm_compute. reflexivity.
        * assert (C : 48 <= c <= 57) by mlia2. clear BU BL BD.
          zstep. zstep. brt.
          eapply (blk_dc pre c rest sixl pad m); try eassumption; [lia|].
          unfold tvrel, b64v. dec. reflexivity.
      + assert (C : 97 <= c <= 122) by mlia2. clear BU BL.
        zstep. zstep. brf. zstep.
        eapply (blk_x pre c rest sixl pad m); try eassumption.
        * apply b64_ws_false; lia.
        * lia.
        * unfold tvrel, b64v. dec. lia.
    - assert (C : 65 <= c <= 90) by mlia2. clear BU.
      zstep. zstep. brf. zstep.
      eapply (blk_x pre c rest sixl pad m); try eassumption.
      + apply b64_ws_false; lia.
      + lia.
      + unfold tvrel, b64v. dec. lia.
  Qed.

  Lemma next_char : forall pre rest sixl pad m x7 x28 x29 k p,
    cs = pre ++ rest -> k = Z.of_nat (length sixl) -> p + 1 = t + Z.of_nat (length pre) -> (1 <= length pre)%nat ->
    sinv m sixl -> 0 <= pad <= Z.of_nat (length pre) -> (length sixl <= length pre)%nat ->
    b64_scan 0 [] cs = b64_scan pad sixl rest ->
    (forall c rest' x28' x29', rest = c :: rest' ->
       evt rsegs scan_exit (SL 0x13728 (Z_to_bv 64 c) x28' x29' k pad (p + 1) m)) ->
    evt rsegs scan_exit (SL 0x13798 x7 x28 x29 k pad p m).
  Proof.
    intros pre rest sixl pad m x7 x28 x29 k p Ecs Ek Ep H1 INV Hpad Hlen SC K.
    pose proof INV as (MU & WM & SX & FR).
    pose proof (txt_at m MU) as TX. pose proof bnds as B. pose proof cs_len as CL.
    assert (HL : (length pre <= length cs)%nat) by (rewrite Ecs, length_app; lia).
    zstep. brf.
    destruct rest as [|c rest'].
    - assert (RD : ov_read_bytes rsegs m (wa (t + Z.of_nat (length pre))) 1 = Some [Z_to_bv 8 0]).
      { apply (rd_txt m pre 0 [] TX). rewrite Ecs, app_nil_r. reflexivity. }
      zstep. zstep. zstep. brt.
      apply evt_done. left. exists pad, sixl, m. do 4 eexists.
      split; [exact INV|]. split; [lia|]. split; [lia|].
      split; [rewrite SC; reflexivity|]. subst k. reflexivity.
    - pose proof (cs_in pre c rest' Ecs) as Hc.
      assert (RD : ov_read_bytes rsegs m (wa (t + Z.of_nat (length pre))) 1 = Some [Z_to_bv 8 c]).
      { apply (rd_txt m pre c (rest' ++ [0]) TX). rewrite Ecs, <- app_assoc. reflexivity. }
      zstep. fix_u8. zstep. zstep. brf. zstep.
      eapply K. reflexivity.
  Qed.

  Lemma scan_loop : forall rest pre c sixl pad m x28 x29 k p,
    cs = pre ++ c :: rest -> k = Z.of_nat (length sixl) -> p = t + Z.of_nat (length pre) ->
    sinv m sixl -> 0 <= pad <= Z.of_nat (length pre) -> (length sixl <= length pre)%nat ->
    b64_scan 0 [] cs = b64_scan pad sixl (c :: rest) ->
    evt rsegs scan_exit (SL 0x13728 (Z_to_bv 64 c) x28 x29 k pad p m).
  Proof.
    induction rest as [|c' rest IH]; intros pre c sixl pad m x28 x29 k p Ecs Ek Ep INV Hpad Hlen SC;
      (eapply char_step; [exact Ecs | exact Ek | exact Ep | exact INV | exact Hpad | exact Hlen | exact SC | ]);
      unfold kont; intros sixl' pad' m' x7' x28' x29' k' p' Ek' Ep' H1' INV' Hpad' Hlen' SC';
      (eapply next_char; [ | exact Ek' | exact Ep' | exact H1' | exact INV' | exact Hpad' | exact Hlen' | exact SC' | ]).
    - rewrite Ecs, <- app_assoc. reflexivity.
    - intros c'' rest' x28'' x29'' E. discriminate.
    - rewrite Ecs, <- app_assoc. reflexivity.
    - intros c'' rest' x28'' x29'' E. injection E as <- <-.
      eapply (IH (pre ++ [c])); [ | exact Ek' | | exact INV' | exact Hpad' | exact Hlen' | exact SC' ].
      + rewrite Ecs, <- app_assoc. reflexivity.
      + lia.
  Qed.

  Definition ginv (sixf : list Z) (m : word -> option byte) (i : Z) : Prop :=
    munch W m0 m /\ wmono rsegs m0 m /\ bytes_at rsegs m six (map (Z_to_bv 8) sixf) /\
    bytes_at rsegs m want (map (Z_to_bv 8) (six_bytes (firstn (Z.to_nat i) sixf))).

  Lemma grp_loop : forall sixf k, k = Z.of_nat (length sixf) -> k <= n -> k mod 4 <> 1 ->
    Forall (fun s => 0 <= s < 64) sixf -> b64_dec cs = Some (six_bytes sixf) ->
    forall (N : nat) i m x5 x6 x7 x17 x19 x28 x29 nout,
      N = Z.to_nat (k - i) -> 0 <= i < k -> i mod 4 = 0 -> nout = 3 * (i / 4) -> ginv sixf m i ->
      evt rsegs POST (ST 0x13864 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - six)) (Z_to_bv 64 k) (Z_to_bv 64 i)
                        (Z_to_bv 64 (18446744073709551615 - want)) (Z_to_bv 64 (six + 1)) (Z_to_bv 64 (-1))
                        x17 x19 (Z_to_bv 64 nout) x28 x29 m).
  Proof.
    intros sixf k Ek Hk H1 FR DEC N. induction N as [N IH] using lt_wf_ind.
    intros i m x5 x6 x7 x17 x19 x28 x29 nout EN Hi Hi4 En (MU & WM & SX & WP).
    pose proof bnds as B.
    assert (Hk2 : i + 2 <= k) by mlia2.
    remember (Z.to_nat i) as j eqn:Ej.
    assert (Ij : Z.of_nat j = i) by lia.
    assert (LP : Z.of_nat (length (map (Z_to_bv 8) (six_bytes (firstn j sixf)))) = nout).
    { rewrite length_map, six_bytes_length, firstn_length_le by lia. rewrite Ij, En. mlia2. }
    rewrite length_map in LP.
    pose proof (nth_rng sixf j FR ltac:(lia)) as R0.
    pose proof (nth_rng sixf (S j) FR ltac:(lia)) as R1.
    pose proof (rd_at m six sixf j SX ltac:(lia)) as RD0.
    pose proof (rd_at m six sixf (S j) SX ltac:(lia)) as RD1.
    pose proof (want_store_ok m nout WM ltac:(mlia2)) as HS.
    zstep. brf. zstep. zstep. brf. zstep. brf.
    zstep. fix_u8. zstep. fix_u8. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    fix_le1 (nth j sixf 0 * 4 + nth (S j) sixf 0 / 16).
    eapply (evt_store_w _ _ _ m _ sixf);
      [exact MU | exact WM | exact SX | lia | exact WP | rewrite length_map; lia | rewrite length_map; mlia2 | mlia2
      | intros m1 MU1 WM1 SX1 WP1].
    clear RD0 RD1 HS MU WM SX WP.
    zstep. if_cases B2; zify_cond B2.
    - assert (Ek2 : k = i + 2) by lia.
      zstep. zstep. brt. zstep. zstep. brf. zstep. zstep. brf.
      apply fin; [exact MU1 | exact WM1 |]. rewrite DEC.
      rewrite (grp_tail2 sixf j) by lia. split.
      + f_equal. rewrite length_app. cbn [length]. lia.
      + rewrite map_app. exact WP1.
    - pose proof (nth_rng sixf (S (S j)) FR ltac:(lia)) as R2.
      pose proof (rd_at m1 six sixf (S j) SX1 ltac:(lia)) as RD1.
      pose proof (rd_at m1 six sixf (S (S j)) SX1 ltac:(lia)) as RD2.
      pose proof (want_store_ok m1 (nout + 1) WM1 ltac:(mlia2)) as HS.
      zstep. brf. zstep. brf. zstep. brf.
      zstep. fix_u8. zstep. fix_u8. zstep. zstep. zstep. zstep. zstep. zstep.
      fix_le1 (nth (S j) sixf 0 mod 16 * 16 + nth (S (S j)) sixf 0 / 4).
      eapply (evt_store_w _ _ _ m1 _ sixf);
        [exact MU1 | exact WM1 | exact SX1 | lia | exact WP1 | rewrite length_app, length_map; cbn [length]; lia
        | rewrite length_app, length_map; cbn [length]; mlia2 | mlia2 | intros m2 MU2 WM2 SX2 WP2].
      clear RD1 RD2 HS MU1 WM1 SX1 WP1.
      zstep. zstep. if_cases B3; zify_cond B3.
      + assert (Ek3 : k = i + 3) by lia.
        zstep. zstep. brf. zstep. zstep. brf.
        apply fin; [exact MU2 | exact WM2 |]. rewrite DEC.
        rewrite (grp_tail3 sixf j) by lia. split.
        * f_equal. rewrite length_app. cbn [length]. lia.
        * rewrite map_app. rewrite <- app_assoc in WP2. exact WP2.
      + pose proof (nth_rng sixf (S (S (S j))) FR ltac:(lia)) as R3.
        pose proof (rd_at m2 six sixf (S (S j)) SX2 ltac:(lia)) as RD2.
        pose proof (rd_at m2 six sixf (S (S (S j))) SX2 ltac:(lia)) as RD3.
        pose proof (want_store_ok m2 (nout + 2) WM2 ltac:(mlia2)) as HS.
        zstep. brf. zstep. brf. zstep. brf.
        zstep. fix_u8. zstep. fix_u8. zstep. zstep. zstep. zstep. zstep.
        fix_le1 (nth (S (S j)) sixf 0 mod 4 * 64 + nth (S (S (S j))) sixf 0).
        eapply (evt_store_w _ _ _ m2 _ sixf);
          [exact MU2 | exact WM2 | exact SX2 | lia | exact WP2
          | rewrite !length_app, length_map; cbn [length]; lia
          | rewrite !length_app, length_map; cbn [length]; mlia2 | mlia2 | intros m3 MU3 WM3 SX3 WP3].
        clear RD2 RD3 HS MU2 WM2 SX2 WP2.
        zstep. brf. zstep. zstep. zstep. if_cases B4; zify_cond B4.
        * eapply (IH (Z.to_nat (k - (i + 4)))); [lia | reflexivity | lia | mlia2 | mlia2 | ].
          split; [exact MU3|]. split; [exact WM3|]. split; [exact SX3|].
          replace (Z.to_nat (i + 4)) with (j + 4)%nat by lia.
          rewrite grp_full by (try rewrite Ij; lia).
          rewrite map_app. rewrite <- !app_assoc in WP3. exact WP3.
        * assert (Ek4 : k = i + 4) by lia.
          apply fin; [exact MU3 | exact WM3 |]. rewrite DEC.
          rewrite (grp_tail4 sixf j) by lia. split.
          -- f_equal. rewrite length_app. cbn [length]. lia.
          -- rewrite map_app. rewrite <- !app_assoc in WP3. exact WP3.
  Qed.

  Lemma at1384c : forall sixf m x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x28 x29 k,
    k = Z.of_nat (length sixf) -> sinv m sixf -> k <= n -> k mod 4 <> 1 ->
    b64_dec cs = Some (six_bytes sixf) ->
    evt rsegs POST (ST 0x1384c x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - six)) (Z_to_bv 64 k)
                      x13 x14 x15 x16 x17 x19 x20 x28 x29 m).
  Proof.
    intros sixf m x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x28 x29 k Ek INV Hk H1 DEC.
    pose proof INV as (MU & WM & SX & FR). pose proof bnds as B.
    zstep. zstep. if_cases BZ; zify_cond BZ.
    - destruct sixf as [|x l]; [|cbn [length] in Ek; lia].
      apply fin; [exact MU | exact WM |]. rewrite DEC. split; [reflexivity | apply bytes_at_nil; lia].
    - zstep. zstep. rewrite (zb_lxor_ones want) by lia. zstep. zstep.
      eapply (grp_loop sixf k Ek Hk H1 FR DEC (Z.to_nat (k - 0)) 0); [reflexivity | lia | reflexivity | reflexivity | ].
      split; [exact MU|]. split; [exact WM|]. split; [exact SX|].
      change (map (Z_to_bv 8) (six_bytes (firstn (Z.to_nat 0) sixf))) with (@nil byte).
      apply bytes_at_nil. lia.
  Qed.

  Lemma tail137f4 : forall sixf flag m x5 x6 x7 x14 x15 x16 x17 x19 x20 x28 x29 k,
    k = Z.of_nat (length sixf) -> sinv m sixf -> k <= n -> flag = 0 \/ flag = 1 ->
    (if flag =? 0 then b64_dec cs = (if six_tail_ok sixf then Some (six_bytes sixf) else None)
     else b64_dec cs = None) ->
    evt rsegs POST (ST 0x137f4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - six)) (Z_to_bv 64 k) (Z_to_bv 64 flag)
                      x14 x15 x16 x17 x19 x20 x28 x29 m).
  Proof.
    intros sixf flag m x5 x6 x7 x14 x15 x16 x17 x19 x20 x28 x29 k Ek INV Hk Hf TL.
    pose proof INV as (MU & WM & SX & FR). pose proof bnds as B.
    destruct Hf as [-> | ->]; cbn [Z.eqb] in TL.
    - rewrite (six_tail_ok_eq sixf k Ek) in TL.
      zstep. zstep. brf. zstep. rewrite (land3 k).
      assert (Hr : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by mlia2.
      destruct Hr as [Hr|[Hr|[Hr|Hr]]]; rewrite Hr in TL; cbn [Z.eqb negb andb orb] in TL.
      + zstep. zstep. brf. zstep. zstep. brf. zstep. zstep. brt.
        eapply at1384c; [exact Ek | exact INV | exact Hk | lia | exact TL].
      + zstep. zstep. brt.
        apply fin; [exact MU | exact WM |]. rewrite TL. apply Z_to_bv_eqm. reflexivity.
      + assert (Hk1 : (1 <= length sixf)%nat) by mlia2.
        pose proof (nth_rng sixf (length sixf - 1) FR ltac:(lia)) as Rl.
        pose proof (rd_at m six sixf (length sixf - 1) SX ltac:(lia)) as RD.
        zstep. zstep. brf. zstep. zstep. brf. zstep. zstep. brf.
        zstep. zstep. brf.
        zstep. zstep. fix_u8. zstep. rewrite land15. zstep. if_cases BL; zify_cond BL.
        * rewrite (proj2 (Z.eqb_eq _ 0) BL) in TL.
          eapply at1384c; [exact Ek | exact INV | exact Hk | lia | exact TL].
        * zstep. rewrite (proj2 (Z.eqb_neq _ 0) BL) in TL.
          apply fin; [exact MU | exact WM |]. rewrite TL. apply Z_to_bv_eqm. reflexivity.
      + assert (Hk1 : (1 <= length sixf)%nat) by mlia2.
        pose proof (nth_rng sixf (length sixf - 1) FR ltac:(lia)) as Rl.
        pose proof (rd_at m six sixf (length sixf - 1) SX ltac:(lia)) as RD.
        zstep. zstep. brf. zstep. zstep. brt.
        zstep. zstep. brf.
        zstep. zstep. fix_u8. zstep. rewrite land3. zstep. if_cases BL; zify_cond BL.
        * rewrite (proj2 (Z.eqb_neq _ 0) BL) in TL.
          apply fin; [exact MU | exact WM |]. rewrite TL. apply Z_to_bv_eqm. reflexivity.
        * rewrite (proj2 (Z.eqb_eq _ 0) BL) in TL.
          eapply at1384c; [exact Ek | exact INV | exact Hk | lia | exact TL].
    - zstep. zstep. brt.
      apply fin; [exact MU | exact WM |]. rewrite TL. apply Z_to_bv_eqm. reflexivity.
  Qed.

  Lemma at137e0 : forall ms, scan_exit ms -> evt rsegs POST ms.
  Proof.
    intros ms [(padf & sixf & m & x7 & x28 & x29 & p & INV & Hp & Hl & E & ->) | HP];
      [| apply evt_done; exact HP].
    zstep. zstep. rewrite (flag_val padf) by lia. zstep.
    eapply (tail137f4 sixf); [reflexivity | exact INV | exact Hl | destruct (padf <=? 2); auto | ].
    unfold b64_dec. rewrite E. destruct (padf <=? 2); reflexivity.
  Qed.

  Lemma asw_main : forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29,
    evt rsegs POST (ST 0x136f0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 t) x20 x28 x29 m0).
  Proof.
    intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29.
    pose proof bnds as B. pose proof cs_len as CL.
    pose proof (txt_at m0 (munch_refl _ _)) as TX.
    assert (Hcs : cs = [] \/ exists c rest, cs = c :: rest)
      by (destruct cs as [|c rest]; [left; reflexivity | right; eauto]).
    destruct Hcs as [Hcs | (c & rest & Hcs)].
    - assert (RD : ov_read_bytes rsegs m0 (wa (t + Z.of_nat (length (@nil Z)))) 1 = Some [Z_to_bv 8 0])
        by (apply (rd_txt m0 [] 0 [] TX); rewrite Hcs; reflexivity).
      cbn [length Z.of_nat] in RD.
      zstep. zstep. rewrite (zb_lxor_ones six) by lia. zstep. brt. zstep. zstep.
      eapply (tail137f4 [] 0 m0); [reflexivity | exact sinv0 | lia | left; reflexivity | ].
      cbn [Z.eqb]. rewrite Hcs. reflexivity.
    - pose proof (cs_in [] c rest Hcs) as Hc.
      assert (RD : ov_read_bytes rsegs m0 (wa (t + Z.of_nat (length (@nil Z)))) 1 = Some [Z_to_bv 8 c])
        by (apply (rd_txt m0 [] c (rest ++ [0]) TX); rewrite Hcs; reflexivity).
      cbn [length Z.of_nat] in RD.
      zstep. fix_u8. zstep. rewrite (zb_lxor_ones six) by lia. zstep. brf. do 11 zstep.
      eapply evt_cut; [ | exact at137e0 ].
      eapply (scan_loop rest [] c [] 0 m0);
        [rewrite Hcs; reflexivity | reflexivity | cbn [length Z.of_nat]; lia | exact sinv0 | cbn; lia | cbn; lia
        | rewrite Hcs; reflexivity].
  Qed.
End AswBody.

Theorem asw_body : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (t want six n : Z) (tb junkw junks : list byte) (m : word -> option byte),
  Z.of_nat (length tb) = n -> n < 2^31 ->
  Forall (fun b : byte => bv_unsigned b <> 0) tb ->
  bytes_at rsegs m t (tb ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m want [CB (Z.to_nat (n / 4 * 3 + 3)) junkw] ->
  rw_cells rsegs m six [CB (Z.to_nat (Z.max n 1)) junks] ->
  (six + Z.max n 1 <= want \/ want + (n / 4 * 3 + 3) <= six) ->
  (six + Z.max n 1 <= t \/ t + n + 1 <= six) ->
  (want + (n / 4 * 3 + 3) <= t \/ t + n + 1 <= want) ->
  evt rsegs (asw_post ra sp gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 F fc t want six n tb m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 six) a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 want) (Z_to_bv 64 t) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x136f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc t want six n
    tb junkw junks m HN HN31 NZ TXT WNT SIX DSW DST DWT.
  eapply asw_main; try reflexivity; eassumption.
Qed.
