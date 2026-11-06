From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrStr StrBytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import fourbyte_strstr_c.
Import ListNotations.
Open Scope Z_scope.

Definition S32 (x : Z) : word := Z_to_bv 64 (bv_swrap 32 x).
Definition wd4 (a b c d : Z) : Z := a * 16777216 + b * 65536 + c * 256 + d.

Lemma swrap32_eq : forall z, bv_swrap 32 z = z mod 2^32 - (if z mod 2^32 <? 2^31 then 0 else 2^32).
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  change (2 ^ Z.of_N 32 `div` 2) with (2^31). change (2 ^ 32 `div` 2) with (2^31).
  rewrite Zplus_mod. destruct (z mod 2^32 <? 2^31) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E];
    pose proof (Z.mod_pos_bound z (2^32) ltac:(lia)); change (2^31 mod 2^32) with (2^31).
  - rewrite Z.mod_small by lia. lia.
  - replace (z mod 2^32 + 2^31) with ((z mod 2^32 - 2^31) + 1 * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lor_disj : forall x y k, 0 <= k -> 0 <= x -> x mod 2^k = 0 -> 0 <= y < 2^k -> Z.lor x y = x + y.
Proof.
  intros x y k Hk Hx Hm Hy. rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor; [reflexivity| |];
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
  (destruct (Z.lt_ge_cases i k) as [Lt|Ge];
   [ rewrite <- (Z.mod_pow2_bits_low x k i) by lia; rewrite Hm, Z.bits_0; reflexivity
   | rewrite <- (Z.mod_small y (2^k)) by lia; rewrite Z.mod_pow2_bits_high by lia; apply andb_false_r ]).
Qed.

Lemma w4_eq : forall a b c d : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 16)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (zxb a)) 24)))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c)) 8)))
                                                    (bv_unsigned (zxb d))))))
  = S32 (wd4 (bv_unsigned a) (bv_unsigned b) (bv_unsigned c) (bv_unsigned d)).
Proof.
  intros a b c d. pose proof (sb_byte_range a) as Ra. pose proof (sb_byte_range b) as Rb.
  pose proof (sb_byte_range c) as Rc. pose proof (sb_byte_range d) as Rd.
  rewrite !sb_u_zxb. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned b * 2^16)) by lia.
  rewrite (unsigned_lit (bv_unsigned c * 2^8)) by lia.
  rewrite (lor_disj (bv_unsigned c * 2^8) (bv_unsigned d) 8) by (try lia; apply Z.mod_mul; lia).
  rewrite (unsigned_lit (bv_unsigned c * 2^8 + bv_unsigned d)) by lia.
  remember (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned a * 2^24)))) as X eqn:EX.
  assert (HX : (bv_unsigned a < 128 /\ X = bv_unsigned a * 2^24) \/
               (128 <= bv_unsigned a /\ X = bv_unsigned a * 2^24 - 2^32 + 2^64)).
  { subst X. rewrite unsigned_lit_wrap, swrap32_eq. rewrite (Z.mod_small (bv_unsigned a * 2^24) (2^32)) by lia.
    destruct (Z.ltb_spec (bv_unsigned a * 2^24) (2^31)) as [L|L].
    - left. split; [lia|]. rewrite Z.sub_0_r. apply Z.mod_small. lia.
    - right. split; [lia|]. rewrite <- (Z.mod_add _ 1 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (HXm : X mod 2^24 = 0).
  { destruct HX as [[_ ->]|[_ ->]]; [apply Z.mod_mul; lia|].
    replace (bv_unsigned a * 2^24 - 2^32 + 2^64) with ((bv_unsigned a - 256 + 2^40) * 2^24) by lia.
    apply Z.mod_mul; lia. }
  assert (HXr : 0 <= X <= 2^64 - 2^24) by (destruct HX as [[? ->]|[? ->]]; lia).
  rewrite (Z.lor_comm (bv_unsigned b * 2^16) X), (lor_disj X (bv_unsigned b * 2^16) 24) by lia.
  rewrite (unsigned_lit (X + bv_unsigned b * 2^16)) by lia.
  assert (HXm2 : (X + bv_unsigned b * 2^16) mod 2^16 = 0).
  { rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia.
    replace (X mod 2^16) with 0; [reflexivity|].
    symmetry. apply (Zmod_divides X (2^16) ltac:(lia)). apply Zmod_divides in HXm; [|lia].
    destruct HXm as [q Hq]. exists (q * 2^8). rewrite Hq. ring. }
  rewrite (lor_disj (X + bv_unsigned b * 2^16) (bv_unsigned c * 2^8 + bv_unsigned d) 16) by lia.
  unfold S32, wd4. apply bv_eq. rewrite !unsigned_lit_wrap, swrap32_eq.
  rewrite (Z.mod_small (bv_unsigned a * 16777216 + bv_unsigned b * 65536 + bv_unsigned c * 256 + bv_unsigned d) (2^32))
    by lia.
  destruct HX as [[H1 ->]|[H1 ->]];
    destruct (Z.ltb_spec (bv_unsigned a * 16777216 + bv_unsigned b * 65536 + bv_unsigned c * 256 + bv_unsigned d) (2^31))
      as [L|L]; lia.
Qed.

Lemma w_step : forall x (e : byte), 0 <= x < 2^32 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (S32 x)) 8)))) (bv_unsigned (zxb e)))
  = S32 ((x * 256 + bv_unsigned e) mod 2^32).
Proof.
  intros x e Hx. pose proof (sb_byte_range e) as Re. rewrite sb_u_zxb. unfold S32.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap, !swrap32_eq.
  rewrite (Z.mod_small x (2^32)) by lia.
  assert (HV : ((x - (if x <? 2^31 then 0 else 2^32)) mod 2^64 * 2^8) mod 2^32 = (x * 256) mod 2^32).
  { destruct (Z.ltb_spec x (2^31)); [rewrite Z.sub_0_r, (Z.mod_small x (2^64)) by lia; reflexivity|].
    rewrite <- (Z.mod_add (x - 2^32) 1 (2^64)) by lia. rewrite (Z.mod_small (x - 2^32 + 1 * 2^64) (2^64)) by lia.
    replace ((x - 2^32 + 1 * 2^64) * 2^8) with (x * 256 + (2^40 - 2^8) * 2^32) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  rewrite !unsigned_lit_wrap, Z.mod_mod by lia.
  rewrite HV.
  set (V := (x * 256) mod 2^32).
  assert (HVr : 0 <= V < 2^32) by (apply Z.mod_pos_bound; lia).
  assert (HVm : V mod 256 = 0).
  { unfold V. Z.div_mod_to_equations. lia. }
  replace ((x * 256 + bv_unsigned e) mod 2^32) with (V + bv_unsigned e).
  2:{ unfold V. rewrite Z.add_mod, (Z.mod_small (bv_unsigned e)) by lia.
      rewrite (Z.mod_small (_ + bv_unsigned e)) by (pose proof (Z.mod_pos_bound (x * 256) (2^32)); lia). reflexivity. }
  destruct (Z.ltb_spec V (2^31)) as [L|L]; destruct (Z.ltb_spec (V + bv_unsigned e) (2^31)) as [L'|L'];
    try (exfalso; lia).
  - rewrite Z.sub_0_r, Z.sub_0_r, (Z.mod_small V (2^64)) by lia.
    rewrite (lor_disj V (bv_unsigned e) 8) by lia. reflexivity.
  - replace ((V - 2^32) mod 2^64) with (V - 2^32 + 2^64)
      by (rewrite <- (Z.mod_add (V - 2^32) 1 (2^64)) by lia; symmetry; apply Z.mod_small; lia).
    rewrite (lor_disj (V - 2^32 + 2^64) (bv_unsigned e) 8) by
      (try lia; replace (V - 2^32 + 2^64) with (V + (2^64 - 2^32) / 256 * 256) by lia;
       rewrite Z.mod_add by lia; exact HVm).
    apply bv_eq. rewrite !unsigned_lit_wrap.
    replace (V - 2^32 + 2^64 + bv_unsigned e) with (V + bv_unsigned e - 2^32 + 1 * 2^64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma S32_eqb : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> bv_eqb (S32 x) (S32 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb, S32. rewrite !unsigned_lit_wrap, !swrap32_eq.
  rewrite (Z.mod_small x), (Z.mod_small y) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec y (2^31));
    destruct (Z.eqb_spec x y); subst;
    first [ exfalso; lia | apply Z.eqb_refl | apply Z.eqb_neq; rewrite ?Z.sub_0_r; Z.div_mod_to_equations; lia ].
Qed.

Lemma wd4_range : forall a b c d : byte,
  0 <= wd4 (bv_unsigned a) (bv_unsigned b) (bv_unsigned c) (bv_unsigned d) < 2^32.
Proof.
  intros a b c d. pose proof (sb_byte_range a). pose proof (sb_byte_range b).
  pose proof (sb_byte_range c). pose proof (sb_byte_range d). unfold wd4. lia.
Qed.

Lemma wd4_shift : forall a b c d e : byte,
  (wd4 (bv_unsigned a) (bv_unsigned b) (bv_unsigned c) (bv_unsigned d) * 256 + bv_unsigned e) mod 2^32
  = wd4 (bv_unsigned b) (bv_unsigned c) (bv_unsigned d) (bv_unsigned e).
Proof.
  intros a b c d e. pose proof (sb_byte_range a). pose proof (sb_byte_range b).
  pose proof (sb_byte_range c). pose proof (sb_byte_range d). pose proof (sb_byte_range e). unfold wd4.
  replace ((bv_unsigned a * 16777216 + bv_unsigned b * 65536 + bv_unsigned c * 256 + bv_unsigned d) * 256 + bv_unsigned e)
    with ((bv_unsigned b * 16777216 + bv_unsigned c * 65536 + bv_unsigned d * 256 + bv_unsigned e) + bv_unsigned a * 2^32)
    by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma wd4_eqb : forall a b c d a' b' c' d' : byte,
  (wd4 (bv_unsigned a) (bv_unsigned b) (bv_unsigned c) (bv_unsigned d) =?
   wd4 (bv_unsigned a') (bv_unsigned b') (bv_unsigned c') (bv_unsigned d'))
  = ((bv_unsigned a =? bv_unsigned a') && (bv_unsigned b =? bv_unsigned b') &&
     (bv_unsigned c =? bv_unsigned c') && (bv_unsigned d =? bv_unsigned d'))%bool.
Proof.
  intros. pose proof (sb_byte_range a). pose proof (sb_byte_range b). pose proof (sb_byte_range c).
  pose proof (sb_byte_range d). pose proof (sb_byte_range a'). pose proof (sb_byte_range b').
  pose proof (sb_byte_range c'). pose proof (sb_byte_range d'). unfold wd4.
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned a')); destruct (Z.eqb_spec (bv_unsigned b) (bv_unsigned b'));
  destruct (Z.eqb_spec (bv_unsigned c) (bv_unsigned c')); destruct (Z.eqb_spec (bv_unsigned d) (bv_unsigned d'));
  cbn; first [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Lemma exit_val : forall (b : byte) (x : word),
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltu (Z_to_bv 64 0) (zxb b))))) (bv_unsigned x))
  = if bv_unsigned b =? 0 then Z_to_bv 64 0 else x.
Proof.
  intros b x. pose proof (sb_byte_range b). unfold v_sltu, c_ltu, bv_ltu. rewrite sb_u_zxb.
  rewrite (unsigned_lit 0) by lia.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [Hb|Hb].
  - rewrite Hb. cbn -[Z_to_bv]. rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l. reflexivity.
  - replace (0 <? bv_unsigned b) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit_wrap.
    change ((0 - 1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by (apply bv_unsigned_in_range). apply Z_to_bv_lit_self.
Qed.

Lemma pe_cons : forall a nd b h, prefix_eqb (a :: nd) (b :: h) = ((a =? b) && prefix_eqb nd h)%bool.
Proof. reflexivity. Qed.

Lemma pe_short : forall nd h, (length h < length nd)%nat -> prefix_eqb nd h = false.
Proof.
  induction nd as [|a nd IH]; intros [|b h] H; cbn in *; try lia; try reflexivity.
  rewrite IH by lia. apply andb_false_r.
Qed.

Lemma ff_none : forall nd h, (forall i, (i <= length h)%nat -> prefix_eqb nd (skipn i h) = false) ->
  find_first h nd = None.
Proof.
  intros nd h. induction h as [|b h IH]; intros H.
  - pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. cbn. rewrite H0. reflexivity.
  - pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [skipn] in H0.
    cbn [find_first]. rewrite H0. rewrite IH; [reflexivity|].
    intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma ff_some : forall nd h i, (forall i', (i' < i)%nat -> prefix_eqb nd (skipn i' h) = false) ->
  prefix_eqb nd (skipn i h) = true -> find_first h nd = Some i.
Proof.
  intros nd h. induction h as [|b h IH]; intros [|i] H Hi.
  - cbn in *. rewrite Hi. reflexivity.
  - cbn in Hi. destruct nd; cbn in Hi; [|discriminate].
    specialize (H 0%nat ltac:(lia)). cbn in H. discriminate.
  - cbn [find_first]. cbn [skipn] in Hi. rewrite Hi. reflexivity.
  - pose proof (H 0%nat ltac:(lia)) as H0. cbn [skipn] in H0. cbn [find_first]. rewrite H0.
    cbn [skipn] in Hi. rewrite (IH i); [reflexivity| |exact Hi].
    intros i' Hi'. exact (H (S i') ltac:(lia)).
Qed.

Lemma pe4 : forall (h : list Z) i y0 y1 y2 y3,
  (i + 4 <= length h)%nat ->
  prefix_eqb [y0; y1; y2; y3] (skipn i h) =
  ((nth i h 0 =? y0) && (nth (i + 1) h 0 =? y1) && (nth (i + 2) h 0 =? y2) && (nth (i + 3) h 0 =? y3))%bool.
Proof.
  intros h i y0 y1 y2 y3 L.
  assert (E : skipn i h = nth i h 0 :: nth (i + 1) h 0 :: nth (i + 2) h 0 :: nth (i + 3) h 0 :: skipn (i + 4) h).
  { revert i L. induction h as [|b h IH]; intros [|i] L; cbn in L; try lia.
    - destruct h as [|b1 [|b2 [|b3 h]]]; cbn in L; try lia. reflexivity.
    - cbn [skipn nth]. replace (S i + 1)%nat with (S (i + 1)) by lia. replace (S i + 2)%nat with (S (i + 2)) by lia.
      replace (S i + 3)%nat with (S (i + 3)) by lia. replace (S i + 4)%nat with (S (i + 4)) by lia.
      cbn [nth skipn]. apply IH. lia. }
  rewrite E. cbn [prefix_eqb]. rewrite !(Z.eqb_sym y0), !(Z.eqb_sym y1), !(Z.eqb_sym y2), !(Z.eqb_sym y3).
  destruct (_ =? _), (_ =? _), (_ =? _), (_ =? _); reflexivity.
Qed.

Lemma nth_map_u : forall (l : list byte) i b, nth_error l i = Some b -> nth i (map bv_unsigned l) 0 = bv_unsigned b.
Proof.
  induction l as [|x l IH]; intros [|i] b E; cbn in *; try discriminate.
  - inversion E; reflexivity.
  - apply IH. exact E.
Qed.

Lemma win_eq : forall (hb : list byte) (n0 n1 n2 n3 : byte) i b0 b1 b2 b3,
  (i + 4 <= length hb)%nat ->
  nth_error hb i = Some b0 -> nth_error hb (i + 1) = Some b1 -> nth_error hb (i + 2) = Some b2 ->
  nth_error hb (i + 3) = Some b3 ->
  prefix_eqb [bv_unsigned n0; bv_unsigned n1; bv_unsigned n2; bv_unsigned n3] (skipn i (map bv_unsigned hb)) =
  bv_eqb (S32 (wd4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3)))
         (S32 (wd4 (bv_unsigned n0) (bv_unsigned n1) (bv_unsigned n2) (bv_unsigned n3))).
Proof.
  intros hb n0 n1 n2 n3 i b0 b1 b2 b3 L E0 E1 E2 E3.
  rewrite pe4 by (rewrite length_map; lia).
  rewrite (nth_map_u hb i b0 E0), (nth_map_u hb (i + 1) b1 E1), (nth_map_u hb (i + 2) b2 E2),
          (nth_map_u hb (i + 3) b3 E3).
  rewrite S32_eqb by apply wd4_range. rewrite wd4_eqb. reflexivity.
Qed.

Theorem fourbyte_strstr_holds : fourbyte_strstr_contract.
Proof.
  unfold fourbyte_strstr_contract, FOURBYTE_STRSTR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m hb n4
         HH NH L3 HN LN NN.
  destruct n4 as [|n0 [|n1 [|n2 [|n3 [|]]]]]; cbn in LN; try lia.
  pose proof (bytes_at_bound _ _ _ _ HH) as BH. rewrite length_app in BH. cbn [length] in BH.
  pose proof (bytes_at_bound _ _ _ _ HN) as BN. cbn [length] in BN.
  assert (EXIT : forall (k : nat) (b : byte) (y5 y10 y11 y12 y14 y15 y16 y17 : word),
    bv_unsigned y12 = bv_unsigned a0 + Z.of_nat k + 3 ->
    (bv_unsigned b <> 0 -> strstr_val (bv_unsigned a0) hb [n0; n1; n2; n3] = bv_unsigned a0 + Z.of_nat k) ->
    (bv_unsigned b = 0 -> strstr_val (bv_unsigned a0) hb [n0; n1; n2; n3] = 0) ->
    evt rsegs (fourbyte_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 hb [n0; n1; n2; n3] m)
      (MS (mkR ra sp gp tp y5 t1 t2 s0 s1 y10 y11 y12 (v_sltu (Z_to_bv 64 0) (zxb b)) y14 y15 y16 y17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1cad4) fc None m (seg_rom rsegs))).
  { intros k b y5 y10 y11 y12 y14 y15 y16 y17 H12 HV HZ.
    step. step. step. step. rewrite exit_val.
    apply evt_done. unfold fourbyte_strstr_post.
    destruct (Z.eqb_spec (bv_unsigned b) 0) as [Hb|Hb].
    - rewrite (HZ Hb). do 14 eexists. reflexivity.
    - rewrite (HV Hb). replace (bv_unsigned y12 + -3) with (bv_unsigned a0 + Z.of_nat k) by lia.
      do 14 eexists. reflexivity. }
  assert (LOOP : forall (n j : nat) (c0 c1 c2 c3 : byte) (y5 y11 y12 y13 y14 y15 y16 y17 : word),
    (length hb - j = n)%nat -> (3 <= j)%nat -> (j < length hb)%nat ->
    nth_error hb (j - 3) = Some c0 -> nth_error hb (j - 2) = Some c1 -> nth_error hb (j - 1) = Some c2 ->
    nth_error hb j = Some c3 ->
    y11 = S32 (wd4 (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3)) ->
    bv_unsigned y12 = bv_unsigned a0 + Z.of_nat j ->
    (forall i, (i <= j - 3)%nat ->
       prefix_eqb [bv_unsigned n0; bv_unsigned n1; bv_unsigned n2; bv_unsigned n3] (skipn i (map bv_unsigned hb)) = false) ->
    evt rsegs (fourbyte_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 hb [n0; n1; n2; n3] m)
      (MS (mkR ra sp gp tp y5 t1 t2 s0 s1 (S32 (wd4 (bv_unsigned n0) (bv_unsigned n1) (bv_unsigned n2) (bv_unsigned n3)))
               y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1cab8) fc None m (seg_rom rsegs))).
  { induction n as [n IH] using lt_wf_ind.
    intros j c0 c1 c2 c3 y5 y11 y12 y13 y14 y15 y16 y17 Hn Hj3 Hjl E0 E1 E2 E3 H11 H12 INV. subst y11.
    destruct (sb_nth_full hb (S j) ltac:(lia)) as [c4 E4].
    assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned y12 + 1)) 1 = Some [c4])
      by (apply (sb_rd1 rsegs m (bv_unsigned a0) _ (S j) c4 _ HH E4); rewrite unsigned_lit by lia; lia).
    pose proof (sb_nth_full_zero hb (S j) c4 NH E4) as Z4.
    step. step. step. step.
    if_cases K4; zify_cond K4; rewrite ?sb_u_zxb, ?sb_u_byte in K4; cbv iota.
    - eapply (EXIT (j - 2)%nat c4); [rewrite unsigned_lit by lia; lia | intros; lia | intros _].
      apply Z4 in K4.
      unfold strstr_val. cbn [map]. rewrite ff_none; [reflexivity|].
      intros i Hi. destruct (Nat.le_gt_cases i (j - 3)) as [Li|Li]; [apply INV; exact Li|].
      apply pe_short. rewrite length_skipn, length_map. cbn [length]. lia.
    - assert (Jl : (S j < length hb)%nat) by (destruct (Nat.eq_dec (S j) (length hb)); [apply Z4 in e; lia | lia]).
      rewrite nth_error_app1 in E4 by lia.
      assert (W : prefix_eqb [bv_unsigned n0; bv_unsigned n1; bv_unsigned n2; bv_unsigned n3]
                    (skipn (j - 2) (map bv_unsigned hb)) =
                  bv_eqb (S32 (wd4 (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) (bv_unsigned c4)))
                         (S32 (wd4 (bv_unsigned n0) (bv_unsigned n1) (bv_unsigned n2) (bv_unsigned n3)))).
      { apply win_eq; [lia | exact E1 | replace (j - 2 + 1)%nat with (j - 1)%nat by lia; exact E2
        | replace (j - 2 + 2)%nat with j by lia; exact E3 | replace (j - 2 + 3)%nat with (S j) by lia; exact E4]. }
      step. step. rewrite w_step by apply wd4_range. rewrite wd4_shift.
      step. if_cases KW; unfold c_eq in KW; rewrite <- W in KW; cbv iota.
      + revert KW; destruct (prefix_eqb _ (skipn (j - 2) (map bv_unsigned hb))) eqn:PW; cbn; intros KW;
          try discriminate.
        eapply (IH (length hb - S j)%nat ltac:(lia) (S j) c1 c2 c3 c4).
        all: try reflexivity; try lia.
        * replace (S j - 3)%nat with (j - 2)%nat by lia. exact E1.
        * replace (S j - 2)%nat with (j - 1)%nat by lia. exact E2.
        * replace (S j - 1)%nat with j by lia. exact E3.
        * exact E4.
        * rewrite unsigned_lit by lia. lia.
        * intros i Hi. destruct (Nat.eq_dec i (j - 2)) as [->|NE]; [exact PW | apply INV; lia].
      + revert KW; destruct (prefix_eqb _ (skipn (j - 2) (map bv_unsigned hb))) eqn:PW; cbn; intros KW;
          try discriminate.
        eapply (EXIT (j - 2)%nat c4); [rewrite unsigned_lit by lia; lia | intros _ | intros; lia].
        unfold strstr_val. cbn [map]. rewrite (ff_some _ _ (j - 2)); [reflexivity | | exact PW].
        intros i' Hi'. apply INV. lia. }
  destruct (sb_nth_full hb 0 ltac:(lia)) as [h0 E0]. destruct (sb_nth_full hb 1 ltac:(lia)) as [h1 E1].
  destruct (sb_nth_full hb 2 ltac:(lia)) as [h2 E2]. destruct (sb_nth_full hb 3 ltac:(lia)) as [h3 E3].
  assert (RH3 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + 3)) 1 = Some [h3])
    by (apply (sb_rd1 rsegs m (bv_unsigned a0) _ 3 h3 _ HH E3); rewrite unsigned_lit by lia; lia).
  pose proof (sb_nth_full_zero hb 3 h3 NH E3) as Z3.
  step. step. step. step.
  if_cases K3; zify_cond K3; rewrite ?sb_u_zxb, ?sb_u_byte in K3; cbv iota.
  - eapply (EXIT 0%nat h3); [rewrite unsigned_lit by lia; lia | intros; lia | intros _].
    apply Z3 in K3.
    unfold strstr_val. cbn [map]. rewrite ff_none; [reflexivity|].
    intros i Hi. apply pe_short. rewrite length_skipn, length_map. cbn [length]. lia.
  - assert (L4 : (4 <= length hb)%nat) by (destruct (Nat.eq_dec 3 (length hb)) as [E|]; [apply Z3 in E; lia | lia]).
    rewrite nth_error_app1 in E0, E1, E2, E3 by lia.
    assert (RN0 : ov_read_bytes rsegs m a1 1 = Some [n0])
      by (apply (sb_rd1 rsegs m (bv_unsigned a1) _ 0 n0 _ HN eq_refl); lia).
    assert (RN1 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + 1)) 1 = Some [n1])
      by (apply (sb_rd1 rsegs m (bv_unsigned a1) _ 1 n1 _ HN eq_refl); rewrite unsigned_lit by lia; lia).
    assert (RN2 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + 2)) 1 = Some [n2])
      by (apply (sb_rd1 rsegs m (bv_unsigned a1) _ 2 n2 _ HN eq_refl); rewrite unsigned_lit by lia; lia).
    assert (RN3 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + 3)) 1 = Some [n3])
      by (apply (sb_rd1 rsegs m (bv_unsigned a1) _ 3 n3 _ HN eq_refl); rewrite unsigned_lit by lia; lia).
    assert (RH0 : ov_read_bytes rsegs m a0 1 = Some [h0]).
    { apply (sb_rd1 rsegs m (bv_unsigned a0) _ 0 h0 _ HH); [rewrite nth_error_app1 by lia; exact E0 | lia]. }
    assert (RH1 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + 1)) 1 = Some [h1]).
    { apply (sb_rd1 rsegs m (bv_unsigned a0) _ 1 h1 _ HH); [rewrite nth_error_app1 by lia; exact E1 |].
      rewrite unsigned_lit by lia; lia. }
    assert (RH2 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + 2)) 1 = Some [h2]).
    { apply (sb_rd1 rsegs m (bv_unsigned a0) _ 2 h2 _ HH); [rewrite nth_error_app1 by lia; exact E2 |].
      rewrite unsigned_lit by lia; lia. }
    assert (W : prefix_eqb [bv_unsigned n0; bv_unsigned n1; bv_unsigned n2; bv_unsigned n3]
                  (skipn 0 (map bv_unsigned hb)) =
                bv_eqb (S32 (wd4 (bv_unsigned h0) (bv_unsigned h1) (bv_unsigned h2) (bv_unsigned h3)))
                       (S32 (wd4 (bv_unsigned n0) (bv_unsigned n1) (bv_unsigned n2) (bv_unsigned n3))))
      by (apply win_eq; [lia | exact E0 | exact E1 | exact E2 | exact E3]).
    do 19 step. rewrite !w4_eq. step.
    if_cases KW; unfold c_eq in KW; rewrite <- W in KW; cbv iota.
    + revert KW; destruct (prefix_eqb _ (skipn 0 (map bv_unsigned hb))) eqn:PW; cbn; intros KW; try discriminate.
      eapply (EXIT 0%nat h3); [rewrite unsigned_lit by lia; lia | intros _ | intros; lia].
      unfold strstr_val. cbn [map]. rewrite (ff_some _ _ 0); [reflexivity | intros; lia | exact PW].
    + revert KW; destruct (prefix_eqb _ (skipn 0 (map bv_unsigned hb))) eqn:PW; cbn; intros KW; try discriminate.
      eapply (LOOP (length hb - 3)%nat 3%nat h0 h1 h2 h3).
      all: try reflexivity; try lia; try assumption.
      * rewrite unsigned_lit by lia. lia.
      * intros i Hi. replace i with 0%nat by lia. exact PW.
Qed.
