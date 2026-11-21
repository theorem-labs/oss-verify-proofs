From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Z_infl_pure2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateArmLib RefInflateOkb RefInflateA_DIST1 InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma rod_lenfix : forall m, mem_inv usegs m -> bytes_at usegs m Z_LENFIX (u32s (av32 lenfix_a 512)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_LENFIX; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma rod_distfix : forall m, mem_inv usegs m -> bytes_at usegs m Z_DISTFIX (u32s (av32 distfix_a 32)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_DISTFIX; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma u32s_read_sub : forall m A ws (i : Z) w (o n : nat) a,
  bytes_at usegs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> (o + n <= 4)%nat -> a = wa (A + 4 * i + Z.of_nat o) ->
  ov_read_bytes usegs m a n = Some (firstn n (skipn o (le4 w))).
Proof.
  intros m A ws i w o n a Hb Hn Hi Hon ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (A + 4 * i + Z.of_nat o) with (A + Z.of_nat (4 * Z.to_nat i + o)) by lia.
  rewrite (bytes_at_ov_read usegs m A (u32s ws) (4 * Z.to_nat i + o) n Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  f_equal. rewrite Eu, skipn_app, Hlu. rewrite skipn_all2 by (rewrite Hlu; lia). cbn [app].
  replace (4 * Z.to_nat i + o - 4 * Z.to_nat i)%nat with o by lia.
  rewrite skipn_app, firstn_app. rewrite length_skipn, length_le4.
  replace (n - (4 - o))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Lemma le4_code_op : forall v, firstn 1 (skipn 0 (le4 (wz v))) = [Z_to_bv 8 (code_op v)].
Proof.
  intros v. unfold le4, code_op. cbn [Z_to_le_bytes firstn skipn]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.
Lemma le4_code_bits : forall v, firstn 1 (skipn 1 (le4 (wz v))) = [Z_to_bv 8 (code_bits v)].
Proof.
  intros v. unfold le4, code_bits. cbn [Z_to_le_bytes firstn skipn]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  rewrite ?Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.
Lemma le4_code_val : forall v, firstn 2 (skipn 2 (le4 (wz v))) = le2 (wz (code_val v)).
Proof.
  intros v. unfold le4, le2, code_val. cbn [Z_to_le_bytes firstn skipn]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
  rewrite ?Z.shiftr_div_pow2 by lia. change (2^16) with 65536. change (2^8) with 256.
  f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul];
    Z.div_mod_to_equations; lia.
Qed.
Definition cp_ofs_ok (p : codeptr) : Prop := match p with CDyn ofs => 0 <= ofs | _ => True end.
Lemma code_rd : forall m L s p i (o n : nat) a,
  mem_inv usegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p -> (o + n <= 4)%nat ->
  a = wa (cp_addr L p + 4 * i + Z.of_nat o) ->
  ov_read_bytes usegs m a n = Some (firstn n (skipn o (le4 (wz (code_at s p i))))).
Proof.
  intros m L s p i o n a MI GC HP Hi Hon ->. destruct p as [ofs| |]; cbn [cp_addr code_at ctab_size cp_ofs_ok] in *.
  - destruct GC as [GB _].
    apply (u32s_read_sub m (il_As L + 1384) (av32 (is_codes s) 1444) (ofs + i) _ o n); [exact GB| apply av32_nth; lia| lia| exact Hon| f_equal; lia].
  - apply (u32s_read_sub m Z_LENFIX (av32 lenfix_a 512) i _ o n); [exact (rod_lenfix m MI)| apply av32_nth; lia| lia| exact Hon| reflexivity].
  - apply (u32s_read_sub m Z_DISTFIX (av32 distfix_a 32) i _ o n); [exact (rod_distfix m MI)| apply av32_nth; lia| lia| exact Hon| reflexivity].
Qed.
Lemma code_rd_bits : forall m L s p i a, mem_inv usegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i + 1) -> ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (code_bits (code_at s p i))].
Proof. intros m L s p i a MI GC HP Hi ->. rewrite <- le4_code_bits. apply (code_rd m L s p i 1 1); try assumption; [lia| reflexivity]. Qed.
Lemma code_rd_op : forall m L s p i a, mem_inv usegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i) -> ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (code_op (code_at s p i))].
Proof. intros m L s p i a MI GC HP Hi ->. rewrite <- le4_code_op. apply (code_rd m L s p i 0 1); try assumption; [lia| f_equal; cbn; lia]. Qed.
Lemma code_rd_val : forall m L s p i a, mem_inv usegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i + 2) -> ov_read_bytes usegs m a 2 = Some (le2 (wz (code_val (code_at s p i)))).
Proof. intros m L s p i a MI GC HP Hi ->. rewrite <- le4_code_val. apply (code_rd m L s p i 2 2); try assumption; [lia| reflexivity]. Qed.
Section DLvl.
Variables (c : icall) (s : inflate_state) (p : codeptr) (index need : Z -> Z).
Record dlvl (r : iregs) : Prop := mkDL {
  dl_i0 : 0 <= index (ir_hold r) < ctab_size p;
  dl_n0 : 0 <= need (code_at s p (index (ir_hold r))) <= 32;
  dl_found0 : need (code_at s p (index (ir_hold r))) <= ir_bits r ->
     DECODE_k 8 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r)
     /\ dchk 8 c index need (ctab_size p) (code_at s p) r = Some r;
  dl_dry0 : ir_bits r < need (code_at s p (index (ir_hold r))) -> ir_have r = 0 ->
     DECODE_k 8 p index need (mkW s c r) = ALeave (mkW s c r);
  dl_i1 : ir_bits r < need (code_at s p (index (ir_hold r))) -> ir_have r = 1 ->
     0 <= index (ir_hold (pullr c r)) < ctab_size p /\ 0 <= need (code_at s p (index (ir_hold (pullr c r)))) <= 32;
  dl_found1 : ir_bits r < need (code_at s p (index (ir_hold r))) -> ir_have r = 1 ->
     need (code_at s p (index (ir_hold (pullr c r)))) <= ir_bits (pullr c r) ->
     DECODE_k 8 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold (pullr c r)))) (mkW s c (pullr c r))
     /\ dchk 8 c index need (ctab_size p) (code_at s p) r = Some (pullr c r);
  dl_dry1 : ir_bits r < need (code_at s p (index (ir_hold r))) -> ir_have r = 1 ->
     ir_bits (pullr c r) < need (code_at s p (index (ir_hold (pullr c r)))) ->
     DECODE_k 8 p index need (mkW s c r) = ALeave (mkW s c (pullr c r)) }.
Lemma dlvl_of_dchk : forall r, dchk 8 c index need (ctab_size p) (code_at s p) r <> None -> 0 <= ir_have r <= 1 -> 0 <= ir_bits r -> dlvl r.
Proof.
  intros r HD Hh Hb.
  destruct (dchk 8 c index need (ctab_size p) (code_at s p) r) as [r'|] eqn:E; [clear HD|contradiction].
  assert (HV1 : ir_have r = 1 -> ir_have (pullr c r) = 0) by (intros E1; unfold pullr; cbn [ir_have]; rewrite E1; reflexivity).
  assert (HB1 : 0 <= ir_bits (pullr c r)) by (unfold pullr; cbn [ir_bits]; apply wrap32_range).
  pose proof (dchk_sound 8 s c p index need r r' E) as SND. cbv zeta in SND.
  destruct SND as (SI & SN & _ & _ & _ & _ & _ & SF & SD).
  destruct (Z.le_gt_cases (need (code_at s p (index (ir_hold r)))) (ir_bits r)) as [HF|HS].
  -
    destruct (dchk_found 8 c index need (ctab_size p) (code_at s p) r r' E HF) as [I0 ->].
    constructor; try lia; try (intros; exfalso; lia).
    intros _. split; [exact (SF HF)| exact E].
  - destruct (dchk_step 8 c index need (ctab_size p) (code_at s p) r r' E HS) as (I0 & N0 & [[H0 ->]|[H1 E7]]).
    + constructor; try lia; try (intros; exfalso; lia).
      intros _ _. exact (proj2 (SD HS)).
    + assert (H1' : ir_have r = 1) by lia.
      destruct (Z.le_gt_cases (need (code_at s p (index (ir_hold (pullr c r))))) (ir_bits (pullr c r))) as [HF1|HS1].
      * destruct (dchk_found 7 c index need (ctab_size p) (code_at s p) (pullr c r) r' E7 HF1) as [I1 ->].
        constructor; try lia; try (intros; exfalso; lia).
        intros _ _ _. split; [exact (SF HF1)| exact E].
      * destruct (dchk_step 7 c index need (ctab_size p) (code_at s p) (pullr c r) r' E7 HS1) as (I1 & N1 & [[H0 ->]|[H1b _]]); [|exfalso; rewrite (HV1 H1') in H1b; apply H1b; reflexivity].
        constructor; try lia; try (intros; exfalso; lia).
        intros _ _ _. exact (proj2 (SD HS1)).
Qed.
End DLvl.
Lemma decode_okb_lvl1 : forall two s c r p n, decode_okb two s c r p n = true ->
  0 <= n <= 15 /\ dchk 8 c (dec_idx1 n) code_bits (ctab_size p) (code_at s p) r <> None.
Proof.
  intros two s c r p n H. unfold decode_okb in H. cbv zeta in H.
  apply andb_prop in H. destruct H as [H H2]. apply andb_prop in H. destruct H as [H0 H1]. apply Z.leb_le in H0, H1.
  split; [lia|]. intros E. rewrite E in H2. discriminate H2.
Qed.
Lemma decode_okb_lvl2 : forall two s c r p n r1, decode_okb two s c r p n = true ->
  dchk 8 c (dec_idx1 n) code_bits (ctab_size p) (code_at s p) r = Some r1 ->
  code_bits (code_at s p (dec_idx1 n (ir_hold r1))) <= ir_bits r1 -> two (code_op (code_at s p (dec_idx1 n (ir_hold r1)))) = true ->
  code_bits (code_at s p (dec_idx1 n (ir_hold r1))) + code_op (code_at s p (dec_idx1 n (ir_hold r1))) <= 31
  /\ dchk 8 c (dec_idx2 (code_at s p (dec_idx1 n (ir_hold r1)))) (dec_need2 (code_at s p (dec_idx1 n (ir_hold r1)))) (ctab_size p) (code_at s p) r1 <> None.
Proof.
  intros two s c r p n r1 H E HB HT. unfold decode_okb in H. cbv zeta in H. rewrite E in H.
  apply andb_prop in H. destruct H as [_ H].
  replace (code_bits (code_at s p (dec_idx1 n (ir_hold r1))) <=? ir_bits r1) with true in H by (symmetry; apply Z.leb_le; exact HB).
  rewrite HT in H. cbn [andb] in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
  intros E2. rewrite E2 in H2. discriminate H2.
Qed.
Lemma ones_range15 : forall n, 0 <= n <= 15 -> 0 <= Z.ones n < 65536.
Proof.
  intros n H. rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)).
  assert (2 ^ n <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2^15) with 32768 in *. lia.
Qed.
Lemma dec_idx1_land : forall n h, 0 <= h -> 0 <= n <= 15 -> Z.land (Z.ones n) h = dec_idx1 n h.
Proof. intros n h Hh Hn. unfold dec_idx1. rewrite BITSv_land by lia. apply Z.land_comm. Qed.
Lemma dec_idx1_range : forall n h, 0 <= h -> 0 <= n <= 15 -> 0 <= dec_idx1 n h < 32768.
Proof.
  intros n h Hh Hn. unfold dec_idx1. rewrite BITSv_mod by lia. pose proof (Z.mod_pos_bound h (2^n) ltac:(apply Z.pow_pos_nonneg; lia)).
  assert (2 ^ n <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2^15) with 32768 in *. lia.
Qed.
Lemma ones_range31 : forall k, 0 <= k <= 31 -> 0 <= Z.ones k < 2147483648.
Proof.
  intros k H. rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2^31) with 2147483648 in *. lia.
Qed.
Lemma land_ones_le : forall h k, 0 <= k -> 0 <= Z.land h (Z.ones k) <= Z.ones k.
Proof.
  intros h k Hk. rewrite Z.land_ones by lia. rewrite Z.ones_equiv.
  pose proof (Z.mod_pos_bound h (2^k) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.
Lemma shiftr_le : forall a k, 0 <= a -> 0 <= k -> 0 <= a ≫ k <= a.
Proof.
  intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma dec_idx2_clang : forall last h, 0 <= h -> 0 <= code_bits last -> 0 <= code_op last -> code_bits last + code_op last <= 31 ->
  dec_idx2 last h = (Z.land h (Z.ones (code_bits last + code_op last)) ≫ code_bits last) + code_val last.
Proof. intros last h Hh Hb Ho Hk. unfold dec_idx2. rewrite BITSv_land by lia. lia. Qed.
Lemma srlw_small : forall x k, 0 <= x < 2147483648 -> 0 <= k <= 31 -> bv_swrap 32 (bv_wrap 32 x ≫ (k mod 32)) = x ≫ k.
Proof.
  intros x k Hx Hk. rewrite (bv_wrap_small 32 x) by (unfold bv_modulus; cbn; lia). rewrite (Z.mod_small k 32) by lia.
  pose proof (shiftr_le x k ltac:(lia) ltac:(lia)). apply bv_swrap32_id. change (2^31) with 2147483648. lia.
Qed.
Lemma zext32_x4 : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 30 = 4 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^30) with 1073741824. Z.div_mod_to_equations. lia.
Qed.
Definition code_lo (v : Z) : Z := code_op v + 256 * code_bits v.
Definition code_w (v : Z) : Z := code_lo v + 65536 * code_val v.
Lemma land255_mod : forall a, Z.land a 255 = a mod 256.
Proof. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma code_op_eq : forall v, code_op v = v mod 256.
Proof. intros v. unfold code_op. apply land255_mod. Qed.
Lemma code_bits_eq : forall v, code_bits v = (v / 256) mod 256.
Proof. intros v. unfold code_bits. rewrite land255_mod, Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma code_lo_range : forall v, 0 <= code_lo v < 65536.
Proof. intros v. unfold code_lo. pose proof (code_op_range v). pose proof (code_bits_range v). lia. Qed.
Lemma code_w_range : forall v, 0 <= code_w v < 4294967296.
Proof. intros v. unfold code_w. pose proof (code_lo_range v). pose proof (code_val_range v). lia. Qed.
Lemma code_lo_eq : forall v, code_lo v = v mod 65536.
Proof.
  intros v. unfold code_lo. rewrite code_op_eq, code_bits_eq.
  Z.div_mod_to_equations. lia.
Qed.
Lemma le4_code_lo : forall v, firstn 2 (skipn 0 (le4 (wz v))) = le2 (wz (code_lo v)).
Proof.
  intros v. rewrite code_lo_eq. unfold le4, le2. cbn [Z_to_le_bytes firstn skipn]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  rewrite ?Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul];
    Z.div_mod_to_equations; lia.
Qed.
Lemma code_rd_lo : forall m L s p i a, mem_inv usegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i) -> ov_read_bytes usegs m a 2 = Some (le2 (wz (code_lo (code_at s p i)))).
Proof. intros m L s p i a MI GC HP Hi ->. rewrite <- le4_code_lo. apply (code_rd m L s p i 0 2); try assumption; try lia. f_equal; cbn; lia. Qed.
Lemma code_w_or : forall v, Z.lor (code_val v ≪ 16) (code_lo v) = code_w v.
Proof.
  intros v. pose proof (code_lo_range v) as R. pose proof (code_val_range v) as RV. unfold code_w.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_hi_lo by (try lia; change (2^16) with 65536; lia). change (2^16) with 65536. lia.
Qed.
Lemma code_w_sh8 : forall v, code_w v ≫ 8 = code_bits v + 256 * code_val v.
Proof.
  intros v. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. unfold code_w, code_lo.
  pose proof (code_op_range v). pose proof (code_bits_range v). pose proof (code_val_range v). Z.div_mod_to_equations. lia.
Qed.
Lemma code_w_op : forall v, Z.land (code_w v) 255 = code_op v.
Proof.
  intros v. rewrite land255_mod. unfold code_w, code_lo.
  pose proof (code_op_range v). pose proof (code_bits_range v). pose proof (code_val_range v). Z.div_mod_to_equations. lia.
Qed.
Lemma code_w_val : forall v, code_w v ≫ 16 = code_val v.
Proof.
  intros v. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536. unfold code_w, code_lo.
  pose proof (code_op_range v). pose proof (code_bits_range v). pose proof (code_val_range v). Z.div_mod_to_equations. lia.
Qed.
Lemma land_lo8 : forall x msk, 0 <= msk < 256 -> Z.land x msk = Z.land (x mod 256) msk.
Proof.
  intros x msk Hm. rewrite <- land255_mod. rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm. rewrite land255_mod. symmetry. apply Z.mod_small. lia.
Qed.
Lemma code_w_sh8_land : forall v msk, 0 <= msk < 256 -> Z.land (code_w v ≫ 8) msk = Z.land (code_bits v) msk.
Proof.
  intros v msk Hm. rewrite (land_lo8 _ msk Hm). rewrite code_w_sh8. f_equal.
  pose proof (code_bits_range v). pose proof (code_val_range v). Z.div_mod_to_equations. lia.
Qed.
Lemma code_w_bits : forall v, Z.land (code_w v ≫ 8) 255 = code_bits v.
Proof. intros v. rewrite code_w_sh8_land by lia. rewrite land255_mod. apply Z.mod_small. apply code_bits_range. Qed.
Lemma byte_lt64_land192 : forall b, 0 <= b < 64 -> Z.land b 192 = 0.
Proof.
  intros b Hb.
  assert (H : forallb (fun i : nat => Z.land (Z.of_nat i) 192 =? 0) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.
Lemma byte_lt32_land224 : forall b, 0 <= b < 32 -> Z.land b 224 = 0.
Proof.
  intros b Hb.
  assert (H : forallb (fun i : nat => Z.land (Z.of_nat i) 224 =? 0) (seq 0 32) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.
Lemma land31_small : forall b, 0 <= b < 32 -> Z.land b 31 = b.
Proof. intros b Hb. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma code_w_g192 : forall v, code_bits v < 64 -> Z.land (code_w v ≫ 8) 192 = 0.
Proof. intros v H. rewrite code_w_sh8_land by lia. apply byte_lt64_land192. pose proof (code_bits_range v). lia. Qed.
Lemma code_w_g31 : forall v, code_bits v < 32 -> Z.land (code_w v ≫ 8) 31 = code_bits v.
Proof. intros v H. rewrite code_w_sh8_land by lia. apply land31_small. pose proof (code_bits_range v). lia. Qed.
Lemma code_w_g63 : forall v, code_bits v < 64 -> Z.land (code_w v ≫ 8) 63 = code_bits v.
Proof. intros v H. rewrite code_w_sh8_land by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. pose proof (code_bits_range v). lia. Qed.
Lemma code_w_ge000 : forall v, code_bits v < 32 -> Z.land (code_w v) 57344 = 0.
Proof.
  intros v H. pose proof (code_w_range v) as R.
  assert (LO : Z.land (Z.land (code_w v) 57344) 255 = 0).
  { rewrite <- Z.land_assoc. change (Z.land 57344 255) with 0. apply Z.land_0_r. }
  assert (HI : (Z.land (code_w v) 57344) ≫ 8 = 0).
  { rewrite Z.shiftr_land. change (57344 ≫ 8) with 224. rewrite code_w_sh8_land by lia. apply byte_lt32_land224. pose proof (code_bits_range v). lia. }
  assert (NN : 0 <= Z.land (code_w v) 57344) by (apply Z.land_nonneg; lia).
  rewrite land255_mod in LO. rewrite Z.shiftr_div_pow2 in HI by lia. change (2^8) with 256 in HI.
  Z.div_mod_to_equations. lia.
Qed.
Lemma cp_addr_rng : forall L p i, cp_ofs_ok p -> 0 <= i < ctab_size p -> 0 < il_As L ->
  0 < cp_addr L p /\ cp_addr L p + 4 * i + 4 <= Z.max (il_As L + 7160) 77824.
Proof.
  intros L p i HP Hi HA. destruct p as [ofs| |]; cbn [cp_addr ctab_size cp_ofs_ok] in *; unfold Z_LENFIX, Z_DISTFIX in *; lia.
Qed.
Lemma code_w_or_step : forall v,
  Z.lor (Z.land (Z.land (code_val v) 18446744073709551615 ≪ 16) 18446744073709551615) (Z.land (code_lo v) 18446744073709551615) = code_w v.
Proof.
  intros v. pose proof (code_val_range v) as RV. pose proof (code_lo_range v) as RL.
  rewrite (land_ones64 (code_val v)) by lia. rewrite (land_ones64 (code_lo v)) by lia.
  rewrite (land_ones64 (code_val v ≪ 16)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^16) with 65536; lia).
  apply code_w_or.
Qed.
Lemma ddrop_facts' : forall r n, 0 <= n <= ir_bits r -> ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 ->
  ir_in (ddrop r n) = ir_in r /\ ir_out (ddrop r n) = ir_out r /\ ir_ret (ddrop r n) = ir_ret r /\ ir_put (ddrop r n) = ir_put r
  /\ ir_left (ddrop r n) = ir_left r /\ ir_bits (ddrop r n) = ir_bits r - n /\ 0 <= ir_hold (ddrop r n) < 2^64
  /\ ir_have (ddrop r n) = ir_have r /\ ir_next (ddrop r n) = ir_next r.
Proof.
  intros r n Hn Hb Hh. unfold ddrop. destruct r; cbn in *. rewrite wrap32_id by lia.
  pose proof (shiftr_le ir_hold n ltac:(lia) ltac:(lia)). repeat split; try reflexivity; lia.
Qed.
Lemma shl32_shr29 : forall h, 0 <= h < 4294967296 -> Z.land (h ≪ 32) 18446744073709551615 ≫ 29 = 8 * h.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite land_ones64 by (change (2^32) with 4294967296; lia).
  change (2^32) with (8 * 2^29). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shl32_shr32 : forall h, 0 <= h < 4294967296 -> (h ≪ 32) ≫ 32 = h.
Proof. intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. Qed.
Lemma code_w_land15 : forall v, Z.land (code_w v) 15 = Z.land (code_op v) 15.
Proof. intros v. rewrite (land_lo8 (code_w v) 15) by lia. rewrite <- land255_mod, code_w_op. reflexivity. Qed.
Lemma land15_small : forall b, 0 <= b < 16 -> Z.land b 15 = b.
Proof. intros b Hb. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma addw_land64 : forall a b, - 2^31 <= a + b < 2^31 -> bv_swrap 32 (Z.land a 18446744073709551615 + b) = a + b.
Proof.
  intros a b H. rewrite (bv_swrap32_eqm _ (a + b)); [apply bv_swrap32_id; lia|].
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite (Z.mod_eq a (2^64)) by lia.
  replace (a - 2 ^ 64 * (a / 2 ^ 64) + b - (a + b)) with ((- (2^32 * (a / 2^64))) * 2^32) by lia.
  apply Z_mod_mult.
Qed.
Lemma subw_land64 : forall a b, - 2^31 <= a - b < 2^31 -> bv_swrap 32 (a - Z.land b 18446744073709551615) = a - b.
Proof.
  intros a b H. rewrite (bv_swrap32_eqm _ (a - b)); [apply bv_swrap32_id; lia|].
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite (Z.mod_eq b (2^64)) by lia.
  replace (a - (b - 2 ^ 64 * (b / 2 ^ 64)) - (a - b)) with ((2^32 * (b / 2^64)) * 2^32) by lia.
  apply Z_mod_mult.
Qed.
