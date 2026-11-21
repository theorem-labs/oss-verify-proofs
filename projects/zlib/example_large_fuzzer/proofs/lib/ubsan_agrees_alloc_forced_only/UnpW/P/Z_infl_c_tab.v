(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_DIST1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rod_lenfix : forall m, mem_inv psegs m -> bytes_at psegs m Z_LENFIX (u32s (av32 lenfix_a 512)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_LENFIX; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma rod_distfix : forall m, mem_inv psegs m -> bytes_at psegs m Z_DISTFIX (u32s (av32 distfix_a 32)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_DISTFIX; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

Lemma u32s_read_sub : forall m A ws (i : Z) w (o n : nat) a,
  bytes_at psegs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> (o + n <= 4)%nat -> a = wa (A + 4 * i + Z.of_nat o) ->
  ov_read_bytes psegs m a n = Some (firstn n (skipn o (le4 w))).
Proof.
  intros m A ws i w o n a Hb Hn Hi Hon ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (A + 4 * i + Z.of_nat o) with (A + Z.of_nat (4 * Z.to_nat i + o)) by lia.
  rewrite (bytes_at_ov_read psegs m A (u32s ws) (4 * Z.to_nat i + o) n Hb).
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
  mem_inv psegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p -> (o + n <= 4)%nat ->
  a = wa (cp_addr L p + 4 * i + Z.of_nat o) ->
  ov_read_bytes psegs m a n = Some (firstn n (skipn o (le4 (wz (code_at s p i))))).
Proof.
  intros m L s p i o n a MI GC HP Hi Hon ->. destruct p as [ofs| |]; cbn [cp_addr code_at ctab_size cp_ofs_ok] in *.
  - destruct GC as [GB _].
    apply (u32s_read_sub m (il_As L + 1384) (av32 (is_codes s) 1444) (ofs + i) _ o n); [exact GB| apply av32_nth; lia| lia| exact Hon| f_equal; lia].
  - apply (u32s_read_sub m Z_LENFIX (av32 lenfix_a 512) i _ o n); [exact (rod_lenfix m MI)| apply av32_nth; lia| lia| exact Hon| reflexivity].
  - apply (u32s_read_sub m Z_DISTFIX (av32 distfix_a 32) i _ o n); [exact (rod_distfix m MI)| apply av32_nth; lia| lia| exact Hon| reflexivity].
Qed.

Lemma code_rd_bits : forall m L s p i a, mem_inv psegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i + 1) -> ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (code_bits (code_at s p i))].
Proof. intros m L s p i a MI GC HP Hi ->. rewrite <- le4_code_bits. apply (code_rd m L s p i 1 1); try assumption; [lia| reflexivity]. Qed.
Lemma code_rd_op : forall m L s p i a, mem_inv psegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i) -> ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (code_op (code_at s p i))].
Proof. intros m L s p i a MI GC HP Hi ->. rewrite <- le4_code_op. apply (code_rd m L s p i 0 1); try assumption; [lia| f_equal; cbn; lia]. Qed.
Lemma code_rd_val : forall m L s p i a, mem_inv psegs m -> icodes m L s -> cp_ofs_ok p -> 0 <= i < ctab_size p ->
  a = wa (cp_addr L p + 4 * i + 2) -> ov_read_bytes psegs m a 2 = Some (le2 (wz (code_val (code_at s p i)))).
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
