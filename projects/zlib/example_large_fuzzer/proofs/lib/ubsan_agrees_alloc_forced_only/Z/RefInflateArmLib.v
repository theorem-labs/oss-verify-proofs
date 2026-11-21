(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ArmForEq.
  Variable iv : ivariant.
Variable flush : Z.

End ArmForEq.

Definition adler_canon_b (a : Z) : bool :=
  (0 <=? a) && (a <? 2 ^ 32) && (lo16 a <? ABASE) && (hi16 a <? ABASE).
Lemma adler_canon_b_ok : forall a, adler_canon_b a = true -> adler_canon a.
Proof.
  intros a H. unfold adler_canon_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  unfold adler_canon. lia.
Qed.

Definition leave_okb (s : inflate_state) : bool :=
  (Z.land (is_wrap s) 4 =? 0) || negb (is_flags s =? 0) || adler_canon_b (is_check s).
Lemma leave_okb_ok : forall s, leave_okb s = true ->
  Z.land (is_wrap s) 4 <> 0 -> is_flags s = 0 -> adler_canon (is_check s).
Proof.
  intros s H Hw Hf. unfold leave_okb in H.
  apply Bool.orb_prop in H. destruct H as [H|H]; [apply Bool.orb_prop in H; destruct H as [H|H]|].
  - apply Z.eqb_eq in H. exfalso. exact (Hw H).
  - rewrite Hf, Z.eqb_refl in H. discriminate H.
  - exact (adler_canon_b_ok _ H).
Qed.

Definition BAD_pcs : list Z :=
  [0x194f0; 0x195cc; 0x198c8; 0x19f18; 0x19fe0; 0x1ad40; 0x1b2fc; 0x1b4d8; 0x1b578; 0x1b5f4; 0x1b710].

Definition arm_stops : list Z :=
  [0x190a4; 0x190c4; 0x190c8; 0x195e4; 0x1c240; 0x20fc4; 0x200c4; 0x20c10; 0x26f9c] ++ BAD_pcs ++ arm_pcs.
Definition arm_vb : list (nat * Z) :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 32); (36%nat, 2 ^ 63); (37%nat, 2 ^ 32);
   (38%nat, 2 ^ 64); (39%nat, 64); (40%nat, 2 ^ 32); (41%nat, 2 ^ 32); (42%nat, 16); (43%nat, 2 ^ 63)].

Definition arm_var0 : nat := 44.

Local Ltac lreg_in := cbn; repeat (first [ left; reflexivity | right ]).

Ltac sxlia := unfold szwrap; change (2 ^ (32 - 1)) with 2147483648; Z.to_euclidean_division_equations; lia.

Lemma szwrap32_mod64_zero : forall x, 0 <= x < 2 ^ 32 -> (szwrap 32 x mod 2 ^ 64 = 0 <-> x = 0).
Proof. intros x Hx. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Lemma wrap8_range : forall x, 0 <= wrap8 x < 256.
Proof. intros x. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Definition pullr (c : icall) (r : iregs) : iregs :=
  mkIR (ir_next r + 1) (wrap32 (ir_have r - 1)) (ir_put r) (ir_left r)
       (wrap64 (ir_hold r + shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r))) (wrap32 (ir_bits r + 8))
       (ir_in r) (ir_out r) (ir_ret r).

Lemma PULLBYTE_eq : forall s c r,
  PULLBYTE (mkW s c r) = if ir_have r =? 0 then ALeave (mkW s c r) else ARun tt (mkW s c (pullr c r)).
Proof. intros. reflexivity. Qed.

Lemma NEEDBITS_k_S : forall k n s c r,
  NEEDBITS_k (S k) n (mkW s c r)
  = if ir_bits r <? n then
      if ir_have r =? 0 then ALeave (mkW s c r) else NEEDBITS_k k n (mkW s c (pullr c r))
    else ARun tt (mkW s c r).
Proof.
  intros.
  change (NEEDBITS_k (S k) n (mkW s c r))
    with (abind (gr ir_bits) (fun bits => if bits <? n then abind PULLBYTE (fun _ => NEEDBITS_k k n) else aret tt) (mkW s c r)).
  unfold abind at 1. cbn [gr w_r]. destruct (ir_bits r <? n); [|reflexivity].
  unfold abind. rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.
Lemma NEEDBITS_k_done : forall k n s c r, n <= ir_bits r -> NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s c r).
Proof.
  intros k n s c r H. destruct k; [reflexivity|]. rewrite NEEDBITS_k_S.
  replace (ir_bits r <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma pullr_facts : forall c r,
  0 < ir_have r < 2 ^ 32 -> 0 <= ir_bits r <= 56 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  0 <= arr_get (ic_input c) (ir_next r) < 256 ->
  ir_next (pullr c r) = ir_next r + 1 /\ ir_have (pullr c r) = ir_have r - 1
  /\ ir_put (pullr c r) = ir_put r /\ ir_left (pullr c r) = ir_left r
  /\ ir_hold (pullr c r) = ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r
  /\ ir_bits (pullr c r) = ir_bits r + 8
  /\ ir_in (pullr c r) = ir_in r /\ ir_out (pullr c r) = ir_out r /\ ir_ret (pullr c r) = ir_ret r
  /\ 0 <= ir_hold (pullr c r) < 2 ^ (ir_bits r + 8).
Proof.
  intros c r Hh Hb Hho Hby. unfold pullr. cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
  assert (Hp : 2 ^ ir_bits r * 2 ^ 8 = 2 ^ (ir_bits r + 8)) by (rewrite <- Z.pow_add_r by lia; reflexivity).
  assert (Hp2 : 2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  assert (Hsh : shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r) = arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r).
  { unfold shl64. rewrite Z.shiftl_mul_pow2 by lia. apply wrap64_id. nia. }
  rewrite Hsh.
  assert (Hsum : 0 <= ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r < 2 ^ (ir_bits r + 8)) by nia.
  repeat split; try reflexivity.
  - apply wrap32_id. lia.
  - apply wrap64_id. lia.
  - apply wrap32_id. lia.
  - rewrite wrap64_id by lia. lia.
  - rewrite wrap64_id by lia. lia.
Qed.

Lemma gr_eq : forall {A} (f : iregs -> A) s c r, gr f (mkW s c r) = ARun (f r) (mkW s c r).
Proof. reflexivity. Qed.
Lemma gs_eq : forall {A} (f : inflate_state -> A) s c r, gs f (mkW s c r) = ARun (f s) (mkW s c r).
Proof. reflexivity. Qed.
Lemma us_eq : forall f s c r, us f (mkW s c r) = ARun tt (mkW (f s) c r).
Proof. reflexivity. Qed.
Lemma uc_eq : forall f s c r, uc f (mkW s c r) = ARun tt (mkW s (f c) r).
Proof. reflexivity. Qed.
Lemma ur_eq : forall f s c r, ur f (mkW s c r) = ARun tt (mkW s c (f r)).
Proof. reflexivity. Qed.
Lemma aret_eq : forall {A} (a : A) w, aret a w = ARun a w.
Proof. reflexivity. Qed.
Lemma aleave_eq : forall {A} w, @aleave A w = ALeave w.
Proof. reflexivity. Qed.
Lemma BITS_eq : forall n s c r, BITS n (mkW s c r) = ARun (BITSv (ir_hold r) n) (mkW s c r).
Proof. reflexivity. Qed.
Lemma HOLD_eq : forall s c r, HOLD (mkW s c r) = ARun (ir_hold r) (mkW s c r).
Proof. reflexivity. Qed.
Lemma DROPBITS_eq : forall n s c r,
  DROPBITS n (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)))).
Proof. reflexivity. Qed.
Lemma INITBITS_eq : forall s c r, INITBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r 0) 0)).
Proof. reflexivity. Qed.
Lemma BYTEBITS_eq : forall s c r,
  BYTEBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)))).
Proof. reflexivity. Qed.
Lemma set_mode_eq : forall m s c r, set_mode m (mkW s c r) = ARun tt (mkW (iset_mode s m) c r).
Proof. reflexivity. Qed.
Lemma go_bad_eq : forall m s c r, go_bad m (mkW s c r) = ARun tt (mkW (iset_mode s BAD) (icset_msg c m) r).
Proof. reflexivity. Qed.
Lemma set_adler_check_eq : forall v s c r, set_adler_check v (mkW s c r) = ARun tt (mkW (iset_check s v) (icset_adler c v) r).
Proof. reflexivity. Qed.

Ltac mstep1 lem := rewrite abind_run; rewrite lem; cbv beta iota.

Ltac irnorm := cbv beta iota delta [irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
                                   w_s w_c w_r wset_s wset_c wset_r];
               cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].

Lemma BITSv_land : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = Z.land h (Z.ones n).
Proof.
  intros h n Hh Hn. unfold BITSv, zmask, wrap32.
  rewrite Z.shiftl_1_l. change 4294967295 with (Z.ones 32).
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite <- Z.land_assoc. f_equal.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)) as Hp.
  assert (Hle : 2 ^ n <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i n); destruct (Z.ltb_spec i 32); cbn; try reflexivity; lia.
Qed.

Local Ltac iwf_upd_tac H :=
  unfold iwf, iwfx in *;
  match goal with |- context [is_mode ?st] => idtac end;
  decompose [and] H; repeat apply conj; first [assumption | lia | exact I].

Lemma hold_drop : forall h b n, 0 <= n <= b -> 0 <= h < 2 ^ b -> 0 <= h / 2 ^ n < 2 ^ (b - n).
Proof.
  intros h b n Hn Hh. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)) as Hp.
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (b - n)) with b by lia. lia.
Qed.

Lemma land_m8 : forall b, 0 <= b -> Z.land b (-8) = b - Z.land b 7.
Proof.
  intros b Hb. change (-8) with (Z.lnot (Z.ones 3)). rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  Z.to_euclidean_division_equations; lia.
Qed.
Lemma land7_mod : forall b, Z.land b 7 = b mod 2 ^ 3.
Proof. intros b. change 7 with (Z.ones 3). apply Z.land_ones. lia. Qed.
Lemma land7_range : forall b, 0 <= Z.land b 7 < 8.
Proof. intros b. rewrite land7_mod. apply Z.mod_pos_bound. lia. Qed.

Fixpoint pulln (c : icall) (r : iregs) (k : nat) : iregs :=
  match k with O => r | S k' => pullr c (pulln c r k') end.

Fixpoint holdn (c : icall) (r : iregs) (k : nat) : Z :=
  match k with
  | O => ir_hold r
  | S k' => holdn c r k' + arr_get (ic_input c) (ir_next r + Z.of_nat k') * 2 ^ (ir_bits r + 8 * Z.of_nat k')
  end.

Section ZSc.
Variable strm : Z.
Variable S : Z.
Variable fa : Z.
Variable ff : Z.
Hypothesis Hstrm : 0 <= strm /\ strm + 112 <= 2 ^ 63.
End ZSc.

Lemma testbit_65280 : forall m, 0 <= m -> Z.testbit 65280 m = ((8 <=? m) && (m <? 16))%bool.
Proof.
  intros m Hm. replace 65280 with (Z.shiftl (Z.ones 8) 8) by reflexivity. rewrite Z.shiftl_spec by lia.
  destruct (Z.leb_spec 8 m).
  - rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. destruct (Z.ltb_spec (m - 8) 8); destruct (Z.ltb_spec m 16); try reflexivity; lia.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Definition zswap_m (h : Z) : Z :=
  Z.lor (h mod 2 ^ 32 / 2 ^ 24) (Z.land (h / 2 ^ 8) 65280) + (Z.land (h * 2 ^ 8) 16711680 + h mod 2 ^ 8 * 2 ^ 24).

Lemma RESTORE_eq : forall s c r,
  RESTORE (mkW s c r) = mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r))
                            (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) r.
Proof. reflexivity. Qed.

Ltac t2_vac := let X := fresh in intros X; exfalso; revert X; clear; intros X; cbv in X;
  repeat (destruct X as [X|X]; [discriminate X|]); discriminate X.

Ltac t2_in := cbv; repeat (first [left; reflexivity | right]); reflexivity.
