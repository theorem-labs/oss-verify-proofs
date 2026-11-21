(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section ArmForEq.
  Variable iv : ivariant.
Variable flush : Z.
  Lemma arm_for_HEAD : arm_for iv flush HEAD = arm_HEAD iv. Proof. reflexivity. Qed.
  Lemma arm_for_FLAGS : arm_for iv flush FLAGS = arm_FLAGS. Proof. reflexivity. Qed.
  Lemma arm_for_TIME : arm_for iv flush TIME = arm_TIME. Proof. reflexivity. Qed.
  Lemma arm_for_OS : arm_for iv flush OS = arm_OS. Proof. reflexivity. Qed.
  Lemma arm_for_EXLEN : arm_for iv flush EXLEN = arm_EXLEN. Proof. reflexivity. Qed.
  Lemma arm_for_EXTRA : arm_for iv flush EXTRA = arm_EXTRA. Proof. reflexivity. Qed.
  Lemma arm_for_NAME : arm_for iv flush NAME = arm_NAME. Proof. reflexivity. Qed.
  Lemma arm_for_COMMENT : arm_for iv flush COMMENT = arm_COMMENT. Proof. reflexivity. Qed.
  Lemma arm_for_HCRC : arm_for iv flush HCRC = arm_HCRC. Proof. reflexivity. Qed.
  Lemma arm_for_DICTID : arm_for iv flush DICTID = arm_DICTID iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_DICT : arm_for iv flush DICT = arm_DICT iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_TYPE : arm_for iv flush TYPE = arm_TYPE iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_TYPEDO : arm_for iv flush TYPEDO = arm_TYPEDO iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_STORED : arm_for iv flush STORED = arm_STORED iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_COPY_ : arm_for iv flush COPY_ = arm_COPY_. Proof. reflexivity. Qed.
  Lemma arm_for_COPY : arm_for iv flush COPY = arm_COPY. Proof. reflexivity. Qed.
  Lemma arm_for_TABLE : arm_for iv flush TABLE = arm_TABLE iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_LENLENS : arm_for iv flush LENLENS = arm_LENLENS iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_CODELENS : arm_for iv flush CODELENS = arm_CODELENS iv flush. Proof. reflexivity. Qed.
  Lemma arm_for_LEN_ : arm_for iv flush LEN_ = arm_LEN_ iv. Proof. reflexivity. Qed.
  Lemma arm_for_LEN : arm_for iv flush LEN = arm_LEN iv. Proof. reflexivity. Qed.
  Lemma arm_for_LENEXT : arm_for iv flush LENEXT = arm_LENEXT iv. Proof. reflexivity. Qed.
  Lemma arm_for_DIST : arm_for iv flush DIST = arm_DIST iv. Proof. reflexivity. Qed.
  Lemma arm_for_DISTEXT : arm_for iv flush DISTEXT = arm_DISTEXT iv. Proof. reflexivity. Qed.
  Lemma arm_for_MATCH : arm_for iv flush MATCH = arm_MATCH iv. Proof. reflexivity. Qed.
  Lemma arm_for_LIT : arm_for iv flush LIT = arm_LIT. Proof. reflexivity. Qed.
  Lemma arm_for_CHECK : arm_for iv flush CHECK = arm_CHECK. Proof. reflexivity. Qed.
  Lemma arm_for_LENGTH : arm_for iv flush LENGTH = arm_LENGTH. Proof. reflexivity. Qed.
  Lemma arm_for_DONE : arm_for iv flush DONE = arm_DONE. Proof. reflexivity. Qed.
  Lemma arm_for_BAD : arm_for iv flush BAD = arm_BAD. Proof. reflexivity. Qed.
  Lemma arm_for_MEM : arm_for iv flush MEM = arm_MEM. Proof. reflexivity. Qed.
  Lemma arm_for_SYNC : arm_for iv flush SYNC = arm_SYNC. Proof. reflexivity. Qed.
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



Lemma icset_outbuf_facts : forall c a,
  ic_next_in (icset_outbuf c a) = ic_next_in c /\ ic_avail_in (icset_outbuf c a) = ic_avail_in c
  /\ ic_next_out (icset_outbuf c a) = ic_next_out c /\ ic_avail_out (icset_outbuf c a) = ic_avail_out c
  /\ ic_input (icset_outbuf c a) = ic_input c /\ ic_outbuf (icset_outbuf c a) = a
  /\ zstrm_of_icall (icset_outbuf c a) = zstrm_of_icall c
  /\ ic_total_in (icset_outbuf c a) = ic_total_in c /\ ic_total_out (icset_outbuf c a) = ic_total_out c
  /\ ic_adler (icset_outbuf c a) = ic_adler c /\ ic_data_type (icset_outbuf c a) = ic_data_type c.
Proof. intros c a. destruct c. repeat split; reflexivity. Qed.

Lemma iwf_x : forall s, iwf s -> iwfx s.
Proof. intros s H. unfold iwf in H. decompose [and] H. assumption. Qed.



Ltac sxlia := unfold szwrap; change (2 ^ (32 - 1)) with 2147483648; Z.to_euclidean_division_equations; lia.
Lemma szwrap32_u32 : forall x, 0 <= x < 2 ^ 32 -> szwrap 32 x = x \/ szwrap 32 x = x - 2 ^ 32.
Proof. intros x Hx. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.
Lemma szwrap32_mod64_zero : forall x, 0 <= x < 2 ^ 32 -> (szwrap 32 x mod 2 ^ 64 = 0 <-> x = 0).
Proof. intros x Hx. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Lemma wrap32_pred : forall x, 0 < x < 2 ^ 32 -> wrap32 (x - 1) = x - 1.
Proof. intros x Hx. apply wrap32_id. lia. Qed.
Lemma wrap8_range : forall x, 0 <= wrap8 x < 256.
Proof. intros x. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.


Lemma icset_msg_facts : forall c m,
  ic_next_in (icset_msg c m) = ic_next_in c /\ ic_avail_in (icset_msg c m) = ic_avail_in c
  /\ ic_next_out (icset_msg c m) = ic_next_out c /\ ic_avail_out (icset_msg c m) = ic_avail_out c
  /\ ic_input (icset_msg c m) = ic_input c /\ ic_outbuf (icset_msg c m) = ic_outbuf c
  /\ ic_total_in (icset_msg c m) = ic_total_in c /\ ic_total_out (icset_msg c m) = ic_total_out c
  /\ ic_adler (icset_msg c m) = ic_adler c /\ ic_data_type (icset_msg c m) = ic_data_type c.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.


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

Lemma iwf_set_last : forall st v, - 2 ^ 31 <= v < 2 ^ 31 -> iwf st -> iwf (iset_last st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_fixedtables : forall st, iwf st -> iwf (fixedtables st).
Proof.
  intros st H. unfold fixedtables, iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia | exact I].
Qed.
Lemma iwf_set_length : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_length st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_check : forall st v, 0 <= v < 2 ^ 64 -> iwf st -> iwf (iset_check st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_flags : forall st v, - 2 ^ 31 <= v < 2 ^ 31 -> iwf st -> iwf (iset_flags st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_total : forall st v, 0 <= v < 2 ^ 64 -> iwf st -> iwf (iset_total st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

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

Lemma pulln_facts : forall c r k,
  Z.of_nat k <= ir_have r -> ir_have r < 2 ^ 32 -> 0 <= ir_bits r -> ir_bits r + 8 * Z.of_nat k <= 64 ->
  0 <= ir_hold r < 2 ^ ir_bits r ->
  (forall i, 0 <= i < Z.of_nat k -> 0 <= arr_get (ic_input c) (ir_next r + i) < 256) ->
  ir_next (pulln c r k) = ir_next r + Z.of_nat k /\ ir_have (pulln c r k) = ir_have r - Z.of_nat k
  /\ ir_put (pulln c r k) = ir_put r /\ ir_left (pulln c r k) = ir_left r
  /\ ir_hold (pulln c r k) = holdn c r k /\ ir_bits (pulln c r k) = ir_bits r + 8 * Z.of_nat k
  /\ ir_in (pulln c r k) = ir_in r /\ ir_out (pulln c r k) = ir_out r /\ ir_ret (pulln c r k) = ir_ret r
  /\ 0 <= holdn c r k < 2 ^ (ir_bits r + 8 * Z.of_nat k).
Proof.
  intros c r k. induction k as [|k IH]; intros Hk Hh32 Hb0 Hbk Hhold Hby.
  - cbn [pulln holdn Z.of_nat]. rewrite Z.mul_0_r, !Z.add_0_r, Z.sub_0_r. repeat split; try reflexivity; lia.
  - cbn [pulln holdn].
    destruct (IH ltac:(lia) Hh32 Hb0 ltac:(lia) Hhold ltac:(intros i Hi; apply Hby; lia)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
    assert (Hbyk : 0 <= arr_get (ic_input c) (ir_next (pulln c r k)) < 256) by (rewrite E1; apply Hby; lia).
    destruct (pullr_facts c (pulln c r k) ltac:(rewrite E2; lia) ltac:(rewrite E6; lia) ltac:(rewrite E5, E6; exact E10) Hbyk)
      as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    rewrite F1, F2, F3, F4, F5, F6, F7, F8, F9. rewrite F5 in F10.
    rewrite E1, E5, E6 in F10. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
    rewrite Nat2Z.inj_succ.
    replace (ir_bits r + 8 * Z.of_nat k + 8) with (ir_bits r + 8 * Z.succ (Z.of_nat k)) in F10 by lia.
    repeat split; try reflexivity; try lia.
Qed.

Lemma NEEDBITS_k_pull : forall f n s c r j,
  ir_bits (pulln c r j) < n -> ir_have (pulln c r j) <> 0 ->
  NEEDBITS_k (S f) n (mkW s c (pulln c r j)) = NEEDBITS_k f n (mkW s c (pulln c r (S j))).
Proof.
  intros f n s c r j Hb Hh. rewrite NEEDBITS_k_S.
  rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.eqb_neq _ _) Hh). reflexivity.
Qed.
Lemma NEEDBITS_k_dry : forall f n s c r j,
  ir_bits (pulln c r j) < n -> ir_have (pulln c r j) = 0 ->
  NEEDBITS_k (S f) n (mkW s c (pulln c r j)) = ALeave (mkW s c (pulln c r j)).
Proof.
  intros f n s c r j Hb Hh. rewrite NEEDBITS_k_S.
  rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.eqb_eq _ _) Hh). reflexivity.
Qed.
Lemma pulln_0 : forall c r, pulln c r 0 = r. Proof. reflexivity. Qed.

Lemma NEEDBITS_k_join : forall k f n s c r,
  (k <= f)%nat ->
  (forall i, (i < k)%nat -> ir_bits (pulln c r i) < n /\ ir_have (pulln c r i) <> 0) ->
  n <= ir_bits (pulln c r k) ->
  NEEDBITS_k f n (mkW s c r) = ARun tt (mkW s c (pulln c r k)).
Proof.
  intros k. induction k as [|k IH]; intros f n s c r Hf Hsteps Hdone.
  - cbn [pulln] in *. apply NEEDBITS_k_done. exact Hdone.
  - destruct f as [|f]; [lia|].
    destruct (Hsteps 0%nat ltac:(lia)) as [Hb0 Hh0].
    pose proof (NEEDBITS_k_pull f n s c r 0 Hb0 Hh0) as X. cbn [pulln] in X. rewrite X. clear X.
    rewrite (IH f n s c (pullr c r) ltac:(lia)).
    + f_equal. f_equal. clear. induction k as [|k IH]; [reflexivity|]. cbn [pulln]. rewrite IH. reflexivity.
    + intros i Hi. specialize (Hsteps (S i) ltac:(lia)).
      replace (pulln c (pullr c r) i) with (pulln c r (S i)); [exact Hsteps|].
      clear. induction i as [|i IH]; [reflexivity|]. cbn [pulln]. rewrite <- IH. reflexivity.
    + replace (pulln c (pullr c r) k) with (pulln c r (S k)); [exact Hdone|].
      clear. induction k as [|k IH]; [reflexivity|]. cbn [pulln]. rewrite <- IH. reflexivity.
Qed.

Lemma NEEDBITS_k_dryrun : forall j f n s c r,
  (j < f)%nat ->
  (forall i, (i < j)%nat -> ir_bits (pulln c r i) < n /\ ir_have (pulln c r i) <> 0) ->
  ir_bits (pulln c r j) < n -> ir_have (pulln c r j) = 0 ->
  NEEDBITS_k f n (mkW s c r) = ALeave (mkW s c (pulln c r j)).
Proof.
  intros j. induction j as [|j IH]; intros f n s c r Hf Hsteps Hb Hh.
  - destruct f as [|f]; [lia|]. exact (NEEDBITS_k_dry f n s c r 0 Hb Hh).
  - destruct f as [|f]; [lia|].
    destruct (Hsteps 0%nat ltac:(lia)) as [Hb0 Hh0].
    pose proof (NEEDBITS_k_pull f n s c r 0 Hb0 Hh0) as X. cbn [pulln] in X. rewrite X. clear X.
    assert (E : forall i, pulln c (pullr c r) i = pulln c r (S i)).
    { clear. intros i. induction i as [|i IH]; [reflexivity|]. cbn [pulln]. rewrite IH. reflexivity. }
    rewrite (IH f n s c (pullr c r) ltac:(lia)); [rewrite E; reflexivity | | rewrite E; exact Hb | rewrite E; exact Hh].
    intros i Hi. rewrite E. apply Hsteps. lia.
Qed.


Section ZSc.
Variable strm : Z.
Variable S : Z.
Variable fa : Z.
Variable ff : Z.
Hypothesis Hstrm : 0 <= strm /\ strm + 112 <= 2 ^ 63.
End ZSc.

Lemma icset_adler_facts : forall c a,
  ic_next_in (icset_adler c a) = ic_next_in c /\ ic_avail_in (icset_adler c a) = ic_avail_in c
  /\ ic_next_out (icset_adler c a) = ic_next_out c /\ ic_avail_out (icset_adler c a) = ic_avail_out c
  /\ ic_input (icset_adler c a) = ic_input c /\ ic_outbuf (icset_adler c a) = ic_outbuf c
  /\ zstrm_of_icall (icset_adler c a) = zs_set_adler a (zstrm_of_icall c)
  /\ ic_total_in (icset_adler c a) = ic_total_in c /\ ic_total_out (icset_adler c a) = ic_total_out c
  /\ ic_adler (icset_adler c a) = a /\ ic_data_type (icset_adler c a) = ic_data_type c.
Proof. intros c a. destruct c. repeat split; reflexivity. Qed.

Lemma iwf_set_holdbits' : forall st h b, 0 <= b < 64 -> 0 <= h < 2 ^ b -> iwf st -> iwf (iset_bits (iset_hold st h) b).
Proof.
  intros st h b Hb Hh H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.


Lemma testbit_255 : forall m, 0 <= m -> Z.testbit 255 m = (m <? 8).
Proof. intros m Hm. replace 255 with (Z.ones 8) by reflexivity. apply Z.testbit_ones_nonneg; lia. Qed.
Lemma testbit_65280 : forall m, 0 <= m -> Z.testbit 65280 m = ((8 <=? m) && (m <? 16))%bool.
Proof.
  intros m Hm. replace 65280 with (Z.shiftl (Z.ones 8) 8) by reflexivity. rewrite Z.shiftl_spec by lia.
  destruct (Z.leb_spec 8 m).
  - rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. destruct (Z.ltb_spec (m - 8) 8); destruct (Z.ltb_spec m 16); try reflexivity; lia.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.
Lemma testbit_16711680 : forall m, 0 <= m -> Z.testbit 16711680 m = ((16 <=? m) && (m <? 24))%bool.
Proof.
  intros m Hm. replace 16711680 with (Z.shiftl (Z.ones 8) 16) by reflexivity. rewrite Z.shiftl_spec by lia.
  destruct (Z.leb_spec 16 m).
  - rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. destruct (Z.ltb_spec (m - 16) 8); destruct (Z.ltb_spec m 24); try reflexivity; lia.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.
Definition zswap_m (h : Z) : Z :=
  Z.lor (h mod 2 ^ 32 / 2 ^ 24) (Z.land (h / 2 ^ 8) 65280) + (Z.land (h * 2 ^ 8) 16711680 + h mod 2 ^ 8 * 2 ^ 24).
Lemma comp_A : forall h, 0 <= h -> h mod 2 ^ 32 / 2 ^ 24 = Z.land (Z.shiftr h 24) 255.
Proof.
  intros h Hh. apply Z.bits_inj'. intros m Hm.
  rewrite Z.div_pow2_bits, Z.land_spec, testbit_255, Z.shiftr_spec by lia.
  destruct (Z.ltb_spec m 8).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Bool.andb_true_r. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma comp_C : forall h, 0 <= h -> Z.land (h * 2 ^ 8) 16711680 = Z.shiftl (Z.land h 65280) 8.
Proof.
  intros h Hh. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, testbit_16711680, Z.mul_pow2_bits, Z.shiftl_spec by lia.
  destruct (Z.leb_spec 8 m).
  - rewrite Z.land_spec, testbit_65280 by lia. destruct (Z.leb_spec 16 m); destruct (Z.ltb_spec m 24); destruct (Z.leb_spec 8 (m-8)); destruct (Z.ltb_spec (m-8) 16); cbn; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; try reflexivity; lia.
  - rewrite !Z.testbit_neg_r by lia. destruct (Z.leb_spec 16 m); [lia|]. reflexivity.
Qed.
Lemma comp_D : forall h, h mod 2 ^ 8 * 2 ^ 24 = Z.shiftl (Z.land h 255) 24.
Proof. intros h. rewrite Z.shiftl_mul_pow2 by lia. replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lor_AB : forall h, 0 <= h ->
  Z.lor (Z.land (Z.shiftr h 24) 255) (Z.land (h / 2 ^ 8) 65280) = Z.land (Z.shiftr h 24) 255 + Z.land (Z.shiftr h 8) 65280.
Proof.
  intros h Hh. rewrite <- (Z.shiftr_div_pow2 h 8) by lia.
  assert (Hz : Z.land (Z.land (Z.shiftr h 24) 255) (Z.land (Z.shiftr h 8) 65280) = 0).
  { apply Z.bits_inj_0. intros m. destruct (Z.leb_spec 0 m); [| rewrite Z.testbit_neg_r by lia; reflexivity].
    rewrite !Z.land_spec, testbit_255, testbit_65280 by lia.
    destruct (Z.ltb_spec m 8); destruct (Z.leb_spec 8 m); cbn; rewrite ?Bool.andb_false_r; try reflexivity; lia. }
  rewrite <- Z.lxor_lor by exact Hz. symmetry. apply Z.add_nocarry_lxor. exact Hz.
Qed.
Lemma small_of_bits : forall x n, 0 <= x -> 0 <= n -> (forall m, n <= m -> Z.testbit x m = false) -> x < 2 ^ n.
Proof.
  intros x n Hx Hn Hb. destruct (Z_lt_le_dec x (2 ^ n)) as [L|L]; [exact L|]. exfalso.
  assert (Hx1 : 0 < x) by (pose proof (Z.pow_pos_nonneg 2 n); lia).
  pose proof (Z.log2_le_mono _ _ L) as Hl. rewrite Z.log2_pow2 in Hl by lia.
  pose proof (Z.bit_log2 x Hx1) as Hb1. rewrite Hb in Hb1 by lia. discriminate.
Qed.
Lemma zswap_eq : forall h, 0 <= h -> zswap_m h = ZSWAP32 h.
Proof.
  intros h Hh. unfold zswap_m, ZSWAP32, wrap64.
  rewrite comp_A, comp_C, comp_D, lor_AB by lia.
  pose proof (Z.land_nonneg (Z.shiftr h 24) 255) as N1. pose proof (Z.land_nonneg (Z.shiftr h 8) 65280) as N2.
  pose proof (Z.land_nonneg h 65280) as N3. pose proof (Z.land_nonneg h 255) as N4.
  rewrite !Z.shiftr_nonneg in N1, N2.
  assert (B1 : Z.land (Z.shiftr h 24) 255 < 2 ^ 8).
  { apply small_of_bits; [lia | lia |]. intros m Hm. rewrite Z.land_spec, testbit_255 by lia. destruct (Z.ltb_spec m 8); [lia|]. apply Bool.andb_false_r. }
  assert (B2 : Z.land (Z.shiftr h 8) 65280 < 2 ^ 16).
  { apply small_of_bits; [lia | lia |]. intros m Hm. rewrite Z.land_spec, testbit_65280 by lia. destruct (Z.ltb_spec m 16); [lia|]. rewrite Bool.andb_false_r. apply Bool.andb_false_r. }
  assert (B3 : Z.shiftl (Z.land h 65280) 8 < 2 ^ 24).
  { apply small_of_bits; [rewrite Z.shiftl_nonneg; lia | lia |]. intros m Hm. rewrite Z.shiftl_spec, Z.land_spec, testbit_65280 by lia. destruct (Z.ltb_spec (m - 8) 16); [lia|]. rewrite Bool.andb_false_r. apply Bool.andb_false_r. }
  assert (B4 : Z.shiftl (Z.land h 255) 24 < 2 ^ 32).
  { apply small_of_bits; [rewrite Z.shiftl_nonneg; lia | lia |]. intros m Hm. rewrite Z.shiftl_spec, Z.land_spec, testbit_255 by lia. destruct (Z.ltb_spec (m - 24) 8); [lia|]. apply Bool.andb_false_r. }
  pose proof (Z.shiftl_nonneg (Z.land h 65280) 8) as N5. pose proof (Z.shiftl_nonneg (Z.land h 255) 24) as N6.
  replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
Qed.


Lemma RESTORE_eq : forall s c r,
  RESTORE (mkW s c r) = mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r))
                            (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) r.
Proof. reflexivity. Qed.

Lemma icset_cursors_facts : forall c nx hv pt lf,
  let c' := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c pt) lf) nx) hv in
  ic_next_in c' = nx /\ ic_avail_in c' = hv /\ ic_next_out c' = pt /\ ic_avail_out c' = lf
  /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c /\ zstrm_of_icall c' = zstrm_of_icall c
  /\ ic_total_in c' = ic_total_in c /\ ic_total_out c' = ic_total_out c /\ ic_adler c' = ic_adler c /\ ic_data_type c' = ic_data_type c.
Proof. intros. destruct c. repeat split; reflexivity. Qed.


Ltac t2_vac := let X := fresh in intros X; exfalso; revert X; clear; intros X; cbv in X;
  repeat (destruct X as [X|X]; [discriminate X|]); discriminate X.
Ltac t2_in := cbv; repeat (first [left; reflexivity | right]); reflexivity.
