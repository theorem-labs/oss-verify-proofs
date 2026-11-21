(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_lmatch_model Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz LmatchModel FillWinModel RefDeflFastM RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_LONGEST_MATCH : Z := 0x1a9d4.
Definition LM_LOOP : Z := 0x1ab00.
Definition LM_INNER : Z := 0x1ab88.
Definition LM_MIS : Z := 0x1ac80.
Definition LM_NEXT : Z := 0x1acec.
Definition LM_EXIT : Z := 0x1ad28.
Definition LM_RET : Z := 0x1ad30.
Definition LM_EXIT2 : Z := 0x1ad70.

(* [comment removed for export] *)
Lemma slti_ge_false : forall k c, 0 <= k < 2 ^ 63 -> c - 9223372036854775808 <= k -> (Z.lxor k 9223372036854775808 <? c) = false.
Proof.
  intros k c Hk Hc. change 9223372036854775808 with (2^63) at 1. rewrite zb_lxor_sign by lia.
  rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma sgn_add_guard : forall k k' p c, 0 <= k -> 0 <= p -> 0 <= k' < 2 ^ 63 -> c - 9223372036854775808 <= k' ->
  Z.lxor (Z.lxor (Z.b2z (k + p <? p)) (Z.b2z (Z.lxor k' 9223372036854775808 <? c))) 1 = 1.
Proof. intros k k' p c Hk Hp Hk' Hc. rewrite (proj2 (Z.ltb_ge (k + p) p)) by lia. rewrite slti_ge_false by lia. reflexivity. Qed.
Lemma sgn_add_guard' : forall k k' p c, 0 <= k -> 0 <= p -> 0 <= k' < 2 ^ 63 -> c - 9223372036854775808 <= k' ->
  Z.lxor (Z.lxor (Z.b2z (p + k <? p)) (Z.b2z (Z.lxor k' 9223372036854775808 <? c))) 1 = 1.
Proof. intros k k' p c Hk Hp Hk' Hc. rewrite (proj2 (Z.ltb_ge (p + k) p)) by lia. rewrite slti_ge_false by lia. reflexivity. Qed.
Ltac gS := first [rewrite sgn_add_guard by lia | rewrite sgn_add_guard' by lia]; gF.

(* [comment removed for export] *)
Lemma scan_flag : forall a, 0 < a -> Z.land (Z.b2z (0 <? a)) (Z.lxor (Z.b2z (a + 258 <? 258)) 1) = 1.
Proof. intros a Ha. rewrite (proj2 (Z.ltb_lt 0 a) Ha). rewrite (proj2 (Z.ltb_ge (a + 258) 258)) by lia. reflexivity. Qed.

Definition lm_post_gen (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (res lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DST m' L dF.

Section LM.
Variables (L : dlay) (d : deflate_state) (lo : Z).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis Hwb : forall i, 0 <= i < 65536 -> 0 <= arr_get (ds_window d) i < 256.
Hypothesis Hpb : forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_prev d) i < 65536.
Hypothesis Hss : 0 <= ds_strstart d /\ ds_strstart d + 258 < 65536.
Hypothesis Hla : 0 <= ds_lookahead d < 2^31.
Hypothesis HREST : forall m' ms, munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m' -> wmono usegs me m' ->
  dsA m' L (set_match_start d ms) -> DST m' L (set_match_start d ms).
Hypothesis LOsp : lo <= bv_unsigned sp + -112.
Hypothesis Bs : dl_As L + 5968 <= lo.
Hypothesis Rs : 0 < dl_As L.
Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.

(* [comment removed for export] *)
Definition lm_frame (j8 : list byte) : list cell :=
  [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma lm_ret : forall (msF res : Z) (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem)
    (j8 h1 h2 h3 h4 h5 : list byte),
  rw_cells usegs m (dl_As L) (dsA_cells L (set_match_start d msF) h1 h2 h3 h4 h5) ->
  rw_cells usegs m (bv_unsigned sp + -112) (lm_frame j8) ->
  stk usegs m lo (bv_unsigned sp + -112) ->
  munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m -> wmono usegs me m -> mem_inv usegs m ->
  0 <= res < 2^32 ->
  evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (set_match_start d msF) res lo me)
    (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (wz (dl_As L)) x11 (wz res) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz LM_RET) fc None m (seg_rom usegs)).
Proof.
  intros until h5. intros GA FR STK MU WM MI HR. unfold lm_frame in FR. unfold LM_RET.
  do 15 zs.
  release_frame FR STK (bv_unsigned sp).
  zs. apply evt_done. unfold lm_post_gen. do 14 eexists. exists m.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  apply HREST; [exact MU| exact WM|]. exists h1, h2, h3, h4, h5. exact GA.
Qed.

(* [comment removed for export] *)
Lemma lm_exit : forall (msF bF : Z) (x1 x5 x6 x7 x8 x9 x11 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem)
    (j8 h1 h2 h3 h4 h5 : list byte),
  rw_cells usegs m (dl_As L) (dsA_cells L (set_match_start d msF) h1 h2 h3 h4 h5) ->
  rw_cells usegs m (bv_unsigned sp + -112) (lm_frame j8) ->
  stk usegs m lo (bv_unsigned sp + -112) ->
  munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m -> wmono usegs me m -> mem_inv usegs m ->
  0 <= bF <= 258 ->
  evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (set_match_start d msF) (if bF <=? ds_lookahead d then bF else ds_lookahead d) lo me)
    (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (wz (dl_As L)) x11 (wz bF) x13 x14 (wz (ds_lookahead d)) x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz LM_EXIT) fc None m (seg_rom usegs)).
Proof.
  intros until h5. intros GA FR STK MU WM MI HB. unfold LM_EXIT.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - replace (if bF <=? ds_lookahead d then bF else ds_lookahead d) with bF by (destruct (Z.leb_spec bF (ds_lookahead d)); lia).
    eapply lm_ret; [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| lia].
  - zs. replace (if bF <=? ds_lookahead d then bF else ds_lookahead d) with (ds_lookahead d) by (destruct (Z.leb_spec bF (ds_lookahead d)); lia).
    eapply lm_ret; [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| lia].
Qed.

(* [comment removed for export] *)
Lemma lm_exit2 : forall (msF bF : Z) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem)
    (j8 h1 h2 h3 h4 h5 : list byte),
  rw_cells usegs m (dl_As L) (dsA_cells L (set_match_start d msF) h1 h2 h3 h4 h5) ->
  rw_cells usegs m (bv_unsigned sp + -112) (lm_frame j8) ->
  stk usegs m lo (bv_unsigned sp + -112) ->
  munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m -> wmono usegs me m -> mem_inv usegs m ->
  0 <= bF <= 258 ->
  evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (set_match_start d msF) (if bF <=? ds_lookahead d then bF else ds_lookahead d) lo me)
    (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (wz (dl_As L)) x11 x12 x13 x14 (wz (ds_lookahead d)) x16 x17 x18 x19 x20 (wz bF) x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz LM_EXIT2) fc None m (seg_rom usegs)).
Proof.
  intros until h5. intros GA FR STK MU WM MI HB. unfold LM_EXIT2.
  zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - zs. replace (if bF <=? ds_lookahead d then bF else ds_lookahead d) with (ds_lookahead d) by (destruct (Z.leb_spec bF (ds_lookahead d)); lia).
    eapply lm_ret; [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| lia].
  - zs. replace (if bF <=? ds_lookahead d then bF else ds_lookahead d) with bF by (destruct (Z.leb_spec bF (ds_lookahead d)); lia).
    eapply lm_ret; [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| lia].
Qed.

(* [comment removed for export] *)
Variables (nice limit : Z).
Definition lmR (x1 x11 x12 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : word) : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned sp + -112)) gp tp (wz (dl_Aw L + ds_strstart d + 258)) (wz (ds_w_mask d)) (wz (dl_Ap L)) (wz 1) (wz 250)
      (wz (dl_As L)) x11 x12 (wz (dl_Aw L)) (wz (dl_Aw L + ds_strstart d)) (wz (ds_lookahead d)) (wz nice) (wz limit)
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 (wz (18446744073709551615 - dl_Aw L)) (wz 18446744073709551615) (wz 18446744073709551613).

Hypothesis RAw : 0 < dl_Aw L /\ dl_Aw L + 65536 < 2^62.

(* [comment removed for export] *)
Ltac lm_cmp Gwin i cur k :=
  pose proof (Hwb (ds_strstart d + i + k) ltac:(lia)); pose proof (Hwb (cur + i + k) ltac:(lia));
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + i + k) ltac:(assumption);
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + i + k) ltac:(assumption).

(* [comment removed for export] *)
Ltac lm_mis HM cur ptr :=
  replace (wz ptr) with (wz (dl_Aw L + ds_strstart d + lm_len (ds_window d) (ds_strstart d) cur)) by (f_equal; lia);
  apply HM.

(* [comment removed for export] *)
Lemma lm_inner : forall (Q : machine_state -> Prop) (cur : Z) (x12 x19 x20 x28 : word) (m : mem),
  u8arr usegs m (dl_Aw L) (av8 (ds_window d) 65536) -> 0 <= cur < ds_strstart d ->
  (forall w1 w18 w21 w22 w23 w24 w25 w27,
     evt usegs Q (MS (lmR w1 (wz cur) x12 w18 x19 x20 w21 w22 w23 w24 w25 (wz (dl_Aw L + ds_strstart d + lm_len (ds_window d) (ds_strstart d) cur)) w27 x28)
                     F (wz LM_MIS) fc None m (seg_rom usegs))) ->
  forall (n : nat) (i : Z) (w1 w18 w23 w24 w25 w26 w27 : word), (1 <= n <= 32)%nat -> i = 8 * (32 - Z.of_nat n) ->
  lm_cmp_loop (S n) (ds_window d) (ds_strstart d + 2 + i) (cur + 2 + i) (ds_strstart d + 258) = lm_len (ds_window d) (ds_strstart d) cur + ds_strstart d ->
  evt usegs Q (MS (lmR w1 (wz cur) x12 w18 x19 x20 (wz (dl_Aw L + cur)) (wz i) w23 w24 w25 w26 w27 x28) F (wz LM_INNER) fc None m (seg_rom usegs)).
Proof.
  intros Q cur x12 x19 x20 x28 m Gwin Hcur HM.
  induction n as [|n IH]; intros i w1 w18 w23 w24 w25 w26 w27 Hn Hi RES; [lia|].
  pose proof (lm_len_bound (ds_window d) (ds_strstart d) cur) as LB.
  unfold lmR in *. unfold LM_INNER, LM_MIS in *.
  zstep. gF. zstep. zstep. gF. zstep. zstep. zstep.
  (* [comment removed for export] *)
  lm_cmp Gwin i cur 3. zs. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 3).
    { rewrite (cmp_round_mis _ _ _ _ _ 1%nat) in RES; [change (Z.of_nat 1) with 1 in RES; lia| lia| change (Z.of_nat 1) with 1; intros t Ht; lia|].
      change (Z.of_nat 1) with 1. replace (ds_strstart d + 2 + i + 1) with (ds_strstart d + i + 3) by lia. replace (cur + 2 + i + 1) with (cur + i + 3) by lia.
      first [exact K1| exact (not_eq_sym K1)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 3). }
  assert (E1 : arr_get (ds_window d) (ds_strstart d + 2 + i + 1) = arr_get (ds_window d) (cur + 2 + i + 1))
    by (replace (ds_strstart d + 2 + i + 1) with (ds_strstart d + i + 3) by lia; replace (cur + 2 + i + 1) with (cur + i + 3) by lia; first [exact K1| exact (eq_sym K1)]).
  (* [comment removed for export] *)
  gF. gF. zstep. zstep.
  lm_cmp Gwin i cur 4. zs. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 4).
    { rewrite (cmp_round_mis _ _ _ _ _ 2%nat) in RES; [change (Z.of_nat 2) with 2 in RES; lia| lia| change (Z.of_nat 2) with 2; intros t Ht; assert (C : t = 1) by lia; subst t; assumption|].
      change (Z.of_nat 2) with 2. replace (ds_strstart d + 2 + i + 2) with (ds_strstart d + i + 4) by lia. replace (cur + 2 + i + 2) with (cur + i + 4) by lia.
      first [exact K2| exact (not_eq_sym K2)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 4). }
  assert (E2 : arr_get (ds_window d) (ds_strstart d + 2 + i + 2) = arr_get (ds_window d) (cur + 2 + i + 2))
    by (replace (ds_strstart d + 2 + i + 2) with (ds_strstart d + i + 4) by lia; replace (cur + 2 + i + 2) with (cur + i + 4) by lia; first [exact K2| exact (eq_sym K2)]).
  (* [comment removed for export] *)
  gF. gF. zstep. zstep.
  lm_cmp Gwin i cur 5. zs. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 5).
    { rewrite (cmp_round_mis _ _ _ _ _ 3%nat) in RES; [change (Z.of_nat 3) with 3 in RES; lia| lia| change (Z.of_nat 3) with 3; intros t Ht; assert (C : t = 1 \/ t = 2) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 3) with 3. replace (ds_strstart d + 2 + i + 3) with (ds_strstart d + i + 5) by lia. replace (cur + 2 + i + 3) with (cur + i + 5) by lia.
      first [exact K3| exact (not_eq_sym K3)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 5). }
  assert (E3 : arr_get (ds_window d) (ds_strstart d + 2 + i + 3) = arr_get (ds_window d) (cur + 2 + i + 3))
    by (replace (ds_strstart d + 2 + i + 3) with (ds_strstart d + i + 5) by lia; replace (cur + 2 + i + 3) with (cur + i + 5) by lia; first [exact K3| exact (eq_sym K3)]).
  (* [comment removed for export] *)
  gF. gF. zstep. zstep.
  lm_cmp Gwin i cur 6. zs. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 6).
    { rewrite (cmp_round_mis _ _ _ _ _ 4%nat) in RES; [change (Z.of_nat 4) with 4 in RES; lia| lia| change (Z.of_nat 4) with 4; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 4) with 4. replace (ds_strstart d + 2 + i + 4) with (ds_strstart d + i + 6) by lia. replace (cur + 2 + i + 4) with (cur + i + 6) by lia.
      first [exact K4| exact (not_eq_sym K4)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 6). }
  assert (E4 : arr_get (ds_window d) (ds_strstart d + 2 + i + 4) = arr_get (ds_window d) (cur + 2 + i + 4))
    by (replace (ds_strstart d + 2 + i + 4) with (ds_strstart d + i + 6) by lia; replace (cur + 2 + i + 4) with (cur + i + 6) by lia; first [exact K4| exact (eq_sym K4)]).
  (* [comment removed for export] *)
  gF. gF. zstep. zstep.
  lm_cmp Gwin i cur 7. zs. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 7).
    { rewrite (cmp_round_mis _ _ _ _ _ 5%nat) in RES; [change (Z.of_nat 5) with 5 in RES; lia| lia| change (Z.of_nat 5) with 5; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 5) with 5. replace (ds_strstart d + 2 + i + 5) with (ds_strstart d + i + 7) by lia. replace (cur + 2 + i + 5) with (cur + i + 7) by lia.
      first [exact K5| exact (not_eq_sym K5)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 7). }
  assert (E5 : arr_get (ds_window d) (ds_strstart d + 2 + i + 5) = arr_get (ds_window d) (cur + 2 + i + 5))
    by (replace (ds_strstart d + 2 + i + 5) with (ds_strstart d + i + 7) by lia; replace (cur + 2 + i + 5) with (cur + i + 7) by lia; first [exact K5| exact (eq_sym K5)]).
  (* [comment removed for export] *)
  gF. gF. zstep. zstep.
  lm_cmp Gwin i cur 8. zs. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 8).
    { rewrite (cmp_round_mis _ _ _ _ _ 6%nat) in RES; [change (Z.of_nat 6) with 6 in RES; lia| lia| change (Z.of_nat 6) with 6; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 6) with 6. replace (ds_strstart d + 2 + i + 6) with (ds_strstart d + i + 8) by lia. replace (cur + 2 + i + 6) with (cur + i + 8) by lia.
      first [exact K6| exact (not_eq_sym K6)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 8). }
  assert (E6 : arr_get (ds_window d) (ds_strstart d + 2 + i + 6) = arr_get (ds_window d) (cur + 2 + i + 6))
    by (replace (ds_strstart d + 2 + i + 6) with (ds_strstart d + i + 8) by lia; replace (cur + 2 + i + 6) with (cur + i + 8) by lia; first [exact K6| exact (eq_sym K6)]).
  (* [comment removed for export] *)
  gF. gF. zstep. zstep.
  lm_cmp Gwin i cur 9. zs. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 9).
    { rewrite (cmp_round_mis _ _ _ _ _ 7%nat) in RES; [change (Z.of_nat 7) with 7 in RES; lia| lia| change (Z.of_nat 7) with 7; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 7) with 7. replace (ds_strstart d + 2 + i + 7) with (ds_strstart d + i + 9) by lia. replace (cur + 2 + i + 7) with (cur + i + 9) by lia.
      first [exact K7| exact (not_eq_sym K7)]. }
    lm_mis HM cur (dl_Aw L + ds_strstart d + i + 9). }
  assert (E7 : arr_get (ds_window d) (ds_strstart d + 2 + i + 7) = arr_get (ds_window d) (cur + 2 + i + 7))
    by (replace (ds_strstart d + 2 + i + 7) with (ds_strstart d + i + 9) by lia; replace (cur + 2 + i + 7) with (cur + i + 9) by lia; first [exact K7| exact (eq_sym K7)]).
  (* [comment removed for export] *)
  gF. gF.
  pose proof (Hwb (ds_strstart d + i + 10) ltac:(lia)). pose proof (Hwb (cur + i + 10) ltac:(lia)).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + i + 10) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + i + 10) ltac:(assumption).
  zstep. zs. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 10).
    { rewrite (cmp_round_mis _ _ _ _ _ 8%nat) in RES; [change (Z.of_nat 8) with 8 in RES; lia| lia| change (Z.of_nat 8) with 8; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 8) with 8. replace (ds_strstart d + 2 + i + 8) with (ds_strstart d + i + 10) by lia. replace (cur + 2 + i + 8) with (cur + i + 10) by lia.
      first [exact K8| exact (not_eq_sym K8)]. }
    zstep. zstep. lm_mis HM cur (dl_Aw L + ds_strstart d + (i + 8) + 2). }
  assert (E8 : arr_get (ds_window d) (ds_strstart d + 2 + i + 8) = arr_get (ds_window d) (cur + 2 + i + 8))
    by (replace (ds_strstart d + 2 + i + 8) with (ds_strstart d + i + 10) by lia; replace (cur + 2 + i + 8) with (cur + i + 10) by lia; first [exact K8| exact (eq_sym K8)]).
  rewrite cmp_round_all in RES
    by (intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption).
  zstep. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by lia.
  - (* [comment removed for export] *)
    replace (i + 10 <? 258) with true in RES by (symmetry; apply Z.ltb_lt; lia).
    apply (IH (i + 8)); [lia| lia| exact RES].
  - (* [comment removed for export] *)
    replace (i + 10 <? 258) with false in RES by (symmetry; apply Z.ltb_ge; lia).
    assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 10) by lia.
    zstep. zstep. lm_mis HM cur (dl_Aw L + ds_strstart d + (i + 8) + 2).
Qed.

Hypothesis Hnice : 0 <= nice <= 258.
Hypothesis Hlimit : 0 <= limit < 65536.
Hypothesis Hwm : ds_w_mask d = 32767.
Hypothesis LAY : dlay_ok L.
Hypothesis LW : Z.of_nat (length (av8 (ds_window d) 65536)) = 65536.
Hypothesis L16 : Z.of_nat (length (u16s (av16 (ds_prev d) 32768))) = 2 * 32768.
Hypothesis RAp : 0 < dl_Ap L /\ dl_Ap L + 65536 < 2^62 /\ dl_Ap L mod 16 = 0.

Lemma lm_loop : forall (f : nat) (msk cur chain best se1 se : Z) (v1 v18 v21 v22 v23 v24 v25 v26 v27 : word) (m : mem) (j8 h1 h2 h3 h4 h5 : list byte),
  rw_cells usegs m (dl_As L) (dsA_cells L (set_match_start d msk) h1 h2 h3 h4 h5) ->
  rw_cells usegs m (bv_unsigned sp + -112) (lm_frame j8) ->
  stk usegs m lo (bv_unsigned sp + -112) ->
  munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m -> wmono usegs me m -> mem_inv usegs m ->
  u8arr usegs m (dl_Aw L) (av8 (ds_window d) 65536) -> u8arr usegs m (dl_Ap L) (u16s (av16 (ds_prev d) 32768)) ->
  f = Z.to_nat chain -> 1 <= chain < 2^31 -> 1 <= best <= 258 -> 0 <= se1 < 256 -> 0 <= se < 256 ->
  Forall (fun c => 0 <= c < ds_strstart d) (lm_curs f (set_match_start d msk) cur chain best nice limit se1 se) ->
  evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L
               (fst (longest_match_loop f (set_match_start d msk) cur chain best nice limit se1 se))
               (if snd (longest_match_loop f (set_match_start d msk) cur chain best nice limit se1 se) <=? ds_lookahead d
                then snd (longest_match_loop f (set_match_start d msk) cur chain best nice limit se1 se) else ds_lookahead d) lo me)
    (MS (lmR v1 (wz cur) (wz best) v18 (wz se1) (wz se) v21 v22 v23 v24 v25 v26 v27 (wz chain)) F (wz LM_LOOP) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until h5; intros GA FR STK MU WM MI Gwin Gprev Hf Hchain Hbest Hse1 Hse VIS; [lia|].
  rewrite lm_loop_S. rewrite lm_curs_S in VIS. apply Forall_cons_iff in VIS. destruct VIS as [Hcur VIS].
  remember (lm_tripG (fun s' c ch b e1 e => longest_match_loop f s' c ch b nice limit e1 e) (fun s' b => (s', b))
                     (set_match_start d msk) cur chain best nice limit se1 se) as R eqn:ER.
  unfold lm_tripG in ER, VIS. cbv zeta in ER, VIS.
  change (ds_window (set_match_start d msk)) with (ds_window d) in *. change (ds_strstart (set_match_start d msk)) with (ds_strstart d) in *.
  change (ds_prev (set_match_start d msk)) with (ds_prev d) in *. change (ds_w_mask (set_match_start d msk)) with (ds_w_mask d) in *.
  change (set_match_start (set_match_start d msk) cur) with (set_match_start d cur) in *.
  unfold LM_LOOP, LM_NEXT, LM_MIS, LM_INNER in *.
  (* [comment removed for export] *)
  assert (HNEXT : forall (msk' best' se1' se' : Z) (w1 w18 w21 w22 w23 w24 w25 w26 w27 : word) (m' : mem) (k1 k2 k3 k4 k5 : list byte),
    rw_cells usegs m' (dl_As L) (dsA_cells L (set_match_start d msk') k1 k2 k3 k4 k5) ->
    rw_cells usegs m' (bv_unsigned sp + -112) (lm_frame j8) ->
    stk usegs m' lo (bv_unsigned sp + -112) ->
    munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m' -> wmono usegs me m' -> mem_inv usegs m' ->
    u8arr usegs m' (dl_Aw L) (av8 (ds_window d) 65536) -> u8arr usegs m' (dl_Ap L) (u16s (av16 (ds_prev d) 32768)) ->
    1 <= best' <= 258 -> 0 <= se1' < 256 -> 0 <= se' < 256 ->
    R = lm_restG (fun s' c ch b e1 e => longest_match_loop f s' c ch b nice limit e1 e) (fun s' b => (s', b))
                 (ds_prev d) (ds_w_mask d) limit (set_match_start d msk') cur chain best' se1' se' ->
    Forall (fun c => 0 <= c < ds_strstart d)
      (lm_restG (fun s' c ch b e1 e => lm_curs f s' c ch b nice limit e1 e) (fun _ _ => []) (ds_prev d) (ds_w_mask d) limit (set_match_start d msk') cur chain best' se1' se') ->
    evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR w1 (wz cur) (wz best') w18 (wz se1') (wz se') w21 w22 w23 w24 w25 w26 w27 (wz chain)) F (wz 0x1acec) fc None m' (seg_rom usegs))).
  { intros until k5. intros GA' FR' STK' MU' WM' MI' Gwin' Gprev' Hb' He1' He' ER' VIS'.
    unfold lmR.
    assert (RL : 0 <= Z.land cur (ds_w_mask d) < 32768).
    { rewrite Hwm. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    pose proof (Hpb (Z.land cur (ds_w_mask d)) RL) as RPV.
    assert (RWM : 0 <= ds_w_mask d < 2^31) by (rewrite Hwm; lia).
    zstep. zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. zstep.
    gF. zstep. zstep. zstep. gX. gF. zstep.
    assert (AL : (dl_Ap L + Z.land cur (ds_w_mask d) * 2) mod 2 = 0) by (clear - RAp RL; Z.div_mod_to_equations; lia).
    rewrite (land1_mod2 _ AL). gF.
    ld16 Gprev' (ds_prev d) 32768 (dl_Ap L) (Z.land cur (ds_w_mask d)) ltac:(assumption).
    unfold lm_restG in ER', VIS'. cbv zeta in ER', VIS'.
    zs. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by lia.
    - (* [comment removed for export] *)
      replace (limit <? arr_get (ds_prev d) (Z.land cur (ds_w_mask d))) with false in ER' by (symmetry; apply Z.ltb_ge; lia).
      rewrite ER'. cbn [fst snd].
      eapply lm_exit; [exact GA'| exact FR'| exact STK'| exact MU'| exact WM'| exact MI'| lia].
    - replace (limit <? arr_get (ds_prev d) (Z.land cur (ds_w_mask d))) with true in ER', VIS' by (symmetry; apply Z.ltb_lt; lia).
      rewrite wrap32_id in ER', VIS' by lia.
      zs. zs. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by lia.
      + (* [comment removed for export] *)
        replace (chain - 1 =? 0) with false in ER', VIS' by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in ER', VIS'.
        rewrite ER'. replace (wz (chain + -1)) with (wz (chain - 1)) by (f_equal; lia).
        eapply (IH msk' (arr_get (ds_prev d) (Z.land cur (ds_w_mask d))) (chain - 1) best' se1' se');
          [exact GA'| exact FR'| exact STK'| exact MU'| exact WM'| exact MI'| exact Gwin'| exact Gprev'| lia| lia| lia| lia| lia| exact VIS'].
      + replace (chain - 1 =? 0) with true in ER' by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in ER'.
        rewrite ER'. cbn [fst snd].
        eapply lm_exit; [exact GA'| exact FR'| exact STK'| exact MU'| exact WM'| exact MI'| lia]. }
  assert (LB := lm_len_bound (ds_window d) (ds_strstart d) cur).
  (* [comment removed for export] *)
  assert (HMIS : forall w1 w18 w21 w22 w23 w24 w25 w27 : word, lm_early (ds_window d) (ds_strstart d) cur best se1 se = false ->
    evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR w1 (wz cur) (wz best) w18 (wz se1) (wz se) w21 w22 w23 w24 w25 (wz (dl_Aw L + ds_strstart d + lm_len (ds_window d) (ds_strstart d) cur)) w27 (wz chain))
          F (wz 0x1ac80) fc None m (seg_rom usegs))).
  { intros w1 w18 w21 w22 w23 w24 w25 w27 HEARLY. unfold lmR. unfold dsA_cells in GA.
    rewrite HEARLY in ER, VIS.
    remember (lm_len (ds_window d) (ds_strstart d) cur) as len eqn:Elen.
    zs. zstep. zs. zstep.
    replace (wz (258 - (dl_Aw L + ds_strstart d + 258 - (dl_Aw L + ds_strstart d + len)))) with (wz len) by (f_equal; lia).
    gF. gF.
    zs. if_cases KB; zify_cond KB; rewrite ?signed_wz in KB by lia.
    - (* [comment removed for export] *)
      replace (best <? len) with false in ER, VIS by (symmetry; apply Z.ltb_ge; lia).
      eapply (HNEXT msk best se1 se); [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| exact Gwin| exact Gprev| lia| lia| lia| exact ER| exact VIS].
    - replace (best <? len) with true in ER, VIS by (symmetry; apply Z.ltb_lt; lia).
      zs. (* [comment removed for export] *)
      zs. if_cases KN; zify_cond KN; rewrite ?signed_wz in KN by lia.
      + (* [comment removed for export] *)
        replace (nice <=? len) with true in ER by (symmetry; apply Z.leb_le; lia).
        rewrite ER. cbn [fst snd].
        eapply (lm_exit2 cur len); [exact GA| exact FR| exact STK| exact MU| exact WM| eassumption| lia].
      + replace (nice <=? len) with false in ER, VIS by (symmetry; apply Z.leb_gt; lia).
        pose proof (Hwb (ds_strstart d + len - 1) ltac:(lia)). pose proof (Hwb (ds_strstart d + len) ltac:(lia)).
        zstep. zstep. gF. zstep. zstep. zstep. zstep. gS.
        zstep. gF. zstep. zstep. zstep. zstep. gS.
        ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + len - 1) ltac:(assumption).
        ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + len) ltac:(assumption).
        zstep.
        eapply (HNEXT cur len (arr_get (ds_window d) (ds_strstart d + len - 1)) (arr_get (ds_window d) (ds_strstart d + len)));
          [exact GA| exact FR| exact STK| exact MU| exact WM| eassumption| exact Gwin| exact Gprev| lia| lia| lia| exact ER| exact VIS]. }
  (* [comment removed for export] *)
  assert (HREJ : forall w1 w18 w21 w22 w23 w24 w25 w26 w27 : word, lm_early (ds_window d) (ds_strstart d) cur best se1 se = true ->
    evt usegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR w1 (wz cur) (wz best) w18 (wz se1) (wz se) w21 w22 w23 w24 w25 w26 w27 (wz chain)) F (wz 0x1acec) fc None m (seg_rom usegs))).
  { intros w1 w18 w21 w22 w23 w24 w25 w26 w27 HE. rewrite HE in ER, VIS.
    eapply (HNEXT msk best se1 se); [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| exact Gwin| exact Gprev| lia| lia| lia| exact ER| exact VIS]. }
  clear HNEXT IH.
  pose proof (Hwb (cur + best) ltac:(lia)). pose proof (Hwb (cur + best - 1) ltac:(lia)).
  pose proof (Hwb (ds_strstart d) ltac:(lia)). pose proof (Hwb cur ltac:(lia)).
  pose proof (Hwb (ds_strstart d + 1) ltac:(lia)). pose proof (Hwb (cur + 1) ltac:(lia)).
  unfold lmR.
  gF. zstep. zstep. gF. zstep. zstep. zstep. zstep. gS.
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + best) ltac:(assumption).
  zs. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) (cur + best) =? se) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  zs. gF. zstep. gF. zstep. zstep. zstep. zstep. gS.
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + best - 1) ltac:(assumption).
  zs. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) (cur + best - 1) =? se1) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite orb_true_r. reflexivity. }
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) cur ltac:(assumption).
  zs. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) cur =? arr_get (ds_window d) (ds_strstart d)) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite orb_true_r. reflexivity. }
  gF. gF. zstep.
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + 1) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + 1) ltac:(assumption).
  zs. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) (cur + 1) =? arr_get (ds_window d) (ds_strstart d + 1)) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite orb_true_r. reflexivity. }
  assert (HE : lm_early (ds_window d) (ds_strstart d) cur best se1 se = false).
  { unfold lm_early. rewrite !(proj2 (Z.eqb_eq _ _)) by lia. reflexivity. }
  gF. gF. zstep.
  replace (wz 0) with (wz (8 * (32 - Z.of_nat 32))) by reflexivity.
  eapply (lm_inner _ cur (wz best) (wz se1) (wz se) (wz chain) m Gwin ltac:(lia)) with (n := 32%nat) (i := 8 * (32 - Z.of_nat 32)).
  - intros. eapply HMIS. exact HE.
  - lia.
  - reflexivity.
  - change (8 * (32 - Z.of_nat 32)) with 0. rewrite !Z.add_0_r. unfold lm_len. lia.
Qed.
End LM.

Definition lm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (cur lo : Z) (m : mem) : machine_state -> Prop :=
  lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst (longest_match d cur)) (snd (longest_match d cur)) lo m.

Lemma longest_match_spec : forall (L : dlay) (d : deflate_state) (cur lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L d -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> dlay_below L lo (bv_unsigned sp) ->
  lm_ok d cur -> ds_w_size d = 32768 ->
  a0 = wz (dl_As L) -> a1 = wz cur ->
  evt usegs (lm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d cur lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_LONGEST_MATCH) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI STK LO BEL LMOK WS -> ->. unfold Z_LONGEST_MATCH.
  destruct LMOK as (Hwb & Hpb & Hs0 & Hs258 & Hwm & Hpl & Hnice & Hlook & Hgood & Hmc & Hch & Hcur & Hvis & Hres).
  rewrite WS in Hwb, Hpb, Hs258, Hwm.
  assert (HREST : forall m' ms, munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] m m' -> wmono usegs m m' ->
            dsA m' L (set_match_start d ms) -> DST m' L (set_match_start d ms)).
  { intros m' ms MUx WMx GAx. pose proof (st_lay _ _ _ _ ST) as LAYx. below_open BEL. lay_open LAYx. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
    clear GA. tr_groups MUx WMx.
    constructor; [exact GAx| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
  open_DST ST. open_A GA. open_win Gwin. open_u16 Gprev. lay_open LAY. below_open BEL.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs. pose proof (lo_p _ LAY) as BKp. unfold blk_ok in BKp.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RWS : 0 <= ds_w_size d < 2^31) by lia.
  (* [comment removed for export] *)
  carve_frame 112%nat STK.
  do 14 zs.
  zstep. al8 (dl_As L). gF.
  zs. zs. zstep. gF. zstep. zstep. zstep. gX. gF. zstep. gN.
  zs. zs. gF.
  pose proof (Hwb (ds_strstart d + ds_prev_length d - 1) ltac:(lia)). pose proof (Hwb (ds_strstart d + ds_prev_length d) ltac:(lia)).
  zstep. gF. zstep. zstep. zstep. zstep. gS.
  zstep. gF. zstep. zstep. zstep. zstep. gS.
  (* [comment removed for export] *)
  zs. zs. zs. zs. zs.
  zs. zs. zs. zs. zs. zs. rewrite limit_mask by lia.
  zstep. zstep. zstep. zstep.
  replace (Z.lxor (Z.b2z (ds_prev_length d <? ds_good_match d)) 1 ≪ 1) with (if ds_good_match d <=? ds_prev_length d then 2 else 0)
    by (destruct (Z.ltb_spec (ds_prev_length d) (ds_good_match d)); destruct (Z.leb_spec (ds_good_match d) (ds_prev_length d)); try lia; reflexivity).
  zstep. eapply (evt_cut usegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (wz (ds_nice_match d)) with (wz (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d))
        by (f_equal; destruct (Z.ltb_spec (ds_lookahead d) (ds_nice_match d)); lia).
      apply evt_done. reflexivity.
    - zs. apply evt_done. repeat f_equal. destruct (Z.ltb_spec (ds_lookahead d) (ds_nice_match d)); lia. }
  intros ms' ->.
  zs. zs.
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + ds_prev_length d - 1) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + ds_prev_length d) ltac:(assumption).
  zs.
  set (chain0 := if ds_good_match d <=? ds_prev_length d then ds_max_chain_length d ≫ 2 else ds_max_chain_length d) in *.
  replace (wz (bv_swrap 32 (bv_wrap 32 (ds_max_chain_length d) ≫ ((if ds_good_match d <=? ds_prev_length d then 2 else 0) mod 32)))) with (wz chain0).
  2:{ f_equal. subst chain0. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2 ^ 32) with 4294967296. rewrite (Z.mod_small (ds_max_chain_length d)) by lia.
      assert (SH : 0 <= ds_max_chain_length d ≫ 2 <= ds_max_chain_length d).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]. }
      destruct (ds_good_match d <=? ds_prev_length d).
      - change (2 mod 32) with 2. rewrite bv_swrap32_id by lia. reflexivity.
      - change (0 mod 32) with 0. rewrite Z.shiftr_0_r, bv_swrap32_id by lia. reflexivity. }
  assert (RCH : 1 <= chain0 < 2^31).
  { subst chain0. split; [exact Hch|]. destruct (ds_good_match d <=? ds_prev_length d); [|lia].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply Z.div_lt_upper_bound; lia. }
  (* [comment removed for export] *)
  zstep. rewrite (zb_lxor_ones (dl_Aw L)) by lia.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite scan_flag by lia.
  replace (wz (-1)) with (wz 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
  replace (wz (-3)) with (wz 18446744073709551613) by (apply Z_to_bv_eqm; reflexivity).
  assert (VIS0 : Forall (fun c => 0 <= c < ds_strstart d)
            (lm_curs (Z.to_nat chain0) (set_match_start d (ds_match_start d)) cur chain0 (ds_prev_length d)
               (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d)
               (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0)
               (arr_get (ds_window d) (ds_strstart d + ds_prev_length d - 1)) (arr_get (ds_window d) (ds_strstart d + ds_prev_length d)))).
  { rewrite set_ms_self. exact Hvis. }
  assert (EQ : longest_match d cur =
               (let r := longest_match_loop (Z.to_nat chain0) (set_match_start d (ds_match_start d)) cur chain0 (ds_prev_length d)
                           (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d)
                           (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0)
                           (arr_get (ds_window d) (ds_strstart d + ds_prev_length d - 1)) (arr_get (ds_window d) (ds_strstart d + ds_prev_length d)) in
                (fst r, if snd r <=? ds_lookahead d then snd r else ds_lookahead d))).
  { rewrite set_ms_self. unfold longest_match, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH, NIL. cbv zeta. fold chain0.
    replace (ds_w_size d - (258 + 3 + 1)) with (ds_w_size d - 262) by lia.
    match goal with |- context [longest_match_loop ?f ?s ?c ?ch ?b ?n ?l ?e1 ?e] =>
      destruct (longest_match_loop_ms f s c ch b n l e1 e) as [msF EF]; destruct (longest_match_loop f s c ch b n l e1 e) as [sF bF] end.
    cbn [fst snd] in *. subst sF. change (ds_lookahead (set_match_start d msF)) with (ds_lookahead d).
    destruct (bF <=? ds_lookahead d); reflexivity. }
  clearbody chain0.
  unfold lm_post. rewrite EQ. cbv zeta. cbn [fst snd].
  assert (T1 : ds_w_mask d = 32767) by lia.
  assert (T2 : 0 < dl_Ap L /\ dl_Ap L + 65536 < 2^62 /\ dl_Ap L mod 16 = 0) by lia.
  assert (T3 : 0 < dl_Aw L /\ dl_Aw L + 65536 < 2^62) by lia.
  assert (T4 : 0 <= (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d) <= 258) by (destruct (Z.ltb_spec (ds_lookahead d) (ds_nice_match d)); lia).
  assert (T5 : 0 <= (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0) < 65536) by (destruct (Z.ltb_spec (ds_w_size d - 262) (ds_strstart d)); lia).
  assert (T6 : 0 <= ds_strstart d /\ ds_strstart d + 258 < 65536) by lia.
  assert (T7 : lo <= bv_unsigned sp + -112) by lia.
  assert (T8 : dl_As L + 5968 <= lo) by lia.
  assert (T9 : 0 < dl_As L) by lia.
  eapply (lm_loop L d lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Hwb Hpb T6 Hlook HREST T7 T8 T9 RSP
            (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d)
            (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0)
            T3 T4 T5 T1 LAY LW L16 T2
            (Z.to_nat chain0) (ds_match_start d) cur chain0 (ds_prev_length d)
            (arr_get (ds_window d) (ds_strstart d + ds_prev_length d - 1)) (arr_get (ds_window d) (ds_strstart d + ds_prev_length d)));
    [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| exact Gwin| exact Gprev| reflexivity| lia| lia| lia| lia| exact VIS0].
Qed.
