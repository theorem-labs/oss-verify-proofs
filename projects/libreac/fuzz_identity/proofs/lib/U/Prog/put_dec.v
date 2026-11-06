From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require put_dec_c put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import put_dec_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec(
  ds_lsb, q_word, digit_word, a0_word, ltu9_word, upd_app_cons, le1_dg, ds_lsb_length, dec_ds).
Import ListNotations.
Open Scope Z_scope.

Local Ltac rng := rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.

Local Ltac ul :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by rng end.

Local Ltac bcond :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); bcond
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); bcond
  | _ => first [ apply Z.eqb_eq; rng | apply Z.eqb_neq; rng | apply Z.ltb_lt; rng | apply Z.ltb_ge; rng ]
  end.

Local Ltac br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [ cbv iota | symmetry; unfold_cond; ul; fold_lit_ux; bcond ]
  end.

Local Ltac wa_mem :=
  try match goal with |- context [write_to_mem ?mm (Z_to_bv 64 ?X) ?bs] =>
    change (write_to_mem mm (Z_to_bv 64 X) bs) with (write_to_mem mm (wa X) bs) end.

Lemma u8arr_appU : forall m A xs ys,
  u8arr rsegs m A (xs ++ ys) <-> u8arr rsegs m A xs /\ u8arr rsegs m (A + Z.of_nat (length xs)) ys.
Proof.
  intros m A xs ys. unfold u8arr. rewrite bytes_at_app, length_app. split.
  - intros [[H1 H2] (W1 & W2 & W3)]. pose proof (bytes_at_bound _ _ _ _ H2) as B2.
    split; split; try assumption.
    + split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. rewrite <- Z.add_assoc. apply W3. lia.
  - intros [[H1 (W1 & W2 & W3)] [H2 (V1 & V2 & V3)]]. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (length xs))) as [Hlt|Hge].
    + apply W3. lia.
    + replace (A + i) with (A + Z.of_nat (length xs) + (i - Z.of_nat (length xs))) by lia. apply V3. lia.
Qed.

Lemma bytes_at_read_allU : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia. cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma shr_shl32 : forall z, 0 <= z < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 32))) 32 = z.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2 ^ 32) with 4294967296 in *; lia).
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma bne_m1 : forall k, 0 <= k < 2^63 ->
  bv_eqb (Z_to_bv 64 (k + -1)) (Z_to_bv 64 18446744073709551615) = (k =? 0).
Proof.
  intros k Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec k 0) as [->|H0]; [reflexivity|].
  apply Z.eqb_neq. rewrite (Z.mod_small (k + -1)) by lia. rewrite (Z.mod_small 18446744073709551615) by lia. lia.
Qed.

Lemma dlU : forall f (ra sq gp tp w0 w1 w2 s0 s1 a0 a1 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xw w5 w6 w7 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (D i x : Z) (pre post : list byte),
  (1 <= f)%nat -> x < 10 ^ Z.of_nat f ->
  bv_unsigned xw mod 2^32 = x -> (bv_unsigned xw < 2^32 \/ 10 <= x) ->
  i = Z.of_nat (length pre) -> (length (ds_lsb f x) <= length post)%nat -> (length pre + length post = 10)%nat ->
  w0 = Z_to_bv 64 10 -> w1 = Z_to_bv 64 14757395259826634752 -> w2 = Z_to_bv 64 9 ->
  w5 = Z_to_bv 64 i -> w6 = Z_to_bv 64 (D + i) -> w7 = Z_to_bv 64 i ->
  u8arr rsegs m D (pre ++ post) -> mem_inv rsegs m ->
  (forall (m' : word -> option byte) (a2' t3' t4' y5 y6 y7 : word) (n : Z) (junk : list byte),
     n = i + Z.of_nat (length (ds_lsb f x)) ->
     y5 = Z_to_bv 64 n -> y6 = Z_to_bv 64 (D + n) -> y7 = Z_to_bv 64 n ->
     (length (ds_lsb f x) + length junk = length post)%nat ->
     munch [(D, D + 10)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     u8arr rsegs m' D (pre ++ ds_lsb f x ++ junk) ->
     evt rsegs Q (MS (mkR ra sq gp tp w0 w1 w2 s0 s1 a0 a1 a2' a3 a4 y5 y6 y7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6) F (Z_to_bv 64 0x141c8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp w0 w1 w2 s0 s1 a0 a1 xw a3 a4 w5 w6 w7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14194) fc None m (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros ra sq gp tp w0 w1 w2 s0 s1 a0 a1 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xw w5 w6 w7
      F fc m Q D i x pre post Hf Hx EX HX HI HLP HL10 E0 E1 E2 E5 E6 E7 HU HMI K; [lia|].
  pose proof (zr_word xw) as R. unfold inr64 in R.
  pose proof (Z.mod_pos_bound (bv_unsigned xw) (2^32) ltac:(lia)) as Hx32. rewrite EX in Hx32.
  assert (L1 : length (ds_lsb (S f) x) = S (length (if x <? 10 then [] else ds_lsb f (x / 10)))) by reflexivity.
  destruct post as [|y post']; [cbn in HLP; lia|].
  pose proof (u8arr_bound _ _ _ _ HU) as HB. rewrite length_app in HB.
  cbn [length] in HLP, HL10, HB.
  pose proof (u8arr_store_ok rsegs m D (pre ++ y :: post') i (wa (D + i)) HU
                ltac:(rewrite length_app; cbn [length]; lia) eq_refl) as HS.
  pose proof (ltu9_word xw x EX HX) as BR.
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
  subst w0 w1 w2 w5 w6 w7.
  step. br false.
  do 8 step.
  rewrite q_word, digit_word. rewrite EX.
  step.
  rewrite (le1_dg (x mod 10)) by lia. wa_mem.
  pose proof (u8arr_write rsegs m D (pre ++ y :: post') i (dg (x mod 10)) HU
                ltac:(rewrite length_app; cbn [length]; lia)) as HU1.
  replace (Z.to_nat i) with (length pre) in HU1 by lia. rewrite upd_app_cons in HU1.
  pose proof (mem_inv_store rsegs m (wa (D + i)) [dg (x mod 10)] HMI HS) as HMI1.
  pose proof (munch_write [(D, D + 10)] m m (D + i) [dg (x mod 10)] (munch_refl _ m)
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [inside length]; lia)) as MU1.
  pose proof (wmono_write rsegs m m (wa (D + i)) [dg (x mod 10)] (wmono_refl rsegs m)) as WM1.
  set (m1 := write_to_mem m (wa (D + i)) [dg (x mod 10)]) in *.
  step. step.
  rewrite a0_word by lia.
  step.
  destruct (Z.leb_spec 10 x) as [Hge|Hlt].
  - rewrite BR. cbv iota.
    rewrite (proj2 (Z.ltb_ge x 10) Hge) in L1.
    assert (Hf1 : (1 <= f)%nat).
    { destruct f; [|lia]. exfalso. change (10 ^ Z.of_nat 1) with 10 in Hx. lia. }
    assert (Hxf : x / 10 < 10 ^ Z.of_nat f).
    { apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. lia. }
    eapply IH with (x := x / 10) (pre := pre ++ [dg (x mod 10)]) (post := post') (i := i + 1) (D := D).
    + exact Hf1.
    + exact Hxf.
    + rewrite unsigned_lit by lia. apply Z.mod_small. lia.
    + left. rewrite unsigned_lit by lia. lia.
    + rewrite length_app. cbn [length]. lia.
    + lia.
    + rewrite length_app. cbn [length]. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal; lia.
    + reflexivity.
    + rewrite <- app_assoc. exact HU1.
    + exact HMI1.
    + intros m' a2' t3' t4' y5 y6 y7 n junk En E5 E6 E7 EJ MU' WM' MI' U'.
      apply K with (n := n) (junk := junk).
      * rewrite En, L1. lia.
      * exact E5.
      * exact E6.
      * exact E7.
      * rewrite L1. cbn [length]. lia.
      * exact (munch_trans _ _ _ _ MU1 MU').
      * exact (wmono_trans rsegs _ _ _ WM1 WM').
      * exact MI'.
      * rewrite <- app_assoc in U'. cbn [app] in U'.
        cbn [ds_lsb]. rewrite (proj2 (Z.ltb_ge x 10) Hge). exact U'.
  - rewrite BR. cbv iota.
    rewrite (proj2 (Z.ltb_lt x 10) Hlt) in L1.
    apply K with (n := i + 1) (junk := post').
    + rewrite L1. cbn [length]. lia.
    + reflexivity.
    + f_equal; lia.
    + reflexivity.
    + rewrite L1. cbn [length]. lia.
    + exact MU1.
    + exact WM1.
    + exact HMI1.
    + cbn [ds_lsb]. rewrite (proj2 (Z.ltb_lt x 10) Hlt). exact HU1.
Qed.

Lemma le1_48 : le1 (Z_to_bv 64 48) = [dg 0].
Proof. exact (le1_dg 0 ltac:(lia)). Qed.

Lemma plU : forall r (ra sq gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w2 w6 w7 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (D e : Z) (pre post : list byte),
  (1 <= r)%nat -> (r <= length post)%nat -> (length pre + length post = 10)%nat ->
  e = Z.of_nat (length pre) + Z.of_nat r -> D + 10 < 2^64 ->
  w2 = Z_to_bv 64 (D + e) -> w6 = Z_to_bv 64 (D + Z.of_nat (length pre)) -> w7 = Z_to_bv 64 48 ->
  u8arr rsegs m D (pre ++ post) -> mem_inv rsegs m ->
  (forall (m' : word -> option byte) (y6 : word) (junk : list byte),
     (r + length junk = length post)%nat ->
     munch [(D, D + 10)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     u8arr rsegs m' D (pre ++ repeat (dg 0) r ++ junk) ->
     evt rsegs Q (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 a0 a1 w2 a3 a4 a5 y6 w7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x141ec) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 a0 a1 w2 a3 a4 a5 w6 w7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x141e0) fc None m (seg_rom rsegs)).
Proof.
  induction r as [|r IH];
    intros ra sq gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w2 w6 w7
      F fc m Q D e pre post Hr HLP HL10 He HD E2 E6 E7 HU HMI K; [lia|].
  destruct post as [|y post']; [cbn in HLP; lia|].
  pose proof (u8arr_bound _ _ _ _ HU) as HB. rewrite length_app in HB.
  cbn [length] in HLP, HL10, HB.
  subst w2 w6 w7.
  remember (Z.of_nat (length pre)) as i eqn:Ei.
  pose proof (u8arr_store_ok rsegs m D (pre ++ y :: post') i (wa (D + i)) HU
                ltac:(rewrite length_app; cbn [length]; lia) eq_refl) as HS.
  step.
  rewrite le1_48. wa_mem.
  pose proof (u8arr_write rsegs m D (pre ++ y :: post') i (dg 0) HU
                ltac:(rewrite length_app; cbn [length]; lia)) as HU1.
  replace (Z.to_nat i) with (length pre) in HU1 by lia. rewrite upd_app_cons in HU1.
  pose proof (mem_inv_store rsegs m (wa (D + i)) [dg 0] HMI HS) as HMI1.
  pose proof (munch_write [(D, D + 10)] m m (D + i) [dg 0] (munch_refl _ m)
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [inside length]; lia)) as MU1.
  pose proof (wmono_write rsegs m m (wa (D + i)) [dg 0] (wmono_refl rsegs m)) as WM1.
  set (m1 := write_to_mem m (wa (D + i)) [dg 0]) in *.
  step. step.
  destruct r as [|r'].
  - br false.
    apply K with (junk := post').
    + cbn [length]. lia.
    + exact MU1.
    + exact WM1.
    + exact HMI1.
    + cbn [repeat app]. exact HU1.
  - br true.
    eapply IH with (pre := pre ++ [dg 0]) (post := post') (D := D) (e := e).
    + lia.
    + lia.
    + rewrite length_app. cbn [length]. lia.
    + rewrite length_app. cbn [length]. lia.
    + exact HD.
    + reflexivity.
    + rewrite length_app. cbn [length]. f_equal; lia.
    + reflexivity.
    + rewrite <- app_assoc. exact HU1.
    + exact HMI1.
    + intros m' y6 junk EJ MU' WM' MI' U'.
      apply K with (y6 := y6) (junk := junk).
      * cbn [length]. lia.
      * exact (munch_trans _ _ _ _ MU1 MU').
      * exact (wmono_trans rsegs _ _ _ WM1 WM').
      * exact MI'.
      * rewrite <- app_assoc in U'. cbn [app] in U'. cbn [repeat app]. exact U'.
Qed.

Lemma clU : forall (pre : list byte) (ra sq gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                     w0 w1 w2 w3 w4 w5 w6 w7 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (P D b N j E lo hi : Z) (done : list byte),
  pre <> [] ->
  j = Z.of_nat (length done) -> E = j + Z.of_nat (length pre) -> E <= 10 -> 0 <= b -> 0 <= N ->
  w0 = Z_to_bv 64 b -> w1 = Z_to_bv 64 P -> w2 = Z_to_bv 64 (18446744073709551615 - b) -> w3 = Z_to_bv 64 10 ->
  w4 = Z_to_bv 64 (18446744073709551615 - D) -> w5 = Z_to_bv 64 (Z.of_nat (length pre) - 1) ->
  w6 = Z_to_bv 64 D -> w7 = Z_to_bv 64 18446744073709551615 ->
  bytes_at rsegs m D pre ->
  bytes_at rsegs m P (le8 (Z_to_bv 64 (N + j))) -> wr_at rsegs m P 8 ->
  bytes_at rsegs m (b + N) done -> wr_at rsegs m (b + N) E ->
  (P + 8 <= b + N \/ b + N + E <= P) ->
  (P + 8 <= D \/ D + Z.of_nat (length pre) <= P) ->
  (b + N + E <= D \/ D + Z.of_nat (length pre) <= b + N) ->
  mem_inv rsegs m -> stk rsegs m lo hi ->
  (forall (m' : word -> option byte) (y0 y1 y2 y5 : word),
     munch [(P, P + 8); (b + N, b + N + E)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo hi ->
     bytes_at rsegs m' (b + N) (done ++ rev pre) -> bytes_at rsegs m' P (le8 (Z_to_bv 64 (N + E))) ->
     evt rsegs Q (MS (mkR ra sq gp tp y0 y1 y2 s0 s1 w0 w1 w2 w3 w4 y5 w6 w7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1423c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14208) fc None m (seg_rom rsegs)).
Proof.
  intros pre. induction pre as [|c pre IH] using rev_ind;
    intros ra sq gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 w6 w7 F fc m Q
      P D b N j E lo hi done Hne Hj HE HE10 Hb HN E0 E1 E2 E3 E4 E5 E6 E7 HPRE HBP HWP HBD HWD DJ1 DJ2 DJ3 HMI HST K;
    [congruence|].
  clear Hne.
  assert (LK : Z.of_nat (length (pre ++ [c])) = Z.of_nat (length pre) + 1) by (rewrite length_app; cbn [length]; lia).
  rewrite LK in HE, E5, DJ2, DJ3.
  replace (Z.of_nat (length pre) + 1 - 1) with (Z.of_nat (length pre)) in E5 by lia.
  pose proof (bytes_at_bound _ _ _ _ HPRE) as BPRE. rewrite LK in BPRE.
  pose proof (bytes_at_bound _ _ _ _ HBP) as BBP. rewrite length_le8 in BBP.
  pose proof (bytes_at_bound _ _ _ _ HBD) as BBD.
  pose proof HWD as (BWD1 & BWD2 & _).
  apply bytes_at_app in HPRE. destruct HPRE as [HPRE' HC].
  pose proof (bytes_at_read_allU _ _ _ HBP) as RP. rewrite length_le8 in RP.
  pose proof (bytes_at_read_allU _ _ _ HC) as RC. cbn [length] in RC.
  assert (HS1 : store_ok rsegs m (wa P) 8 = true).
  { rewrite <- (Z.add_0_r P) at 1. apply (wr_at_store_ok rsegs m P 8 0 8 HWP); lia. }
  subst w0 w1 w2 w3 w4 w5 w6 w7.
  step. step. br false.
  step. br false.
  do 4 step.
  step.
  wa_mem.
  pose proof (bytes_at_write_same rsegs m P (le8 (Z_to_bv 64 (N + j + 1))) ltac:(lia) ltac:(rewrite length_le8; lia)) as HBP1.
  pose proof (wr_at_write rsegs m P 8 (wa P) (le8 (Z_to_bv 64 (N + j + 1))) HWP) as HWP1.
  pose proof (wr_at_write rsegs m (b + N) E (wa P) (le8 (Z_to_bv 64 (N + j + 1))) HWD) as HWD1.
  pose proof (bytes_at_write_other rsegs m P (le8 (Z_to_bv 64 (N + j + 1))) (b + N) done HBD
                ltac:(lia) ltac:(rewrite length_le8; lia) ltac:(rewrite length_le8; lia)) as HBD1.
  pose proof (bytes_at_write_other rsegs m P (le8 (Z_to_bv 64 (N + j + 1))) D pre HPRE'
                ltac:(lia) ltac:(rewrite length_le8; lia) ltac:(rewrite length_le8; lia)) as HPRE1.
  pose proof (mem_inv_store rsegs m (wa P) (le8 (Z_to_bv 64 (N + j + 1))) HMI ltac:(rewrite length_le8; exact HS1)) as HMI1.
  pose proof (munch_write [(P, P + 8); (b + N, b + N + E)] m m P (le8 (Z_to_bv 64 (N + j + 1))) (munch_refl _ m)
                ltac:(lia) ltac:(rewrite length_le8; lia) ltac:(cbn [inside]; rewrite length_le8; lia)) as MU1.
  pose proof (wmono_write rsegs m m (wa P) (le8 (Z_to_bv 64 (N + j + 1))) (wmono_refl rsegs m)) as WM1.
  pose proof (stk_write rsegs m lo hi P (le8 (Z_to_bv 64 (N + j + 1))) HST ltac:(lia) ltac:(rewrite length_le8; lia)) as HST1.
  set (m1 := write_to_mem m (wa P) (le8 (Z_to_bv 64 (N + j + 1)))) in *.
  assert (HS2 : store_ok rsegs m1 (wa (b + N + j)) 1 = true) by (apply (wr_at_store_ok rsegs m1 (b + N) E j 1 HWD1); lia).
  step. br false.
  step. step.
  step.
  rewrite le1_zxb. wa_mem.
  pose proof (bytes_at_write_other rsegs m1 (b + N + j) [c] P (le8 (Z_to_bv 64 (N + j + 1))) HBP1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(rewrite length_le8; cbn [length]; lia)) as HBP2.
  pose proof (wr_at_write rsegs m1 P 8 (wa (b + N + j)) [c] HWP1) as HWP2.
  pose proof (wr_at_write rsegs m1 (b + N) E (wa (b + N + j)) [c] HWD1) as HWD2.
  pose proof (bytes_at_write_other rsegs m1 (b + N + j) [c] (b + N) done HBD1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as HBD2.
  pose proof (bytes_at_write_same rsegs m1 (b + N + j) [c] ltac:(lia) ltac:(cbn [length]; lia)) as HC2.
  pose proof (bytes_at_write_other rsegs m1 (b + N + j) [c] D pre HPRE1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as HPRE2.
  pose proof (mem_inv_store rsegs m1 (wa (b + N + j)) [c] HMI1 HS2) as HMI2.
  pose proof (munch_write [(P, P + 8); (b + N, b + N + E)] m m1 (b + N + j) [c] MU1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [inside length]; lia)) as MU2.
  pose proof (wmono_write rsegs m m1 (wa (b + N + j)) [c] WM1) as WM2.
  pose proof (stk_write rsegs m1 lo hi (b + N + j) [c] HST1 ltac:(lia) ltac:(cbn [length]; lia)) as HST2.
  set (m2 := write_to_mem m1 (wa (b + N + j)) [c]) in *.
  assert (HBD3 : bytes_at rsegs m2 (b + N) (done ++ [c])).
  { apply bytes_at_app. split; [exact HBD2|]. rewrite <- Hj. exact HC2. }
  clear HBD2 HC2.
  pose proof (bne_m1 (Z.of_nat (length pre)) ltac:(lia)) as BE.
  step.
  rewrite BE.
  destruct (Z.eqb_spec (Z.of_nat (length pre)) 0) as [H0|H0]; cbv iota beta delta [negb].
  - destruct pre as [|z pre'']; [|cbn [length] in H0; lia].
    apply K.
    + exact MU2.
    + exact WM2.
    + exact HMI2.
    + exact HST2.
    + cbn [rev app]. exact HBD3.
    + replace (N + E) with (N + j + 1) by (cbn [length] in HE; lia). exact HBP2.
  - eapply IH with (done := done ++ [c]) (j := j + 1) (E := E) (N := N) (b := b) (P := P) (D := D).
    + intros ->. cbn [length] in H0. lia.
    + rewrite length_app. cbn [length]. lia.
    + lia.
    + lia.
    + exact Hb.
    + exact HN.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal; lia.
    + reflexivity.
    + reflexivity.
    + exact HPRE2.
    + rewrite Z.add_assoc. exact HBP2.
    + exact HWP2.
    + exact HBD3.
    + exact HWD2.
    + lia.
    + lia.
    + lia.
    + exact HMI2.
    + exact HST2.
    + intros m' y0 y1 y2 y5 MU' WM' MI' ST' HB' HP'.
      apply K.
      * exact (munch_trans _ _ _ _ MU2 MU').
      * exact (wmono_trans rsegs _ _ _ WM2 WM').
      * exact MI'.
      * exact ST'.
      * rewrite rev_app_distr. cbn [rev app]. rewrite <- app_assoc in HB'. exact HB'.
      * exact HP'.
Qed.

Theorem put_dec_holds : put_dec_contract.
Proof.
  unfold put_dec_contract, PUT_DEC, PUT_DEC_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b p v mn N
    E0 HB0 E1 EV HV E3 HMN HP HPW HPA HW HMI ST LO DJ1 DJ2 DJ3.
  subst a0 a1 a3.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 8);
                (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
  pose proof (zr_word N) as RN. unfold inr64 in RN.
  pose proof (Z.mod_pos_bound (bv_unsigned a2) (2^32) ltac:(lia)) as Hv32. rewrite EV in Hv32.
  pose proof (bytes_at_bound _ _ _ _ HP) as BP. rewrite length_le8 in BP.
  pose proof HW as (BW1 & BW2 & _).
  pose proof ST as (SL0 & _ & _).
  pose proof (ds_lsb_length 10 v) as LDS.
  remember (length (ds_lsb 10 v)) as n eqn:En0.
  assert (Hn1 : (1 <= n)%nat) by (rewrite En0; cbn [ds_lsb length]; lia).
  assert (HE : dec_len v mn = Z.max mn (Z.of_nat n)).
  { unfold dec_len, DEC. rewrite length_app, repeat_length. rewrite dec_ds by lia. rewrite length_rev, <- En0. lia. }
  assert (HE1 : 1 <= dec_len v mn) by (rewrite HE; lia).
  carve_frame 10%nat ST. rename FR into FRD, junk into jD.
  assert (LJD : length jD = 10%nat) by (destruct FRD as [[W _] _]; exact (proj1 W)).
  pose proof (u8arr_of_rw_cells rsegs m (bv_unsigned sp + -10) 10 jD FRD) as UD. clear FRD.
  do 10 step.
  match goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  assert (TAIL : forall (mX : word -> option byte) (E : Z) (rest : list byte)
                   (t0x t1x t2x a2x a3x a4x a5x a6x a7x t3x t4x : word),
    E = Z.max mn (Z.of_nat n) ->
    a4x = Z_to_bv 64 (18446744073709551615 - (bv_unsigned sp + -10)) ->
    a5x = Z_to_bv 64 E ->
    u8arr rsegs mX (bv_unsigned sp + -10) (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (E - Z.of_nat n)) ++ rest) ->
    length (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (E - Z.of_nat n)) ++ rest) = 10%nat ->
    bytes_at rsegs mX p (le8 N) -> wr_at rsegs mX p 8 -> wr_at rsegs mX (b + bv_unsigned N) (dec_len v mn) ->
    munch [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 8);
           (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m mX ->
    wmono rsegs m mX -> mem_inv rsegs mX -> stk rsegs mX lo (bv_unsigned sp + -10) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0x t1x t2x s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 p)
                         a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5 t6)
                    F (Z_to_bv 64 0x141f4) fc None mX (seg_rom rsegs))).
  { intros mX E rest t0x t1x t2x a2x a3x a4x a5x a6x a7x t3x t4x HEE E4 E5 UX LX HPX HPWX HWX MUX WMX MIX STX.
    subst a4x a5x.
    assert (Eb : E = dec_len v mn) by (rewrite HE; exact HEE).
    pose proof STX as (SL1 & SL2 & _).
    do 5 step.
    set (pre := ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (E - Z.of_nat n))) in *.
    assert (LP : length pre = Z.to_nat E) by (unfold pre; rewrite length_app, repeat_length, <- En0; lia).
    assert (DE : DEC v mn = rev pre).
    { unfold pre, DEC. rewrite dec_ds by lia. rewrite rev_app_distr, rev_repeat, length_rev, <- En0.
      f_equal. f_equal. lia. }
    pose proof UX as UX0. rewrite app_assoc in UX0. fold pre in UX0.
    apply u8arr_appU in UX0. destruct UX0 as [UP _].
    eapply (clU pre) with (done := []) (j := 0) (E := E) (N := bv_unsigned N) (b := b) (P := p)
                          (D := bv_unsigned sp + -10) (lo := lo) (hi := bv_unsigned sp + -10).
    { intros E0'. apply (f_equal (@length byte)) in E0'. rewrite LP in E0'. cbn [length] in E0'. lia. }
    { reflexivity. }
    { lia. }
    { lia. }
    { exact HB0. }
    { lia. }
    { reflexivity. }
    { reflexivity. }
    { rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { f_equal; lia. }
    { reflexivity. }
    { apply Z_to_bv_eqm. reflexivity. }
    { exact (proj1 UP). }
    { rewrite Z.add_0_r, Z_to_bv_lit_self. exact HPX. }
    { exact HPWX. }
    { apply bytes_at_nil. lia. }
    { rewrite Eb. exact HWX. }
    { lia. }
    { lia. }
    { lia. }
    { exact MIX. }
    { exact STX. }
    intros mY y0 y1 y2 y5 MUY WMY MIY STY HBY HPY.
    clear UP.
    assert (UY : u8arr rsegs mY (bv_unsigned sp + -10)
                   (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (E - Z.of_nat n)) ++ rest)).
    { eapply u8arr_transport; [exact UX | exact MUY | exact WMY |]. rewrite LX. cbn [disjoint_from]. lia. }
    pose proof (rw_cells_of_u8arr rsegs mY _ _ UY) as FRDY. rewrite LX in FRDY.
    release_frame FRDY STY (bv_unsigned sp).
    step. step.
    apply evt_done. unfold Q. do 16 eexists.
    split; [reflexivity|].
    split.
    { eapply munch_trans; [exact MUX|]. eapply munch_weaken; [|exact MUY].
      unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _). rewrite Eb. tauto. }
    split; [exact (wmono_trans rsegs _ _ _ WMX WMY)|].
    split; [exact MIY|].
    split; [exact STY|].
    split.
    - rewrite DE. exact HBY.
    - rewrite <- Eb. exact HPY. }
  eapply (dlU 10%nat) with (D := bv_unsigned sp + -10) (i := 0) (x := v) (pre := []) (post := jD).
  { lia. }
  { change (10 ^ Z.of_nat 10) with 10000000000. change (2 ^ 32) with 4294967296 in Hv32. lia. }
  { exact EV. }
  { exact HV. }
  { reflexivity. }
  { rewrite LJD, <- En0. exact LDS. }
  { cbn [length]. lia. }
  { reflexivity. }
  { apply Z_to_bv_eqm. reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { f_equal; lia. }
  { reflexivity. }
  { cbn [app]. exact UD. }
  { exact HMI. }
  intros mB a2' t3' t4' y5 y6 y7 nz junk En E5 E6 E7 EJ MU1 WM1 MI1 U1.
  assert (Enz : nz = Z.of_nat n) by (rewrite En, <- En0; reflexivity). clear En. subst nz y5 y6 y7.
  transport_after_call rsegs m mB MU1 WM1.
  clear MU1 WM1 HMI. cbn [app] in U1.
  assert (A4 : forall a4x : word, a4x = Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -10))) 18446744073709551615) ->
                a4x = Z_to_bv 64 (18446744073709551615 - (bv_unsigned sp + -10))).
  { intros a4x ->. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. }
  assert (BL : bv_ltu (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 mn) = (Z.of_nat n <? mn)).
  { unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. }
  step.
  rewrite BL.
  destruct (Z.ltb_spec (Z.of_nat n) mn) as [Hlt|Hge]; cbv iota beta delta [negb].
  - do 5 step.
    eapply (plU (Z.to_nat (mn - Z.of_nat n))) with (D := bv_unsigned sp + -10) (e := mn) (pre := ds_lsb 10 v) (post := junk).
    { lia. }
    { lia. }
    { lia. }
    { rewrite <- En0. lia. }
    { lia. }
    { rewrite shr_shl32 by lia. reflexivity. }
    { rewrite <- En0. reflexivity. }
    { reflexivity. }
    { exact U1. }
    { exact MI1. }
    intros mC y6 junk2 EJ2 MU2 WM2 MI2 U2.
    transport_after_call rsegs mB mC MU2 WM2.
    clear MU2 WM2 MI1.
    step. br false.
    step.
    eapply TAIL with (E := mn) (rest := junk2).
    { lia. }
    { apply A4. reflexivity. }
    { reflexivity. }
    { exact U2. }
    { rewrite !length_app, repeat_length. lia. }
    { exact HP. }
    { exact HPW. }
    { exact HW. }
    { exact MU. }
    { exact WM. }
    { exact MI2. }
    { exact ST. }
  - step.
    destruct (Z.ltb_spec mn (Z.of_nat n)) as [Hlt2|Hge2].
    + br true.
      eapply TAIL with (E := Z.of_nat n) (rest := junk).
      { lia. }
      { apply A4. reflexivity. }
      { reflexivity. }
      { rewrite Z.sub_diag. cbn [Z.to_nat repeat app]. exact U1. }
      { rewrite !length_app, repeat_length. lia. }
      { exact HP. }
      { exact HPW. }
      { exact HW. }
      { exact MU. }
      { exact WM. }
      { exact MI1. }
      { exact ST. }
    + br false.
      step.
      eapply TAIL with (E := mn) (rest := junk).
      { lia. }
      { apply A4. reflexivity. }
      { reflexivity. }
      { replace (Z.to_nat (mn - Z.of_nat n)) with 0%nat by lia. cbn [repeat app]. exact U1. }
      { rewrite !length_app, repeat_length. lia. }
      { exact HP. }
      { exact HPW. }
      { exact HW. }
      { exact MU. }
      { exact WM. }
      { exact MI1. }
      { exact ST. }
Qed.
