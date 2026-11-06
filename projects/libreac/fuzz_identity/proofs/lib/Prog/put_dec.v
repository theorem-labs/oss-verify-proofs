From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec memset_c put_dec_c.
Import ListNotations.
Open Scope Z_scope.

Fixpoint ds_lsb (f : nat) (x : Z) : list byte :=
  match f with
  | O => []
  | S f' => dg (x mod 10) :: (if x <? 10 then [] else ds_lsb f' (x / 10))
  end.

Lemma div10_magic : forall x, 0 <= x < 4294967296 -> (x * 3435973837) / 34359738368 = x / 10.
Proof.
  intros x Hx.
  assert (E : x = 10 * (x / 10) + x mod 10) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
  assert (Hq : 0 <= x / 10 < 429496730) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (q := x / 10) in *. set (r := x mod 10) in *.
  rewrite E. replace ((10 * q + r) * 3435973837) with (q * 34359738368 + (2 * q + r * 3435973837)) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (2 * q + r * 3435973837)) by lia. lia.
Qed.

Lemma q_word : forall xw : word,
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned xw) 32)) * 14757395259826634752) 64))) 35)
  = Z_to_bv 64 ((bv_unsigned xw mod 2^32) / 10).
Proof.
  intros xw. pose proof (zr_word xw) as R. unfold inr64 in R.
  set (u := bv_unsigned xw) in *.
  rewrite !unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 64) with (4294967296 * 4294967296). change (2 ^ 32) with 4294967296.
  change (2 ^ 35) with 34359738368.
  rewrite Z.mul_mod_distr_r by lia.
  pose proof (Z.mod_pos_bound u 4294967296 ltac:(lia)) as Hx.
  set (x := u mod 4294967296) in *.
  replace (x * 4294967296 * 14757395259826634752) with ((x * 3435973837) * (4294967296 * 4294967296)) by lia.
  rewrite Z.div_mul by lia. rewrite Z.mod_small by nia.
  rewrite div10_magic by lia. reflexivity.
Qed.

Lemma digit_word : forall xw : word,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned xw - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ((bv_unsigned xw mod 2^32) / 10)) * 10)))))) 48)
  = Z_to_bv 64 (48 + (bv_unsigned xw mod 2^32) mod 10).
Proof.
  intros xw. pose proof (zr_word xw) as R. unfold inr64 in R.
  set (u := bv_unsigned xw) in *. change (2 ^ 32) with 4294967296.
  pose proof (Z.mod_pos_bound u 4294967296 ltac:(lia)) as Hx.
  set (x := u mod 4294967296) in *.
  assert (Hq : 0 <= x / 10 < 429496730) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite (unsigned_lit (x / 10)) by lia. rewrite (unsigned_lit (x / 10 * 10)) by lia.
  assert (Hu : u = x + 4294967296 * (u / 4294967296)) by (unfold x; pose proof (Z.div_mod u 4294967296); lia).
  assert (Hx10 : x = 10 * (x / 10) + x mod 10) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
  assert (S : bv_swrap 32 (u - x / 10 * 10) = x mod 10).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 `div` 2) with 2147483648.
    replace (u - x / 10 * 10 + 2147483648) with ((x mod 10 + 2147483648) + (u / 4294967296) * 4294967296) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite S. rewrite (unsigned_lit (x mod 10)) by lia. f_equal.
  clear S Hx10. set (r := x mod 10) in *. clearbody r.
  assert (C : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) by lia.
  repeat destruct C as [C|C]; rewrite C; reflexivity.
Qed.

Lemma a7_word : forall D i, 0 <= i < 4294967296 ->
  Z_to_bv 64 (D + Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 32))) 32) = Z_to_bv 64 (D + i).
Proof.
  intros D i Hi. rewrite (unsigned_lit i) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma a0_word : forall i, 0 <= i < 100 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1)) = Z_to_bv 64 (i + 1).
Proof.
  intros i Hi. rewrite (unsigned_lit i) by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ltu9_word : forall (xw : word) x, bv_unsigned xw mod 2^32 = x -> (bv_unsigned xw < 2^32 \/ 10 <= x) ->
  bv_ltu (Z_to_bv 64 9) xw = (10 <=? x).
Proof.
  intros xw x EX HX. pose proof (zr_word xw) as R. unfold inr64 in R.
  unfold bv_ltu. rewrite (unsigned_lit 9) by lia.
  change (2 ^ 32) with 4294967296 in *.
  pose proof (Z.mod_pos_bound (bv_unsigned xw) 4294967296 ltac:(lia)) as Hx.
  destruct (Z.leb_spec 10 x) as [H|H].
  - apply Z.ltb_lt. pose proof (Z.mod_le (bv_unsigned xw) 4294967296 ltac:(lia) ltac:(lia)). lia.
  - apply Z.ltb_ge. destruct HX as [HX|HX]; [|lia]. rewrite Z.mod_small in EX by lia. lia.
Qed.

Lemma upd_app_cons : forall (pre post : list byte) y b, upd (pre ++ y :: post) (length pre) b = pre ++ b :: post.
Proof. induction pre as [|z pre IH]; intros post y b; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma le1_dg : forall r, 0 <= r < 10 -> le1 (Z_to_bv 64 (48 + r)) = [dg r].
Proof. intros r Hr. unfold le1, dg. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma dloop : forall f (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xw : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (D i x : Z) (pre post : list byte),
  (1 <= f)%nat -> x < 10 ^ Z.of_nat f ->
  bv_unsigned xw mod 2^32 = x -> (bv_unsigned xw < 2^32 \/ 10 <= x) ->
  i = Z.of_nat (length pre) -> (length (ds_lsb f x) <= length post)%nat -> (length pre + length post = 10)%nat ->
  u8arr rsegs m D (pre ++ post) -> mem_inv rsegs m ->
  (forall (m' : word -> option byte) (t0' a2' a6' a7' : word) (n : Z) (junk : list byte),
     n = i + Z.of_nat (length (ds_lsb f x)) ->
     (length (ds_lsb f x) + length junk = length post)%nat ->
     munch [(D, D + 10)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     u8arr rsegs m' D (pre ++ ds_lsb f x ++ junk) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 10) a2' (Z_to_bv 64 D)
                         (Z_to_bv 64 14757395259826634752) (Z_to_bv 64 9) a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13e78) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 10) xw (Z_to_bv 64 D)
                      (Z_to_bv 64 14757395259826634752) (Z_to_bv 64 9) a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13e44) fc None m (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xw F fc m Q D i x pre post
      Hf Hx EX HX HI HLP HL10 HU HMI K; [lia|].
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
  do 11 step.
  rewrite q_word, digit_word, a7_word, a0_word by lia.
  rewrite EX.
  step.
  rewrite (le1_dg (x mod 10)) by lia. change (Z_to_bv 64 (D + i)) with (wa (D + i)).
  pose proof (u8arr_write rsegs m D (pre ++ y :: post') i (dg (x mod 10)) HU
                ltac:(rewrite length_app; cbn [length]; lia)) as HU1.
  replace (Z.to_nat i) with (length pre) in HU1 by lia. rewrite upd_app_cons in HU1.
  pose proof (mem_inv_store rsegs m (wa (D + i)) [dg (x mod 10)] HMI HS) as HMI1.
  pose proof (munch_write [(D, D + 10)] m m (D + i) [dg (x mod 10)] (munch_refl _ m)
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [inside length]; lia)) as MU1.
  pose proof (wmono_write rsegs m m (wa (D + i)) [dg (x mod 10)] (wmono_refl rsegs m)) as WM1.
  set (m1 := write_to_mem m (wa (D + i)) [dg (x mod 10)]) in *.
  step.
  destruct (Z.leb_spec 10 x) as [Hge|Hlt].
  - rewrite BR. cbv iota.
    rewrite (proj2 (Z.ltb_ge x 10) Hge) in L1.
    assert (Hf1 : (1 <= f)%nat).
    { destruct f; [|lia]. exfalso. change (10 ^ Z.of_nat 1) with 10 in Hx. lia. }
    assert (Hxf : x / 10 < 10 ^ Z.of_nat f).
    { apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. lia. }
    eapply IH with (x := x / 10) (pre := pre ++ [dg (x mod 10)]) (post := post').
    + exact Hf1.
    + exact Hxf.
    + rewrite unsigned_lit by lia. apply Z.mod_small. lia.
    + left. rewrite unsigned_lit by lia. lia.
    + rewrite length_app. cbn [length]. lia.
    + lia.
    + rewrite length_app. cbn [length]. lia.
    + rewrite <- app_assoc. exact HU1.
    + exact HMI1.
    + intros m' t0' a2' a6' a7' n junk En EJ MU' WM' MI' U'.
      apply K with (t0' := t0') (a2' := a2') (a6' := a6') (a7' := a7') (n := n) (junk := junk).
      * rewrite En, L1. lia.
      * rewrite L1. cbn [length]. lia.
      * exact (munch_trans _ _ _ _ MU1 MU').
      * exact (wmono_trans rsegs _ _ _ WM1 WM').
      * exact MI'.
      * rewrite <- app_assoc in U'. cbn [app] in U'.
        cbn [ds_lsb]. rewrite (proj2 (Z.ltb_ge x 10) Hge). exact U'.
  - rewrite BR. cbv iota.
    rewrite (proj2 (Z.ltb_lt x 10) Hlt) in L1.
    apply K with (junk := post').
    + rewrite L1. cbn [length]. lia.
    + rewrite L1. cbn [length]. lia.
    + exact MU1.
    + exact WM1.
    + exact HMI1.
    + cbn [ds_lsb]. rewrite (proj2 (Z.ltb_lt x 10) Hlt). exact HU1.
Qed.

Lemma bytes_at_read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia. cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma addr_mod : forall (Bw : word) N bN j, (bv_unsigned Bw + N) mod 2^64 = bN ->
  Z_to_bv 64 (bv_unsigned Bw + (N + j)) = Z_to_bv 64 (bN + j).
Proof.
  intros Bw N bN j H. apply Z_to_bv_eqm. rewrite <- H. rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma cloop : forall r (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Bw : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (P D1 bN N j E lo hi : Z) (pre done : list byte),
  length pre = r -> (1 <= r)%nat ->
  j = Z.of_nat (length done) -> E = j + Z.of_nat r ->
  (bv_unsigned Bw + N) mod 2^64 = bN ->
  bytes_at rsegs m (D1 + 1) pre ->
  bytes_at rsegs m P (le8 (Z_to_bv 64 (N + j))) -> wr_at rsegs m P 8 ->
  bytes_at rsegs m bN done -> wr_at rsegs m bN E ->
  (P + 8 <= bN \/ bN + E <= P) ->
  (P + 8 <= D1 + 1 \/ D1 + 1 + Z.of_nat r <= P) ->
  (bN + E <= D1 + 1 \/ D1 + 1 + Z.of_nat r <= bN) -> 0 <= D1 ->
  mem_inv rsegs m -> stk rsegs m lo hi ->
  (forall (m' : word -> option byte) (a1' a2' a3' : word),
     munch [(P, P + 8); (bN, bN + E)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo hi ->
     bytes_at rsegs m' bN (done ++ rev pre) -> bytes_at rsegs m' P (le8 (Z_to_bv 64 (N + E))) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) Bw (Z_to_bv 64 D1) a1' a2' a3' a4 a5 a6 a7
                         (Z_to_bv 64 D1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13edc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) Bw (Z_to_bv 64 D1) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (D1 + Z.of_nat r)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ebc) fc None m (seg_rom rsegs)).
Proof.
  induction r as [|r IH];
    intros ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Bw F fc m Q
      P D1 bN N j E lo hi pre done HLr Hr1 Hj HE HBN HPRE HBP HWP HBD HWD DJ1 DJ2 DJ3 HD1 HMI HST K; [lia|].
  assert (Hne : pre <> []) by (intros ->; cbn in HLr; lia).
  destruct (exists_last Hne) as (pre' & c & ->). clear Hne.
  rewrite length_app in HLr. cbn [length] in HLr.
  pose proof (bytes_at_bound _ _ _ _ HPRE) as BPRE. rewrite length_app in BPRE. cbn [length] in BPRE.
  pose proof (bytes_at_bound _ _ _ _ HBP) as BBP. rewrite length_le8 in BBP.
  pose proof (bytes_at_bound _ _ _ _ HBD) as BBD.
  pose proof HWD as (BWD1 & BWD2 & _).
  apply bytes_at_app in HPRE. destruct HPRE as [HPRE' HC].
  pose proof (bytes_at_read_all _ _ _ HBP) as RP. rewrite length_le8 in RP.
  pose proof (bytes_at_read_all _ _ _ HC) as RC. cbn [length] in RC.
  assert (HS1 : store_ok rsegs m (wa P) 8 = true).
  { rewrite <- (Z.add_0_r P) at 1. apply (wr_at_store_ok rsegs m P 8 0 8 HWP); lia. }
  pose proof (addr_mod Bw N bN j HBN) as AM.
  do 6 step.
  rewrite AM. change (Z_to_bv 64 P) with (wa P).
  pose proof (bytes_at_write_same rsegs m P (le8 (Z_to_bv 64 (N + j + 1))) ltac:(lia) ltac:(rewrite length_le8; lia)) as HBP1.
  pose proof (wr_at_write rsegs m P 8 (wa P) (le8 (Z_to_bv 64 (N + j + 1))) HWP) as HWP1.
  pose proof (wr_at_write rsegs m bN E (wa P) (le8 (Z_to_bv 64 (N + j + 1))) HWD) as HWD1.
  pose proof (bytes_at_write_other rsegs m P (le8 (Z_to_bv 64 (N + j + 1))) bN done HBD
                ltac:(lia) ltac:(rewrite length_le8; lia) ltac:(rewrite length_le8; lia)) as HBD1.
  pose proof (bytes_at_write_other rsegs m P (le8 (Z_to_bv 64 (N + j + 1))) (D1 + 1) pre' HPRE'
                ltac:(lia) ltac:(rewrite length_le8; lia) ltac:(rewrite length_le8; lia)) as HPRE1.
  pose proof (mem_inv_store rsegs m (wa P) (le8 (Z_to_bv 64 (N + j + 1))) HMI ltac:(rewrite length_le8; exact HS1)) as HMI1.
  pose proof (munch_write [(P, P + 8); (bN, bN + E)] m m P (le8 (Z_to_bv 64 (N + j + 1))) (munch_refl _ m)
                ltac:(lia) ltac:(rewrite length_le8; lia) ltac:(cbn [inside]; rewrite length_le8; lia)) as MU1.
  pose proof (wmono_write rsegs m m (wa P) (le8 (Z_to_bv 64 (N + j + 1))) (wmono_refl rsegs m)) as WM1.
  pose proof (stk_write rsegs m lo hi P (le8 (Z_to_bv 64 (N + j + 1))) HST ltac:(lia) ltac:(rewrite length_le8; lia)) as HST1.
  set (m1 := write_to_mem m (wa P) (le8 (Z_to_bv 64 (N + j + 1)))) in *.
  assert (HS2 : store_ok rsegs m1 (wa (bN + j)) 1 = true) by (apply (wr_at_store_ok rsegs m1 bN E j 1 HWD1); lia).
  step.
  rewrite le1_zxb. change (Z_to_bv 64 (bN + j)) with (wa (bN + j)).
  pose proof (bytes_at_write_other rsegs m1 (bN + j) [c] P (le8 (Z_to_bv 64 (N + j + 1))) HBP1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(rewrite length_le8; cbn [length]; lia)) as HBP2.
  pose proof (wr_at_write rsegs m1 P 8 (wa (bN + j)) [c] HWP1) as HWP2.
  pose proof (wr_at_write rsegs m1 bN E (wa (bN + j)) [c] HWD1) as HWD2.
  pose proof (bytes_at_write_other rsegs m1 (bN + j) [c] bN done HBD1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as HBD2.
  pose proof (bytes_at_write_same rsegs m1 (bN + j) [c] ltac:(lia) ltac:(cbn [length]; lia)) as HC2.
  pose proof (bytes_at_write_other rsegs m1 (bN + j) [c] (D1 + 1) pre' HPRE1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as HPRE2.
  pose proof (mem_inv_store rsegs m1 (wa (bN + j)) [c] HMI1 HS2) as HMI2.
  pose proof (munch_write [(P, P + 8); (bN, bN + E)] m m1 (bN + j) [c] MU1
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [inside length]; lia)) as MU2.
  pose proof (wmono_write rsegs m m1 (wa (bN + j)) [c] WM1) as WM2.
  pose proof (stk_write rsegs m1 lo hi (bN + j) [c] HST1 ltac:(lia) ltac:(cbn [length]; lia)) as HST2.
  set (m2 := write_to_mem m1 (wa (bN + j)) [c]) in *.
  assert (HBD3 : bytes_at rsegs m2 bN (done ++ [c])).
  { apply bytes_at_app. split; [exact HBD2|]. rewrite <- Hj. exact HC2. }
  clear HBD2 HC2.
  replace (D1 + Z.of_nat (S r) + -1) with (D1 + Z.of_nat r) by lia.
  assert (BE : bv_eqb (Z_to_bv 64 (D1 + Z.of_nat r)) (Z_to_bv 64 D1) = Nat.eqb r 0).
  { unfold bv_eqb. rewrite !unsigned_lit by lia.
    destruct (Nat.eqb_spec r 0) as [->|H0]; [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia]. }
  step.
  rewrite BE.
  destruct (Nat.eqb_spec r 0) as [->|Hr0]; cbv iota beta delta [negb].
  - destruct pre' as [|z pre'']; [|cbn in HLr; lia].
    replace (D1 + Z.of_nat 0) with D1 by lia.
    apply K.
    + exact MU2.
    + exact WM2.
    + exact HMI2.
    + exact HST2.
    + cbn [rev app]. exact HBD3.
    + replace (N + E) with (N + j + 1) by lia. exact HBP2.
  - eapply IH with (pre := pre') (done := done ++ [c]) (j := j + 1) (E := E) (N := N) (bN := bN).
    + lia.
    + lia.
    + rewrite length_app. cbn [length]. lia.
    + lia.
    + exact HBN.
    + exact HPRE2.
    + rewrite Z.add_assoc. exact HBP2.
    + exact HWP2.
    + exact HBD3.
    + exact HWD2.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact HMI2.
    + exact HST2.
    + intros m' a1' a2' a3' MU' WM' MI' ST' HB' HP'.
      apply K.
      * exact (munch_trans _ _ _ _ MU2 MU').
      * exact (wmono_trans rsegs _ _ _ WM2 WM').
      * exact MI'.
      * exact ST'.
      * rewrite rev_app_distr. cbn [rev app]. rewrite <- app_assoc in HB'. exact HB'.
      * exact HP'.
Qed.

Lemma u8arr_app : forall m A xs ys,
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

Lemma ds_lsb_length : forall f x, (length (ds_lsb f x) <= f)%nat.
Proof.
  induction f as [|f IH]; intros x; cbn [ds_lsb length]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10)). lia.
Qed.

Lemma rev_ds_lsb : forall f x, rev (ds_lsb f x) = dec_digits f x.
Proof.
  induction f as [|f IH]; intros x; [reflexivity|].
  cbn [ds_lsb dec_digits rev]. destruct (x <? 10); [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma dec_digits_fuel : forall f g x, 0 <= x -> x < 10 ^ Z.of_nat f -> x < 10 ^ Z.of_nat g ->
  (1 <= f)%nat -> (1 <= g)%nat -> dec_digits f x = dec_digits g x.
Proof.
  induction f as [|f IH]; intros g x Hx Hf Hg Hf1 Hg1; [lia|].
  destruct g as [|g]; [lia|].
  cbn [dec_digits]. destruct (Z.ltb_spec x 10) as [H|H]; [reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf, Hg by lia.
  assert (F1 : (1 <= f)%nat) by (destruct f; [cbn in Hf; lia | lia]).
  assert (G1 : (1 <= g)%nat) by (destruct g; [cbn in Hg; lia | lia]).
  rewrite (IH g (x / 10)); [reflexivity | apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia
                           | apply Z.div_lt_upper_bound; lia | exact F1 | exact G1].
Qed.

Lemma log2_fuel : forall x, 0 <= x -> x < 10 ^ Z.of_nat (S (Z.to_nat (Z.log2 x))).
Proof.
  intros x Hx. rewrite Nat2Z.inj_succ, Z2Nat.id by (apply Z.log2_nonneg).
  destruct (Z.eq_dec x 0) as [->|Hx0]; [cbn; lia|].
  destruct (Z.log2_spec x ltac:(lia)) as [_ H].
  eapply Z.lt_le_trans; [exact H|]. rewrite <- Z.add_1_r.
  apply Z.pow_le_mono_l. pose proof (Z.log2_nonneg x). lia.
Qed.

Lemma dec_ds : forall v, 0 <= v < 2^32 ->
  dec_digits (S (Z.to_nat (Z.log2 v))) v = rev (ds_lsb 10 v).
Proof.
  intros v Hv. rewrite rev_ds_lsb. apply dec_digits_fuel.
  - lia.
  - apply log2_fuel. lia.
  - change (10 ^ Z.of_nat 10) with 10000000000. change (2 ^ 32) with 4294967296 in Hv. lia.
  - lia.
  - lia.
Qed.

Theorem put_dec_holds : memset_contract -> put_dec_contract.
Proof.
  intros MSET. unfold put_dec_contract, PUT_DEC, PUT_DEC_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b p v mn N
    E0 E1 EV HV E3 HMN HP HPW HPA HW HMI ST LO DJ1 DJ2 DJ3.
  subst a0 a1 a3.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 8);
                (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (zr_word sp) as Rsp'. unfold inr64 in Rsp'.
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
  carve_frame 40%nat ST. rename FR into FRS, junk into jS.
  carve_frame 10%nat ST. rename FR into FRD, junk into jD.
  carve_frame 14%nat ST. rename FR into FRL, junk into jL.
  do 16 zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  assert (LJD : length jD = 10%nat) by (destruct FRD as [[W _] _]; exact (proj1 W)).
  pose proof (u8arr_of_rw_cells rsegs mA (bv_unsigned sp + -50) 10 jD FRD) as UD. clear FRD.
  eapply (dloop 10%nat) with (D := bv_unsigned sp + -50) (i := 0) (x := v) (pre := []) (post := jD).
  { lia. }
  { change (10 ^ Z.of_nat 10) with 10000000000. change (2 ^ 32) with 4294967296 in Hv32. lia. }
  { exact EV. }
  { exact HV. }
  { reflexivity. }
  { rewrite LJD, <- En0. exact LDS. }
  { cbn [length]. lia. }
  { cbn [app]. exact UD. }
  { exact HMI. }
  intros mB t0' a2' a6' a7' nz junk En EJ MU1 WM1 MI1 U1.
  transport_after_call rsegs mA mB MU1 WM1.
  clear MU1 WM1 HMI. cbn [app] in U1.
  assert (Enz : nz = Z.of_nat n) by (rewrite En, <- En0; reflexivity). clear En. subst nz.
  match goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  assert (TAIL : forall (mX : word -> option byte) (E : Z) (rest : list byte)
                   (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s3x t3x t4x t5x t6x : word),
    E = Z.max mn (Z.of_nat n) ->
    u8arr rsegs mX (bv_unsigned sp + -50) (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat E - n) ++ rest) ->
    length (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat E - n) ++ rest) = 10%nat ->
    bytes_at rsegs mX p (le8 N) -> wr_at rsegs mX p 8 -> wr_at rsegs mX (b + bv_unsigned N) (dec_len v mn) ->
    munch [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 8);
           (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m mX ->
    wmono rsegs m mX -> mem_inv rsegs mX -> stk rsegs mX lo (bv_unsigned sp + -64) ->
    rw_cells rsegs mX (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mX (bv_unsigned sp + -64) [CB 14 jL] ->
    evt rsegs Q (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0x t1x t2x (Z_to_bv 64 p) (Z_to_bv 64 b)
                         a0x a1x a2x a3x a4x a5x a6x a7x (Z_to_bv 64 E) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x)
                    F (Z_to_bv 64 0x13eb4) fc None mX (seg_rom rsegs))).
  { intros mX E rest rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s3x t3x t4x t5x t6x
      HEE UX LX HPX HPWX HWX MUX WMX MIX STX FRSX FRLX.
    zstep. zstep.
    assert (Eb : E = dec_len v mn) by (rewrite HE; exact HEE).
    pose proof STX as (SL1 & SL2 & _).
    set (pre := ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat E - n)) in *.
    assert (LP : length pre = Z.to_nat E) by (unfold pre; rewrite length_app, repeat_length, <- En0; lia).
    assert (DE : DEC v mn = rev pre).
    { unfold pre, DEC. rewrite dec_ds by lia. rewrite rev_app_distr, rev_repeat, length_rev, <- En0.
      f_equal. f_equal. lia. }
    pose proof UX as UX0. rewrite app_assoc in UX0. fold pre in UX0.
    apply u8arr_app in UX0. destruct UX0 as [UP _].
    remember (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat E - n) ++ rest) as dfull eqn:Edf.
    replace (bv_unsigned sp + -51 + E) with (bv_unsigned sp + -51 + Z.of_nat (Z.to_nat E)) by lia.
    eapply cloop with (pre := pre) (done := []) (j := 0) (E := E) (N := bv_unsigned N) (bN := b + bv_unsigned N)
                      (P := p) (D1 := bv_unsigned sp + -51) (lo := lo) (hi := bv_unsigned sp + -64).
    { exact LP. }
    { lia. }
    { reflexivity. }
    { lia. }
    { rewrite unsigned_lit_wrap, Z.add_mod_idemp_l by lia. apply Z.mod_small. lia. }
    { replace (bv_unsigned sp + -51 + 1) with (bv_unsigned sp + -50) by lia. exact (proj1 UP). }
    { rewrite Z.add_0_r, Z_to_bv_lit_self. exact HPX. }
    { exact HPWX. }
    { apply bytes_at_nil. lia. }
    { rewrite Eb. exact HWX. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { exact MIX. }
    { exact STX. }
    intros mY a1y a2y a3y MUY WMY MIY STY HBY HPY.
    clear UP.
    transport_after_call rsegs mX mY MUY WMY.
    clear MUY WMY.
    do 7 zstep.
    pose proof (rw_cells_of_u8arr rsegs mY _ _ UX) as FRDX. rewrite LX in FRDX.
    release_frame FRLX STY (bv_unsigned sp + -50).
    release_frame FRDX STY (bv_unsigned sp + -40).
    release_frame FRSX STY (bv_unsigned sp).
    apply evt_done. unfold Q. do 16 eexists.
    split; [reflexivity|].
    split; [exact MUX|]. split; [exact WMX|]. split; [exact MIY|]. split; [exact STY|]. split.
    - rewrite DE. exact HBY.
    - rewrite <- Eb. exact HPY. }
  zstep. zstep.
  assert (BL : bv_ltu (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 mn) = (Z.of_nat n <? mn)).
  { unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. }
  rewrite BL.
  destruct (Z.ltb_spec (Z.of_nat n) mn) as [Hlt|Hge]; cbv iota beta delta [negb].
  - do 9 zstep.
    rewrite (Z.mod_small (Z.of_nat n) 4294967296) by lia.
    assert (A2E : ((Z.lxor (Z.of_nat n) 18446744073709551615 + mn) mod 18446744073709551616) mod 4294967296 + 1
                  = mn - Z.of_nat n).
    { rewrite zb_lxor_ones by lia.
      replace (18446744073709551615 - Z.of_nat n + mn) with ((mn - Z.of_nat n - 1) + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. rewrite (Z.mod_small (mn - Z.of_nat n - 1)) by lia.
      rewrite Z.mod_small by lia. lia. }
    rewrite A2E.
    zstep.
    remember (Z.to_nat (mn - Z.of_nat n)) as k eqn:Ek.
    assert (LJ : length junk = (10 - n)%nat) by lia.
    rewrite <- (firstn_skipn k junk) in U1.
    apply u8arr_app in U1. destruct U1 as [UDs U1]. rewrite <- En0 in U1.
    apply u8arr_app in U1. destruct U1 as [UJ1 UJ2].
    assert (LF : length (firstn k junk) = k) by (rewrite length_firstn; lia).
    rewrite LF in UJ2.
    pose proof (rw_cells_of_u8arr rsegs mB _ _ UJ1) as RWM. rewrite LF in RWM. clear UJ1.
    eapply evt_cut; [eapply MSET with (junk := firstn k junk) |].
    { rewrite !unsigned_lit by lia. rewrite <- Ek. exact RWM. }
    { exact MI1. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (t0m & t1m & t2m & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3m & t4m & t5m & t6m & mC
                    & -> & MU2 & WM2 & MI2 & RWF).
    rewrite !unsigned_lit in MU2, RWF by lia. rewrite <- Ek in RWF.
    change (Z_to_bv 8 (48 mod 256)) with (dg 0) in RWF.
    clear RWM.
    transport_after_call rsegs mB mC MU2 WM2.
    clear MU2 WM2 MI1.
    pose proof (u8arr_of_rw_cells rsegs mC _ _ _ RWF) as UF. clear RWF.
    replace (ret_pc (Z_to_bv 64 81576)) with (Z_to_bv 64 81576) by (apply bv_eq; vm_compute; reflexivity).
    zstep.
    rewrite (Z.mod_small (Z.of_nat n) 4294967296) by lia.
    zstep.
    rewrite BL. cbv iota.
    eapply TAIL with (E := mn) (rest := skipn k junk).
    { lia. }
    { replace (Z.to_nat mn - n)%nat with k by lia.
      apply u8arr_app. split; [exact UDs|]. rewrite <- En0.
      apply u8arr_app. split; [exact UF|]. rewrite repeat_length. exact UJ2. }
    { rewrite !length_app, repeat_length, length_skipn. lia. }
    { exact HP. }
    { exact HPW. }
    { exact HW. }
    { exact MU. }
    { exact WM. }
    { exact MI2. }
    { exact ST. }
    { exact FRS. }
    { exact FRL. }
  - zstep.
    rewrite (Z.mod_small (Z.of_nat n) 4294967296) by lia.
    zstep.
    rewrite BL. cbv iota.
    zstep.
    eapply TAIL with (E := Z.of_nat n) (rest := junk).
    { lia. }
    { rewrite Nat2Z.id, Nat.sub_diag. cbn [repeat app]. exact U1. }
    { rewrite Nat2Z.id, Nat.sub_diag. cbn [repeat app]. rewrite length_app. lia. }
    { exact HP. }
    { exact HPW. }
    { exact HW. }
    { exact MU. }
    { exact WM. }
    { exact MI1. }
    { exact ST. }
    { exact FRS. }
    { exact FRL. }
Qed.
