From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib memcpy_c
  reac_frame_is_reac_c reac_frame_clean_len_c reac_frame_clean_len.
Import ListNotations.
Open Scope Z_scope.

Definition en_k (pl : list byte) : Z := Z.min (Z.of_nat (length pl)) 3.
Definition en_len (pl : list byte) : Z := Z.of_nat (length pl) - en_k pl.
Definition GOTB : list byte := le8 (Z_to_bv 64 0x103f8) ++ le8 (Z_to_bv 64 0x10410) ++ le8 (Z_to_bv 64 0x10404).

Definition q_en1 (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp lo p k len : Z) (w : list cell) (ms : machine_state) : Prop :=
  exists R m' mode nch ns j', ms = MS R F (Z_to_bv 64 0x147c4) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12d74 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 10 = Z_to_bv 64 len /\ reg_get R 18 = Z_to_bv 64 mode /\ reg_get R 19 = Z_to_bv 64 (p + k) /\
    reg_get R 25 = Z_to_bv 64 len /\
    munch [(Sp, Sp + 160)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rw_cells rsegs m' Sp (CB 44 j' :: C4 (Z_to_bv 64 48000) :: C4 (Z_to_bv 64 nch) :: C4 (Z_to_bv 64 ns) :: w) /\
    -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
    ((mode = 0x103f8 \/ mode = 0x10404 \/ mode = 0x10410) \/ mode = Sp + 44).

Lemma en_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma ubyte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma sbyte_range : forall b : byte, -128 <= bv_signed b < 128.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_signed, bv_swrap, bv_wrap.
  unfold bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Definition en_sx (fb : Z) : Z := if fb <? 128 then fb else fb - 256.

Lemma en_signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.

Lemma en_signed_hi : forall x, 2 ^ 63 <= x < 2 ^ 64 -> bv_signed (Z_to_bv 64 x) = x - 2 ^ 64.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.

Lemma en_sext : forall fb, 0 <= fb < 256 ->
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fb)) 56))) 56) =
  Z_to_bv 64 (en_sx fb).
Proof.
  intros fb Hfb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. unfold en_sx.
  destruct (Z.ltb_spec fb 128) as [H|H].
  - rewrite en_signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
  - rewrite en_signed_hi by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (fb * 2 ^ 56 - 2 ^ 64) with ((fb - 256) * 2 ^ 56) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Ltac qreg := split; [reflexivity|].

Lemma en_tail :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte)
         (Sp lo p k len fb0 fb1 v2 : Z) (j : list byte) (w : list cell),
    0 <= Sp < 2 ^ 63 -> lo <= Sp -> 0x1d0a0 <= Sp ->
    0 <= fb0 < 256 -> 0 <= fb1 < 256 -> -128 <= v2 < 128 ->
    rw_cells rsegs m Sp (CB 56 j :: w) -> mem_inv rsegs m -> stk rsegs m lo Sp ->
    munch [(Sp, Sp + 160)] mb m -> wmono rsegs mb m ->
    bytes_at rsegs m 0x1d088 (le8 (Z_to_bv 64 0x103f8)) ->
    bytes_at rsegs m 0x1d090 (le8 (Z_to_bv 64 0x10410)) ->
    bytes_at rsegs m 0x1d098 (le8 (Z_to_bv 64 0x10404)) ->
    evt rsegs (q_en1 F fc x3 x4 mb Sp lo p k len w)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 fb0) (Z_to_bv 64 fb1)
               (Z_to_bv 64 v2) x15 x16 x17 x18 (Z_to_bv 64 (p + k)) x20 x21 x22 x23 x24 (Z_to_bv 64 len) x26 x27
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x12d14) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
    F fc mb m Sp lo p k len fb0 fb1 v2 j w HSp HlS HgS Hb0 Hb1 Hv2 FR MI ST MU WM HG1 HG2 HG3.
  do 8 step.
  rewrite (en_sext fb1 Hb1) in FR |- *.
  rewrite (unsigned_lit fb0) by lia. rewrite (land3 fb0) by lia.
  assert (Hs : fb0 mod 4 = 0 \/ fb0 mod 4 = 1 \/ fb0 mod 4 = 2 \/ fb0 mod 4 = 3) by lia.
  pose proof (rd_all _ _ _ HG1) as RG1. pose proof (rd_all _ _ _ HG2) as RG2. pose proof (rd_all _ _ _ HG3) as RG3.
  rewrite length_le8 in RG1, RG2, RG3.
  assert (Hsx : -128 <= en_sx fb1 <= 127) by (unfold en_sx; destruct (Z.ltb_spec fb1 128); lia).
  destruct Hs as [E|[E|[E|E]]]; rewrite E.
  - step. if_false. step. if_false. do 5 step.
    apply evt_done. unfold q_en1. eexists. eexists. exists 0x103f8, (en_sx fb1), v2. eexists.
    split; [reflexivity|]. do 8 qreg.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
    split; [lia|]. split; [lia|]. left; left; reflexivity.
  - step. if_false. step. if_true. do 5 step.
    apply evt_done. unfold q_en1. eexists. eexists. exists 0x10404, (en_sx fb1), v2. eexists.
    split; [reflexivity|]. do 8 qreg.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
    split; [lia|]. split; [lia|]. left; right; left; reflexivity.
  - step. if_true. step. step. if_false. do 5 step.
    apply evt_done. unfold q_en1. eexists. eexists. exists 0x10410, (en_sx fb1), v2. eexists.
    split; [reflexivity|]. do 8 qreg.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
    split; [lia|]. split; [lia|]. left; right; right; reflexivity.
  - step. if_true. step. step. if_true. do 3 step.
    apply evt_done. unfold q_en1. eexists. eexists. exists (Sp + 44), (en_sx fb1), v2. eexists.
    split; [reflexivity|]. qreg. qreg. qreg. qreg. qreg.
    split; [first [reflexivity | rewrite (unsigned_lit Sp) by lia; reflexivity | f_equal; lia]|]. qreg. qreg.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
    split; [lia|]. split; [lia|]. right; reflexivity.
Qed.

Ltac ensolve := first [ eassumption | lia
  | (eapply munch_weaken; [|eassumption]; intros x; cbn [outside]; intros [H _]; split; [lia | exact I])
  | (rewrite ?(unsigned_lit _) by lia; f_equal; lia) ].

Section E.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (pl : list byte).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : lo + 160 <= bv_unsigned sp.
Hypothesis Hsp63 : bv_unsigned sp < 2 ^ 63.
Hypothesis MI : mem_inv rsegs m.
Hypothesis HN : Z.of_nat (length pl) < 2 ^ 26.
Hypothesis HP : (0 < length pl)%nat -> bytes_at rsegs m p pl.
Hypothesis HPL : (0 < length pl)%nat -> p + Z.of_nat (length pl) <= lo.
Hypothesis HP0 : 0 <= p < 2 ^ 64.
Hypothesis HG1 : bytes_at rsegs m 0x1d088 (le8 (Z_to_bv 64 0x103f8)).
Hypothesis HG2 : bytes_at rsegs m 0x1d090 (le8 (Z_to_bv 64 0x10410)).
Hypothesis HG3 : bytes_at rsegs m 0x1d098 (le8 (Z_to_bv 64 0x10404)).
Hypothesis HGL : 0x1d0a0 <= lo.

Lemma en1 :
  evt rsegs (q_en1 F fc gp tp m (bv_unsigned sp - 160) lo p (en_k pl) (en_len pl)
              [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length pl))) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12c60) fc None m (seg_rom rsegs)).
Proof.
  destruct (Nat.eq_dec (length pl) 0) as [N0|N0].
  { pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
      carve_frame 160%nat ST.
      do 16 step.
      rewrite (unsigned_lit (Z.of_nat (length pl))) by lia.
      if_false_by (en_cond (Z.of_nat (length pl)) ltac:(lia)).
      step. step.
    if_cases HC.
  - assert (Hn0 : length pl = 0%nat) by (zify_cond HC; lia).
      pose proof (rd_all _ _ _ HG1) as RG1. rewrite length_le8 in RG1.
      do 4 step. step. step. step. step. step. step. step.
      apply evt_done. unfold q_en1. eexists. eexists. exists 0x103f8, 0, 0. eexists.
      split; [reflexivity|]. do 4 qreg.
      split; [unfold en_len, en_k; rewrite Hn0; reflexivity|]. qreg.
      split; [replace (p + en_k pl) with p by (unfold en_k; rewrite Hn0; lia); reflexivity|].
      split; [unfold en_len, en_k; rewrite Hn0; reflexivity|].
      split; [eapply munch_weaken; [|exact MU]; intros x; cbn [outside]; intros [H _]; split; [lia | exact I]|].
      split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
      split; [lia|]. split; [lia|]. left; left; reflexivity.
    - exfalso. rewrite N0 in HC. vm_compute in HC. discriminate HC. }
  pose proof (HP ltac:(lia)) as HP1. pose proof (HPL ltac:(lia)) as HPL1.
  pose proof (bytes_at_bound _ _ _ _ HP1) as HPB.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  carve_frame 160%nat ST.
  do 16 step.
  rewrite (unsigned_lit (Z.of_nat (length pl))) by lia.
  if_false_by (en_cond (Z.of_nat (length pl)) ltac:(lia)).
  step. step.
  if_cases HC.
  - exfalso. zify_cond HC. lia.
  - assert (Hn1 : (1 <= length pl)%nat) by lia.
    assert (RB0 : ov_read_bytes rsegs m0 (Z_to_bv 64 (p + 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
      by (apply (rd1 _ _ _ 0 HP1); lia).
    assert (RB0' : ov_read_bytes rsegs m0 (Z_to_bv 64 p) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
      by (rewrite <- RB0; f_equal; f_equal; lia).
    pose proof (ubyte_range (nth 0 pl (Z_to_bv 8 0))) as R0.
    step. step. step. if_cases HC1.
    + assert (Hn2 : (2 <= length pl)%nat) by (zify_cond HC1; lia).
      assert (RB1 : ov_read_bytes rsegs m0 (Z_to_bv 64 (p + 1)) 1 = Some [nth 1 pl (Z_to_bv 8 0)])
        by (apply (rd1 _ _ _ 1 HP1); lia).
      pose proof (ubyte_range (nth 1 pl (Z_to_bv 8 0))) as R1.
      step. step. step. if_cases HC2.
      * assert (Hn3 : (3 <= length pl)%nat) by (zify_cond HC2; lia).
        assert (RB2 : ov_read_bytes rsegs m0 (Z_to_bv 64 (p + 2)) 1 = Some [nth 2 pl (Z_to_bv 8 0)])
          by (apply (rd1 _ _ _ 2 HP1); lia).
        pose proof (sbyte_range (nth 2 pl (Z_to_bv 8 0))) as R2.
        step. step. step.
        replace (en_k pl) with 3 by (unfold en_k; lia).
        replace (en_len pl) with (Z.of_nat (length pl) - 3) by (unfold en_len, en_k; lia).
        eapply en_tail; ensolve.
      * step. step. step. step.
        replace (en_k pl) with 2 by (unfold en_k; zify_cond HC2; lia).
        replace (en_len pl) with 0 by (unfold en_len, en_k; zify_cond HC2; lia).
        eapply en_tail; ensolve.
    + step. step. step. step. step.
      replace (en_k pl) with 1 by (unfold en_k; zify_cond HC1; lia).
      replace (en_len pl) with 0 by (unfold en_len, en_k; zify_cond HC1; lia).
      eapply en_tail; ensolve.
Qed.

Lemma en1_eq : forall x10 x11 : word, x10 = Z_to_bv 64 p -> x11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  evt rsegs (q_en1 F fc gp tp m (bv_unsigned sp - 160) lo p (en_k pl) (en_len pl)
              [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12c60) fc None m (seg_rom rsegs)).
Proof. intros x10 x11 -> ->. exact en1. Qed.

End E.

Lemma km_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_M; lia | rewrite length_le8; unfold A_M; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma kt_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_T; lia | rewrite length_le8; unfold A_T; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c32_core : forall x y, 0 <= x < 2^32 -> y = (x * 954437177) mod 2^32 ->
  ((y mod 4) * 2^30 + y / 4 < 119304648 <-> x mod 36 = 0).
Proof.
  intros x y Hx Hy.
  set (s := (x * 954437177) / 2^32) in *.
  assert (Es : x * 954437177 = 2^32 * s + y) by (subst y s; apply Z.div_mod; lia).
  assert (Ry : 0 <= y < 2^32) by (subst y; apply Z.mod_pos_bound; lia).
  clearbody s. clear Hy.
  set (b := y mod 4). set (a := y / 4).
  assert (Ea : y = 4 * a + b) by (apply Z.div_mod; lia).
  assert (Rb : 0 <= b < 4) by (apply Z.mod_pos_bound; lia).
  set (f := x mod 36). set (e := x / 36).
  assert (Ex : x = 36 * e + f) by (apply Z.div_mod; lia).
  assert (Rf : 0 <= f < 36) by (apply Z.mod_pos_bound; lia).
  clearbody a b e f.
  change (2^32) with 4294967296 in *. change (2^30) with 1073741824 in *.
  split.
  - intro Hlt.
    assert (Hb : b = 0) by lia. subst b.
    remember (9 * s - 2 * x) as t eqn:Et.
    assert (E9 : x = 36 * a + 4294967296 * t) by lia.
    assert (Ht : t = 0 \/ t = -1) by lia.
    destruct Ht as [Ht | Ht]; subst t; lia.
  - intro Hf. subst f.
    remember (8 * e - s) as t eqn:Et.
    assert (E4 : y = 4 * e + 4294967296 * t) by lia.
    assert (Ht : t = 0) by lia. subst t.
    lia.
Qed.

Lemma c64_cond : forall len, 54 <= len < 2 ^ 26 -> (len - 52) mod 36 = 2 ->
  bv_ltu (Z_to_bv 64 (Z.lor
    (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (len - 2 + -52)) *
       bv_unsigned (Z_to_bv 64 KM)))) 2)))
    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (len - 2 + -52)) *
       bv_unsigned (Z_to_bv 64 KM)))) 62))))) (Z_to_bv 64 KT) = true.
Proof.
  intros len H1 H2. unfold bv_ltu. rewrite !unsigned_lit_wrap. rewrite rot_wrap.
  rewrite (Z.mod_small KT) by (unfold KT; lia). rewrite (Z.mod_small KM) by (unfold KM; lia).
  rewrite (Z.mod_small (len - 2 + -52)) by lia.
  replace (len - 2 + -52) with (len - 54) by lia.
  apply Z.ltb_lt.
  apply (proj2 (c2_core (len - 54) (((len - 54) * KM) mod 2^64) ltac:(lia) eq_refl)).
  Z.div_mod_to_equations. lia.
Qed.

Lemma c32_val : forall len, 54 <= len < 2 ^ 26 ->
  v_sltu (Z_to_bv 64 (Z.lor
    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64
       (bv_unsigned (Z_to_bv 64 len) * 954437177 + -6)))) 2))))
    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64
       (bv_unsigned (Z_to_bv 64 len) * 954437177 + -6))) 30))))))
    (Z_to_bv 64 119304648) = Z_to_bv 64 (if (len - 54) mod 36 =? 0 then 1 else 0).
Proof.
  intros len H.
  rewrite (unsigned_lit len) by lia.
  assert (HX : 0 <= len * 954437177 + -6 < 2 ^ 64) by lia.
  rewrite (unsigned_lit (len * 954437177 + -6)) by lia.
  set (X := len * 954437177 + -6) in *.
  set (y := bv_wrap 32 X).
  assert (Ey : y = X mod 2 ^ 32) by reflexivity.
  assert (Ry : 0 <= y < 2 ^ 32) by (rewrite Ey; apply Z.mod_pos_bound; lia).
  assert (Ey2 : y = ((len - 54) * 954437177) mod 2 ^ 32).
  { rewrite Ey. subst X. replace (len * 954437177 + -6) with ((len - 54) * 954437177 + 12 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (Q4 : 0 <= y / 4 < 2 ^ 30) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (S1 : bv_swrap 32 (y / 4) = y / 4).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 / 2) with 2147483648. rewrite Z.mod_small by lia. lia. }
  rewrite S1. rewrite (unsigned_lit (y / 4)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (EXy : X mod 4 = y mod 4).
  { rewrite Ey. Z.div_mod_to_equations. lia. }
  assert (S2 : bv_swrap 32 (X * 2 ^ 30) = if y mod 4 <? 2 then (y mod 4) * 2 ^ 30 else (y mod 4) * 2 ^ 30 - 2 ^ 32).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 / 2) with 2147483648. change (2 ^ 30) with 1073741824. change (2 ^ 32) with 4294967296.
    rewrite <- EXy. destruct (Z.ltb_spec (X mod 4) 2); Z.div_mod_to_equations; lia. }
  rewrite S2. rewrite unsigned_lit_wrap. rewrite v_sltu_b2z. rewrite (unsigned_lit 119304648) by lia.
  pose proof (c32_core (len - 54) y ltac:(lia) Ey2) as C.
  assert (Rb : 0 <= y mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec (y mod 4) 2) as [Lb|Lb].
  - rewrite (Z.mod_small ((y mod 4) * 2 ^ 30)) by lia.
    rewrite (lor_low 30 (y / 4) (y mod 4)) by lia.
    rewrite (unsigned_lit ((y mod 4) * 2 ^ 30 + y / 4)) by lia.
    destruct (Z.ltb_spec ((y mod 4) * 2 ^ 30 + y / 4) 119304648) as [L|L];
      destruct (Z.eqb_spec ((len - 54) mod 36) 0) as [E|E]; try reflexivity.
    + exfalso. apply E. apply C. exact L.
    + exfalso. apply (proj2 C) in E. lia.
  - replace (((y mod 4) * 2 ^ 30 - 2 ^ 32) mod 2 ^ 64) with ((y mod 4 + 2 ^ 34 - 4) * 2 ^ 30)
      by (set (r := y mod 4) in *; clearbody r; Z.div_mod_to_equations; lia).
    rewrite (lor_low 30 (y / 4) (y mod 4 + 2 ^ 34 - 4)) by lia.
    rewrite (unsigned_lit ((y mod 4 + 2 ^ 34 - 4) * 2 ^ 30 + y / 4)) by lia.
    rewrite (proj2 (Z.ltb_ge _ 119304648)) by lia.
    destruct (Z.eqb_spec ((len - 54) mod 36) 0) as [E|E]; [|reflexivity].
    exfalso. apply (proj2 C) in E. lia.
Qed.

Ltac iff_false tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false by (symmetry; tac); cbv iota end.
Ltac iff_true tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true by (symmetry; tac); cbv iota end.

Lemma lxor_bound : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb.
  assert (NN : 0 <= Z.lxor a b) by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; lia).
  split; [exact NN|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [rewrite E; lia|].
  assert (P : 0 < Z.lxor a b) by lia.
  apply Z.log2_lt_pow2; [exact P|].
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as L.
  assert (La : Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [->|Na]; [reflexivity | apply Z.log2_lt_pow2; lia]).
  assert (Lb : Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|Nb]; [reflexivity | apply Z.log2_lt_pow2; lia]).
  lia.
Qed.

Lemma snez_xor : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) =
  Z_to_bv 64 (if a =? b then 0 else 1).
Proof.
  intros a b Ha Hb. rewrite (unsigned_lit a), (unsigned_lit b) by lia.
  pose proof (lxor_bound a b Ha Hb) as B.
  rewrite v_sltu_b2z. rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit (Z.lxor a b)) by lia.
  destruct (Z.eqb_spec a b) as [E|E].
  - subst b. rewrite Z.lxor_nilpotent. reflexivity.
  - assert (N : Z.lxor a b <> 0) by (intros H; apply E; apply Z.lxor_eq; exact H).
    rewrite (proj2 (Z.ltb_lt 0 (Z.lxor a b))) by lia. reflexivity.
Qed.

Section EC.
Context (ICL : reac_frame_clean_len_contract).
Variables (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
  : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (Sp len : Z).
Hypothesis HLB : 0 <= len < 2 ^ 26.
Hypothesis MI : mem_inv rsegs m.

Lemma en_clean :
  (forall y10 y11 y12 y13 : word,
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x12ddc) (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 y13 x14 x15 x16 x17 x18
       x19 x20 x21 x22 x23 x24 (Z_to_bv 64 len) x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12e5c) fc None m
       (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 len) x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12dd4) fc None m (seg_rom rsegs)).
Proof.
  intros CONT.
  pose proof ICL as CL. unfold reac_frame_clean_len_contract in CL.
  step. step.
  eapply evt_cut; [eapply CL; [apply km_bytes; exact MI | apply kt_bytes; exact MI]|].
  intros ms' (c1 & c2 & c3 & ->).
  replace (ret_pc (Z_to_bv 64 0x12ddc)) with (Z_to_bv 64 0x12ddc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) by lia.
  step.
  unfold reac_frame_clean_len_model.
  destruct ((54 <=? len) && ((len - 52) mod 36 =? 2)) eqn:EC.
  - pose proof EC as EC'. apply andb_true_iff in EC' as [E1 E2]. apply Z.leb_le in E1. apply Z.eqb_eq in E2.
    rewrite eqb_lit by lia. rewrite (proj2 (Z.eqb_neq (len - 2) len)) by lia. cbv iota.
    step. step. iff_false ltac:(rewrite ltu_lit by lia; apply Z.ltb_ge; lia).
    step. step. iff_false ltac:(apply negb_false_iff; rewrite eqb_lit by lia; apply Z.eqb_eq; lia).
    pose proof (rd_all _ _ _ (km_bytes m MI)) as RKM. pose proof (rd_all _ _ _ (kt_bytes m MI)) as RKT.
    rewrite length_le8 in RKM, RKT.
    do 8 step. step. step.
    iff_false ltac:(apply negb_false_iff; apply c64_cond; lia).
    step. step. iff_false ltac:(rewrite ltu_lit by lia; apply Z.ltb_ge; lia).
    do 10 step.
    rewrite (c32_val len) by lia.
    replace ((len - 54) mod 36 =? 0) with true by (symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia).
    step. step. step.
    rewrite snez_xor by lia. rewrite (proj2 (Z.eqb_neq (len - 2) len)) by lia.
    step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
    apply CONT.
  - rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbv iota.
    step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec len 54) as [L54|L54].
    + step. step. step.
      rewrite snez_xor by lia. rewrite Z.eqb_refl.
      step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
      apply CONT.
    + do 10 step.
      rewrite (c32_val len) by lia.
      replace ((len - 54) mod 36 =? 0) with false.
      2:{ symmetry. apply Z.eqb_neq. intros H54. apply andb_false_iff in EC. destruct EC as [EC|EC].
          - apply Z.leb_gt in EC. lia.
          - apply Z.eqb_neq in EC. apply EC. Z.div_mod_to_equations. lia. }
      step. step. step.
      rewrite snez_xor by lia. rewrite Z.eqb_refl.
      step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
      apply CONT.
Qed.

End EC.

Section E2.
Context (MC : memcpy_contract) (IIR : reac_frame_is_reac_contract) (ICL : reac_frame_clean_len_contract).
Variables (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (Sp mode src frame len lo : Z) (fr junk : list byte).
Hypothesis HSp : 0 <= Sp < 2 ^ 63.
Hypothesis HLB : 0 <= len < 2 ^ 26.
Hypothesis HSR : 0 < len -> 0 <= src < 2 ^ 60.
Hypothesis HLEN : Z.of_nat (length fr) = len.
Hypothesis HSRC : 0 < len -> bytes_at rsegs m src fr.
Hypothesis HO : 0 < len -> rw_cells rsegs m frame [CB (Z.to_nat len) junk].
Hypothesis HFP : 4096 <= frame < 2 ^ 60.
Hypothesis DSF : frame + len <= src \/ src + len <= frame.
Hypothesis MI : mem_inv rsegs m.

Definition en2_k : Prop :=
  forall (z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) (m' : word -> option byte),
    munch [(frame, frame + len)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> bytes_at rsegs m' frame fr ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x12ddc) (Z_to_bv 64 Sp) x3 x4 z5 z6 z7 x8 x9 z10 z11 z12 z13 z14 z15 z16 z17
       (Z_to_bv 64 mode) (Z_to_bv 64 src) x20 x21 x22 x23 x24 (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 z28 z29 z30 z31)
       F (Z_to_bv 64 0x12e5c) fc None m' (seg_rom rsegs)).

Lemma ir_byte_eq : forall (b : byte) c, 0 <= c < 256 ->
  bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (ubyte_range b). unfold zxb. rewrite eqb_lit by lia. reflexivity.
Qed.

Lemma ir_seqz : forall (b : byte),
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -25)) 1 = Z_to_bv 64 (if bv_unsigned b =? 25 then 1 else 0).
Proof.
  intros b. pose proof (ubyte_range b) as R. unfold v_sltiu, zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  destruct (Z.eqb_spec (bv_unsigned b) 25) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    destruct (Z.ltb_spec ((bv_unsigned b + -25) mod 2 ^ 64) 1); [|reflexivity].
    exfalso. Z.div_mod_to_equations. lia.
Qed.

Lemma en2 : en2_k ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 frame) x11 x12 x13 x14 x15 x16 x17
     (Z_to_bv 64 mode) (Z_to_bv 64 src) x20 x21 x22 x23 x24 (Z_to_bv 64 len) x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 0x12d74) fc None m (seg_rom rsegs)).
Proof.
  intros K.
  pose proof IIR as IR. unfold reac_frame_is_reac_contract in IR.
  step. step. if_cases HC0.
  - assert (L0 : len = 0) by (destruct (Z.eq_dec len 0) as [E|E]; [exact E|]; exfalso; rewrite eqb_lit in HC0 by lia;
      apply Z.eqb_eq in HC0; exact (E HC0)).
    assert (F0 : fr = []) by (destruct fr as [|x r]; [reflexivity | cbn [length] in HLEN; lia]).
    step. step. rewrite HC0. cbv iota.
    step. step.
    eapply evt_cut.
    { eapply IR with (bs := @nil byte). rewrite (unsigned_lit 0) by lia. intros _ H. lia. }
    intros ms' (b1' & b2' & b3' & ->).
    replace (ret_pc (Z_to_bv 64 0x12dcc)) with (Z_to_bv 64 0x12dcc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    replace (is_reac_result (bv_unsigned (Z_to_bv 64 frame)) (bv_unsigned (Z_to_bv 64 0)) []) with 0
      by (unfold is_reac_result; rewrite (unsigned_lit 0) by lia; destruct (_ =? 0); reflexivity).
    step. step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
    eapply en_clean; [exact ICL | lia | exact MI |].
    intros y10 y11 y12 y13.
    apply K; [apply munch_refl | apply wmono_refl | exact MI |].
    rewrite F0. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - step. if_cases HC1; [exfalso; zify_cond HC1; lia|].
    step. step. if_cases HC2; [exfalso; zify_cond HC2; lia|].
    step. step. step.
    assert (HL0 : 0 < len).
    { destruct (Z.eq_dec len 0) as [E|E]; [|lia]. rewrite E in HC2. vm_compute in HC2. discriminate HC2. }
    pose proof (HSRC HL0) as HSRC1. pose proof (HO HL0) as HO1. pose proof (HSR HL0) as HSR1.
    pose proof (bytes_at_bound _ _ _ _ HSRC1) as HSB.
    eapply evt_cut.
    { eapply MC with (src := fr) (junk := junk); rewrite ?(unsigned_lit src), ?(unsigned_lit frame), ?(unsigned_lit len) by lia.
      - exact HSRC1.
      - lia.
      - exact HO1.
      - lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
      & -> & MU1 & WM1 & MI1 & HF1 & HS1).
    replace (ret_pc (Z_to_bv 64 0x12d94)) with (Z_to_bv 64 0x12d94) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit frame) in MU1, HF1 by lia. rewrite (unsigned_lit len) in MU1, HF1 by lia.
    assert (HFR1 : bytes_at rsegs m1 frame fr).
    { destruct HF1 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    step. step. step.
    eapply evt_cut.
    { eapply IR with (bs := fr). rewrite ?(unsigned_lit frame), ?(unsigned_lit len) by lia. intros _ H14.
      split; [lia | exact HFR1]. }
    intros ms' (b1' & b2' & b3' & ->).
    replace (ret_pc (Z_to_bv 64 0x12da0)) with (Z_to_bv 64 0x12da0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite ?(unsigned_lit frame), ?(unsigned_lit len) by lia.
    assert (KK : forall y10 y11 y12 y13 : word,
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x12ddc) (Z_to_bv 64 Sp) x3 x4 t0' t1' t2' x8 x9 y10 y11 y12 y13 a4' a5' a6' a7'
        (Z_to_bv 64 mode) (Z_to_bv 64 src) x20 x21 x22 x23 x24 (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12e5c) fc None m1 (seg_rom rsegs))).
    { intros y10 y11 y12 y13. apply K; [exact MU1 | exact WM1 | exact MI1 | exact HFR1]. }
    unfold is_reac_result. rewrite (proj2 (Z.eqb_neq frame 0)) by lia. cbn [orb].
    step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec len 14) as [L14|L14].
    + step. step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
      eapply en_clean; [exact ICL | lia | exact MI1 | exact KK].
    + pose proof (rd1 _ _ _ 12 HFR1 ltac:(lia)) as RD12. change (Z.to_nat 12) with 12%nat in RD12.
      step. step. step. rewrite ir_byte_eq by lia.
      unfold is_reac_byte.
      destruct (Z.eqb_spec (bv_unsigned (nth 12 fr (Z_to_bv 8 0))) 136) as [B12|B12]; cbn [negb andb].
      * pose proof (rd1 _ _ _ 13 HFR1 ltac:(lia)) as RD13. change (Z.to_nat 13) with 13%nat in RD13.
        step. step. step. rewrite ir_seqz. step.
        destruct (Z.eqb_spec (bv_unsigned (nth 13 fr (Z_to_bv 8 0))) 25) as [B13|B13]; cbn [andb].
        -- step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
           eapply en_clean; [exact ICL | lia | exact MI1 | exact KK].
        -- step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
           eapply en_clean; [exact ICL | lia | exact MI1 | exact KK].
      * step. step. iff_false ltac:(apply negb_false_iff; apply bv_eqb_refl).
        eapply en_clean; [exact ICL | lia | exact MI1 | exact KK].
Qed.

Lemma en2_eq : forall x2 x10 x18 x19 x25 : word,
  x2 = Z_to_bv 64 Sp -> x10 = Z_to_bv 64 frame -> x18 = Z_to_bv 64 mode -> x19 = Z_to_bv 64 src ->
  x25 = Z_to_bv 64 len -> en2_k ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
     x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12d74) fc None m (seg_rom rsegs)).
Proof. intros x2 x10 x18 x19 x25 -> -> -> -> -> K. exact (en2 K). Qed.

End E2.
