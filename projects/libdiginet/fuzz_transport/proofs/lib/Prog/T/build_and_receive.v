(* Walk of build_and_receive (fuzz/fuzz_transport.c:1024-1030; spec_build_frame of fuzz/spec.h inlined) in the
   plain image: 0x15be4, 412 bytes, own frame 1616 (ra, s0-s8 saved at sp + 0x600 .. 0x648, frame[] at sp + 20). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TNeed TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require KindB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c
  build_and_receive_c TSRGlue.
Import ListNotations.
Open Scope Z_scope.


(* ---- cells ---- *)

Lemma bar_firstn_rep : forall (x : byte) a b, firstn a (repeat x (a + b)) = repeat x a.
Proof. intros x a b. induction a as [|a IH]; cbn; [reflexivity | f_equal; exact IH]. Qed.

Lemma bar_skipn_rep : forall (x : byte) a b, skipn a (repeat x (a + b)) = repeat x b.
Proof. intros x a b. induction a as [|a IH]; cbn; [reflexivity | exact IH]. Qed.

(* the first cell of a run, and the rest at the address after it *)
Lemma bar_rw_cons : forall m A c cs, rw_cells rsegs m A (c :: cs) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[Hc Hwf] Hb] (W0 & W1 & Hw)]. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb as [Hb1 Hb2]. rewrite cbytes_length in Hb2 by exact Hc. cbn [cells_size] in W1, Hw.
  split.
  - split; [split; [split; [exact Hc | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact Hb1] |].
    split; [exact W0|]. cbn [cells_size]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact Hwf | exact Hb2]|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

(* a memset cell of n1 + n2 zero bytes splits in two *)
Lemma bar_cb_split : forall m A (x : byte) n1 n2, rw_cells rsegs m A [CB (n1 + n2) (repeat x (n1 + n2))] ->
  rw_cells rsegs m A [CB n1 (repeat x n1); CB n2 (repeat x n2)].
Proof.
  intros m A x n1 n2 H.
  pose proof (rw_cells_split_CB rsegs m A [] (n1 + n2) (repeat x (n1 + n2)) [] [n1; n2] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. rewrite bar_firstn_rep, bar_skipn_rep, firstn_all2 in H2 by (rewrite repeat_length; lia).
  exact H2.
Qed.

Lemma bar_rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

(* ---- bytes of a stored register ---- *)

Lemma bar_zb : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
  intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H.
Qed.

(* the byte a sb of a register writes (Lib/Step.v cell_of_bytes, its le1 case) *)
Lemma bar_b8 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof.
  intros z. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64).
  apply Z.mod_mod_divide. exists (2^56). reflexivity.
Qed.

(* the four dst bytes the code ors into a0 (0x15c3c-0x15c74), and the word they make *)
Lemma bar_val4 : forall (b0 b1 b2 b3 : byte),
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b3)) 24)))
                                        (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 16))))))
        (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8)))
                                        (bv_unsigned (zxb b0)))))
  = bv_unsigned b0 + bv_unsigned b1 * 2^8 + bv_unsigned b2 * 2^16 + bv_unsigned b3 * 2^24.
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
  unfold zxb. rewrite !(unsigned_lit (bv_unsigned b0)) by lia. rewrite !(unsigned_lit (bv_unsigned b1)) by lia.
  rewrite !(unsigned_lit (bv_unsigned b2)) by lia. rewrite !(unsigned_lit (bv_unsigned b3)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned b3 * 2 ^ 24)) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2 ^ 16)) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2 ^ 8)) by lia.
  rewrite (kb_lor_low (bv_unsigned b3 * 2 ^ 24) (bv_unsigned b2 * 2 ^ 16) 24) by (try lia; apply Z.mod_mul; lia).
  rewrite (kb_lor_low (bv_unsigned b1 * 2 ^ 8) (bv_unsigned b0) 8) by (try lia; apply Z.mod_mul; lia).
  rewrite (unsigned_lit (bv_unsigned b3 * 2 ^ 24 + bv_unsigned b2 * 2 ^ 16)) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2 ^ 8 + bv_unsigned b0)) by lia.
  rewrite (kb_lor_low (bv_unsigned b3 * 2 ^ 24 + bv_unsigned b2 * 2 ^ 16) (bv_unsigned b1 * 2 ^ 8 + bv_unsigned b0) 16)
    by (try lia; rewrite Z.add_mod by lia; rewrite !Z.mod_mul by lia; reflexivity).
  lia.
Qed.

Lemma bar_le4 : forall (b0 b1 b2 b3 : byte),
  le4 (Z_to_bv 64 (bv_unsigned b0 + bv_unsigned b1 * 2^8 + bv_unsigned b2 * 2^16 + bv_unsigned b3 * 2^24))
  = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
  unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia.
  replace ((bv_unsigned b0 + bv_unsigned b1 * 2 ^ 8 + bv_unsigned b2 * 2 ^ 16 + bv_unsigned b3 * 2 ^ 24) / 2 ^ 8)
    with (bv_unsigned b1 + bv_unsigned b2 * 2 ^ 8 + bv_unsigned b3 * 2 ^ 16) by (Z.div_mod_to_equations; lia).
  replace ((bv_unsigned b1 + bv_unsigned b2 * 2 ^ 8 + bv_unsigned b3 * 2 ^ 16) / 2 ^ 8)
    with (bv_unsigned b2 + bv_unsigned b3 * 2 ^ 8) by (Z.div_mod_to_equations; lia).
  replace ((bv_unsigned b2 + bv_unsigned b3 * 2 ^ 8) / 2 ^ 8) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
  f_equal; [apply bar_zb; Z.div_mod_to_equations; lia|].
  f_equal; [apply bar_zb; Z.div_mod_to_equations; lia|].
  f_equal; [apply bar_zb; Z.div_mod_to_equations; lia|].
  f_equal. apply bar_zb. Z.div_mod_to_equations; lia.
Qed.

Lemma bar_val2 : forall (b0 b1 : byte),
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b0))
  = bv_unsigned b0 + bv_unsigned b1 * 2^8.
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  unfold bv_modulus in R0, R1. change (2 ^ Z.of_N 8) with 256 in R0, R1.
  unfold zxb. rewrite !(unsigned_lit (bv_unsigned b0)) by lia. rewrite !(unsigned_lit (bv_unsigned b1)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b1 * 2 ^ 8)) by lia.
  rewrite (kb_lor_low (bv_unsigned b1 * 2 ^ 8) (bv_unsigned b0) 8) by (try lia; apply Z.mod_mul; lia). lia.
Qed.

Lemma bar_le2 : forall (b0 b1 : byte), le2 (Z_to_bv 64 (bv_unsigned b0 + bv_unsigned b1 * 2^8)) = [b0; b1].
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  unfold bv_modulus in R0, R1. change (2 ^ Z.of_N 8) with 256 in R0, R1.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia.
  replace ((bv_unsigned b0 + bv_unsigned b1 * 2 ^ 8) / 2 ^ 8) with (bv_unsigned b1) by (Z.div_mod_to_equations; lia).
  f_equal; [apply bar_zb; Z.div_mod_to_equations; lia|].
  f_equal. apply bar_zb. Z.div_mod_to_equations; lia.
Qed.

(* ---- the model's frame ---- *)

Lemma bar_upd_app_l : forall (X Y v : list byte) k, 0 <= k -> (Z.to_nat k + length v <= length X)%nat ->
  upd (X ++ Y) k v = upd X k v ++ Y.
Proof.
  intros X Y v k Hk HL. unfold upd.
  rewrite firstn_app, skipn_app.
  replace (Z.to_nat k - length X)%nat with 0%nat by lia.
  replace (Z.to_nat k + length v - length X)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma bar_upd_app_r : forall (X Y v : list byte) k, Z.to_nat k = length X -> (length v <= length Y)%nat ->
  upd (X ++ Y) k v = X ++ v ++ skipn (length v) Y.
Proof.
  intros X Y v k Hk HL. unfold upd.
  rewrite firstn_app, skipn_app, Hk.
  replace (length X - length X)%nat with 0%nat by lia.
  replace (length X + length v - length X)%nat with (length v) by lia.
  rewrite firstn_all. rewrite (skipn_all2 X) by lia. cbn [firstn skipn]. rewrite !app_nil_r. cbn [app]. reflexivity.
Qed.

(* the 18 header bytes spec_build_frame writes at frame[12 .. 29] *)
Definition bar_hdr (len send ack retry cmd : Z) (body : list byte) : list byte :=
  put16 34911 ++ put16 (16 + len) ++ put16 (spec_sum body) ++ put32 send ++ put32 ack ++ put16 retry
  ++ [b8 cmd; b8 1].

Lemma bar_frame_shape : forall (d0 d1 d2 d3 d4 d5 : byte) (src body : list byte) (send ack retry cmd : Z),
  length src = 6%nat -> Z.of_nat (length body) <= 1484 ->
  fst (spec_build_frame [d0;d1;d2;d3;d4;d5] src send ack retry cmd 1 body 0) =
  [d0;d1;d2;d3;d4;d5] ++ src ++ bar_hdr (Z.of_nat (length body)) send ack retry cmd body ++ body
    ++ repeat (b8 0) (Z.to_nat (Z.max 30 (Z.of_nat (length body)) - Z.of_nat (length body))).
Proof.
  intros d0 d1 d2 d3 d4 d5 src body send ack retry cmd LS HL.
  destruct src as [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|? ?]]]]]]]; try discriminate LS.
  unfold spec_build_frame. cbv zeta. cbn [fst].
  set (L := Z.of_nat (length body)) in *.
  assert (LL : Z.to_nat L = length body) by (unfold L; lia).
  replace (Z.to_nat (if 30 + L <? 60 then 60 else 30 + L))
    with (30 + (Z.to_nat L + Z.to_nat (Z.max 30 L - L)))%nat
    by (destruct (Z.ltb_spec (30 + L) 60); lia).
  rewrite !repeat_app.
  replace ((16 + L) mod 2 ^ 32) with (16 + L) by (symmetry; apply Z.mod_small; unfold L; lia).
  change (if 0 =? 0 then spec_sum body else 0) with (spec_sum body).
  unfold upd, bar_hdr.
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 6) with 6%nat. change (Z.to_nat 12) with 12%nat.
  change (Z.to_nat 14) with 14%nat. change (Z.to_nat 16) with 16%nat. change (Z.to_nat 18) with 18%nat.
  change (Z.to_nat 22) with 22%nat. change (Z.to_nat 26) with 26%nat. change (Z.to_nat 28) with 28%nat.
  change (Z.to_nat 29) with 29%nat. change (Z.to_nat 30) with 30%nat.
  cbn [repeat firstn skipn app length Nat.add put16 put32].
  assert (ER : skipn (length body) (repeat (b8 0) (Z.to_nat L) ++ repeat (b8 0) (Z.to_nat (Z.max 30 L - L)))
             = repeat (b8 0) (Z.to_nat (Z.max 30 L - L))).
  { rewrite skipn_app, repeat_length, LL, Nat.sub_diag.
    rewrite skipn_all2 by (rewrite repeat_length; lia). reflexivity. }
  destruct (Z.eqb_spec L 0) as [E|E].
  - assert (Eb : body = []) by (apply length_zero_iff_nil; lia).
    rewrite Eb. rewrite E. change (Z.to_nat 0) with 0%nat. cbn [repeat app]. reflexivity.
  - rewrite skipn_0, ER. reflexivity.
Qed.

(* ---- the body sum ---- *)

Lemma bar_sum_firstn : forall (l : list byte) n b, nth_error l n = Some b ->
  sum_bytes (firstn (S n) l) = sum_bytes (firstn n l) + bz b.
Proof.
  induction l as [|x l IH]; intros [|n] b H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. cbn [firstn sum_bytes]. rewrite firstn_O. cbn [sum_bytes]. lia.
  - cbn [firstn sum_bytes]. rewrite (IH n b H). lia.
Qed.

Lemma bar_sum_range : forall l, 0 <= sum_bytes l <= 255 * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; cbn [sum_bytes length]; [lia|].
  pose proof (bz_range x). lia.
Qed.

Lemma bar_sum_firstn_range : forall l n, 0 <= sum_bytes (firstn n l) <= 255 * Z.of_nat (length l).
Proof.
  intros l n. pose proof (bar_sum_range (firstn n l)) as H.
  pose proof (length_firstn n l) as H3. lia.
Qed.

Lemma bar_firstn1_skipn : forall (l : list byte) n b, nth_error l n = Some b -> firstn 1 (skipn n l) = [b].
Proof.
  induction l as [|x l IH]; intros [|n] b H; cbn [nth_error skipn] in *; try discriminate.
  - injection H as <-. reflexivity.
  - apply IH. exact H.
Qed.

Lemma bar_eqb_le : forall a b, 0 < a <= 2 ^ 64 -> 0 < b <= 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  destruct (Z.eq_dec a (2 ^ 64)) as [A|A]; destruct (Z.eq_dec b (2 ^ 64)) as [B|B].
  - lia.
  - rewrite A, Z.mod_same in E by lia. rewrite (Z.mod_small b) in E by lia. lia.
  - rewrite B, Z.mod_same in E by lia. rewrite (Z.mod_small a) in E by lia. lia.
  - rewrite !Z.mod_small in E by lia. lia.
Qed.
Lemma bar_b8_eq : forall x y, x mod 256 = y mod 256 -> b8 x = b8 y.
Proof.
  intros x y H. unfold b8. apply bar_zb. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. exact H.
Qed.

(* the byte at bit 8j of a register holding x is the model's byte of x cut to w bits (j + 8 <= w) *)
Lemma bar_b8_modw : forall x y j w, 0 <= j -> j + 8 <= w -> x mod 2 ^ w = y -> b8 (x / 2 ^ j) = b8 (y / 2 ^ j).
Proof.
  intros x y j w Hj Hjw Hxy. apply bar_b8_eq.
  assert (Hw : 0 < 2 ^ w) by (apply Z.pow_pos_nonneg; lia).
  assert (Hj0 : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hs1 : 2 ^ w = 2 ^ (w - j) * 2 ^ j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hs2 : 2 ^ (w - j) = 2 ^ (w - j - 8) * 256)
    by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Ex : x = y + (2 ^ (w - j) * (x / 2 ^ w)) * 2 ^ j)
    by (pose proof (Z.mod_eq x (2 ^ w) ltac:(lia)); rewrite Hxy in *; nia).
  rewrite Ex at 1. rewrite Z.div_add by lia.
  replace (2 ^ (w - j) * (x / 2 ^ w)) with ((2 ^ (w - j - 8) * (x / 2 ^ w)) * 256) by nia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma bar_hdr_bytes : forall (aw bw : word) (len send ack retry cmd sm : Z),
  bv_unsigned aw mod 2 ^ 32 = send -> 0 <= send < 2 ^ 16 ->
  bv_unsigned bw mod 2 ^ 32 = ack -> 0 <= ack < 2 ^ 32 ->
  0 <= retry < 2 ^ 8 -> 0 <= cmd < 2 ^ 8 -> 0 <= len <= 1484 -> 0 <= sm < 2 ^ 64 ->
  cells_bytes
    [C2 (Z_to_bv 64 24456);
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (len + 16))) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (len + 16))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 sm)) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 sm)));
     C2 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned aw) 8))));
     C1 (Z_to_bv 8 (bv_unsigned aw));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned bw) 24))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned bw) 16))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned bw) 8))));
     C1 (Z_to_bv 8 (bv_unsigned bw));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 retry)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 cmd)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1)))]
  = put16 34911 ++ put16 (16 + len) ++ put16 (sm mod 2 ^ 16) ++ put32 send ++ put32 ack ++ put16 retry
    ++ [b8 cmd; b8 1].
Proof.
  intros aw bw len send ack retry cmd sm HA HS HB HK HR HC HL HM.
  pose proof (bv_unsigned_in_range 64 aw) as Ra. pose proof (bv_unsigned_in_range 64 bw) as Rb.
  unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra, Rb.
  rewrite !(unsigned_lit (len + 16)) by lia. rewrite !(unsigned_lit sm) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !bar_b8.
  unfold put16, put32, cells_bytes, cbytes, le2.
  rewrite !(unsigned_lit 24456) by lia. rewrite !(unsigned_lit 0) by lia.
  cbn [Z_to_le_bytes app].
  change (Z_to_bv 8 (len + 16)) with (b8 (len + 16)). change (Z_to_bv 8 sm) with (b8 sm).
  change (Z_to_bv 8 (bv_unsigned aw)) with (b8 (bv_unsigned aw)).
  change (Z_to_bv 8 (bv_unsigned bw)) with (b8 (bv_unsigned bw)).
  change (Z_to_bv 8 24456) with (b8 24456). change (Z_to_bv 8 (Z.shiftr 24456 8)) with (b8 (24456 / 2 ^ 8)).
  change (Z_to_bv 8 0) with (b8 0). change (Z_to_bv 8 (Z.shiftr 0 8)) with (b8 0).
  f_equal; [apply bar_b8_eq; reflexivity|].
  f_equal; [apply bar_b8_eq; reflexivity|].
  f_equal; [f_equal; lia|].
  f_equal; [f_equal; lia|].
  f_equal; [apply (bar_b8_modw sm (sm mod 2 ^ 16) 8 16); [lia | lia | reflexivity]|].
  f_equal; [apply bar_b8_eq; symmetry; apply Z.mod_mod_divide; exists (2 ^ 8); reflexivity|].
  f_equal; [apply bar_b8_eq; rewrite (Z.div_small send (2 ^ 24)) by lia; reflexivity|].
  f_equal; [apply bar_b8_eq; rewrite (Z.div_small send (2 ^ 16)) by lia; reflexivity|].
  f_equal; [apply (bar_b8_modw (bv_unsigned aw) send 8 32); [lia | lia | exact HA]|].
  f_equal; [apply bar_b8_eq; rewrite <- HA; symmetry; apply Z.mod_mod_divide; exists (2 ^ 24); reflexivity|].
  f_equal; [apply (bar_b8_modw (bv_unsigned bw) ack 24 32); [lia | lia | exact HB]|].
  f_equal; [apply (bar_b8_modw (bv_unsigned bw) ack 16 32); [lia | lia | exact HB]|].
  f_equal; [apply (bar_b8_modw (bv_unsigned bw) ack 8 32); [lia | lia | exact HB]|].
  f_equal; [apply bar_b8_eq; rewrite <- HB; symmetry; apply Z.mod_mod_divide; exists (2 ^ 24); reflexivity|].
  f_equal. apply bar_b8_eq. rewrite (Z.div_small retry (2 ^ 8)) by lia. reflexivity.
Qed.

Lemma bar_hdr_len : forall l s a r c b, length (bar_hdr l s a r c b) = 18%nat.
Proof. intros. unfold bar_hdr, put16, put32. cbn [length app Z_to_le_bytes]. reflexivity. Qed.

Lemma bar_split8 : forall m A (u : word) r, bytes_at rsegs m A (le8 u ++ r) ->
  bytes_at rsegs m A (le8 u) /\ bytes_at rsegs m (A + 8) r.
Proof.
  intros m A u r H. apply bytes_at_app in H as [H1 H2]. rewrite length_le8 in H2.
  change (Z.of_nat 8) with 8 in H2. split; [exact H1 | exact H2].
Qed.
Lemma bar_rd8 : forall m A (v : word), bytes_at rsegs m A (le8 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) 8 = Some (le8 v).
Proof.
  intros m A v H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite length_le8 in B.
  pose proof (bytes_at_read rsegs m A (le8 v) 0 8 H ltac:(lia) ltac:(rewrite length_le8; lia)) as R.
  replace (A + 0) with A in R by lia.
  change (Z.to_nat 0) with 0%nat in R. rewrite skipn_O, firstn_all2 in R by (rewrite length_le8; lia).
  exact R.
Qed.


Definition bar_frame (dst src : list byte) (send ack retry cmd : Z) (body : list byte) : list byte :=
  fst (spec_build_frame dst src send ack retry cmd 1 body 0).

Definition bar_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (frame : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x15d50) (Z_to_bv 64 (bv_unsigned sp - 1616)) gp tp t0' t1' t2' s0' s1'
                  (Z_to_bv 64 (bv_unsigned sp - 1596)) (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 0)
                  (Z_to_bv 64 0) a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 receive_ENTRY) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 1616, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' (bv_unsigned sp - 1596) frame /\
    bytes_at rsegs m' (bv_unsigned sp - 80)
      (le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra).


Lemma bar_walk : memset_contract -> memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (D S P : Z) (dst src body : list byte) (send ack retry cmd : Z),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S ->
  bv_unsigned a2 mod 2 ^ 32 = send -> 0 <= send < 2 ^ 16 ->
  bv_unsigned a3 mod 2 ^ 32 = ack -> 0 <= ack < 2 ^ 32 ->
  a4 = Z_to_bv 64 retry -> 0 <= retry < 2 ^ 8 ->
  a5 = Z_to_bv 64 cmd -> 0 <= cmd < 2 ^ 8 ->
  a6 = Z_to_bv 64 P -> a7 = Z_to_bv 64 (Z.of_nat (length body)) ->
  Z.of_nat (length body) <= 1484 ->
  length dst = 6%nat -> bytes_at rsegs m D dst -> D + 6 <= 2 ^ 20 ->
  length src = 6%nat -> bytes_at rsegs m S src -> S + 6 <= 2 ^ 20 ->
  bytes_at rsegs m P body ->
  (Z.of_nat (length body) = 0 \/ P + Z.of_nat (length body) <= bv_unsigned sp - 1616 \/ bv_unsigned sp <= P) ->
  bv_unsigned sp mod 16 = 0 -> 2 ^ 20 + 1616 <= bv_unsigned sp < 2 ^ 63 ->
  stk rsegs m (bv_unsigned sp - 1616) (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs (bar_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (bar_frame dst src send ack retry cmd body))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 build_and_receive_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros MSET MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m D S P dst src body send ack retry cmd -> -> HA2 Hsend HA3 Hack -> Hretry -> Hcmd -> -> Hlen
    LD HD RD LS HS RS HP DP SP16 RSP ST MI.
  unfold memset_contract, MEMSET in MSET. unfold memcpy_contract in MCPY.
  unfold build_and_receive_ENTRY.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (munch_refl [(bv_unsigned sp - 1616, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.

  set (len := Z.of_nat (length body)) in *.
  assert (Len0 : 0 <= len) by (unfold len; lia).
  assert (HPb : exists Pb, bytes_at rsegs m Pb body /\ (Pb + len <= bv_unsigned sp - 1616 \/ bv_unsigned sp <= Pb) /\
                  (len <> 0 -> Pb = P)).
  { destruct (Z.eq_dec len 0) as [E|E].
    - exists 0. destruct body as [|? ?]; [|cbn in E; unfold len in E; cbn in E; lia].
      split; [apply bytes_at_nil; lia | split; [lia | intros N; lia]].
    - exists P. split; [exact HP | split; [lia | reflexivity]]. }
  destruct HPb as (Pb & HPb & DPb & EPb). clear HP DP.
  set (s8v := Z.max 30 len).
  assert (Rs8 : 30 <= s8v <= 1484) by (unfold s8v; lia).
  carve_frame 80%nat ST. rename FR into FRs.
  carve_frame 2%nat ST. rename FR into FRp.
  destruct (stk_carve rsegs m _ _ (Z.to_nat (1484 - s8v)) ST ltac:(lia)) as [ST2 [jt FRt]]. clear ST. rename ST2 into ST.
  destruct (stk_carve rsegs m _ _ (Z.to_nat (s8v + 18)) ST ltac:(lia)) as [ST2 [jm FRm]]. clear ST. rename ST2 into ST.
  destruct (stk_carve rsegs m _ _ 6 ST ltac:(lia)) as [ST2 [js FRsrc]]. clear ST. rename ST2 into ST.
  destruct (stk_carve rsegs m _ _ 6 ST ltac:(lia)) as [ST2 [jd FRdst]]. clear ST. rename ST2 into ST.
  replace (bv_unsigned sp + -82 - Z.of_nat (Z.to_nat (1484 - s8v)) - Z.of_nat (Z.to_nat (s8v + 18)) - Z.of_nat 6 - Z.of_nat 6) with (bv_unsigned sp + -1596) in FRdst, ST by lia.
  replace (bv_unsigned sp + -82 - Z.of_nat (Z.to_nat (1484 - s8v)) - Z.of_nat (Z.to_nat (s8v + 18)) - Z.of_nat 6) with (bv_unsigned sp + -1590) in FRsrc by lia.
  replace (bv_unsigned sp + -82 - Z.of_nat (Z.to_nat (1484 - s8v)) - Z.of_nat (Z.to_nat (s8v + 18))) with (bv_unsigned sp + -1584) in FRm by lia.
  replace (bv_unsigned sp + -82 - Z.of_nat (Z.to_nat (1484 - s8v))) with (bv_unsigned sp + -1566 + s8v) in FRt by lia.
  pose proof (bytes_at_bound _ _ _ _ HD) as BD.
  pose proof (bytes_at_bound _ _ _ _ HS) as BS.
  pose proof (bytes_at_bound _ _ _ _ HPb) as BP.
  do 21 step.
  assert (K1 : forall q11 q24 : word, q24 = Z_to_bv 64 s8v ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 P)
        (Z_to_bv 64 D) q11 a2 a3 (Z_to_bv 64 retry) (Z_to_bv 64 cmd) (Z_to_bv 64 P) (Z_to_bv 64 len)
        a2 (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 (Z_to_bv 64 S) s7 q24 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 89148) fc None m1 (seg_rom rsegs))).
  2: destruct (Z.ltb_spec 30 len) as [L30|L30]; [replace (bv_ltu (Z_to_bv 64 30) (Z_to_bv 64 len)) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia); cbv iota; apply K1; unfold s8v; f_equal; lia | replace (bv_ltu (Z_to_bv 64 30) (Z_to_bv 64 len)) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia); cbv iota; step; apply K1; unfold s8v; f_equal; lia].
  intros q11 q24 ->.
  destruct dst as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 [|? ?]]]]]]]; try discriminate LD.
  pose proof (bytes_at_read rsegs m1 D [d0; d1; d2; d3; d4; d5] 5 1 HD ltac:(lia) ltac:(cbn; lia)) as RD5.
  pose proof (bytes_at_read rsegs m1 D [d0; d1; d2; d3; d4; d5] 4 1 HD ltac:(lia) ltac:(cbn; lia)) as RD4.
  pose proof (bytes_at_read rsegs m1 D [d0; d1; d2; d3; d4; d5] 0 1 HD ltac:(lia) ltac:(cbn; lia)) as RD0.
  pose proof (bytes_at_read rsegs m1 D [d0; d1; d2; d3; d4; d5] 1 1 HD ltac:(lia) ltac:(cbn; lia)) as RD1.
  pose proof (bytes_at_read rsegs m1 D [d0; d1; d2; d3; d4; d5] 2 1 HD ltac:(lia) ltac:(cbn; lia)) as RD2.
  pose proof (bytes_at_read rsegs m1 D [d0; d1; d2; d3; d4; d5] 3 1 HD ltac:(lia) ltac:(cbn; lia)) as RD3.
  change (Z.to_nat 5) with 5%nat in RD5. change (Z.to_nat 4) with 4%nat in RD4. change (Z.to_nat 0) with 0%nat in RD0.
  change (Z.to_nat 1) with 1%nat in RD1. change (Z.to_nat 2) with 2%nat in RD2. change (Z.to_nat 3) with 3%nat in RD3.
  cbn [firstn skipn] in RD0, RD1, RD2, RD3, RD4, RD5.
  clear HD.
  do 21 step.
  assert (Ua0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1584)) = bv_unsigned sp + -1584) by (apply unsigned_lit; lia).
  assert (Ua2 : bv_unsigned (Z_to_bv 64 (s8v + 18)) = s8v + 18) by (apply unsigned_lit; lia).

  eapply evt_cut; [eapply MSET; [rewrite Ua0, Ua2; exact FRm | exact MI] | ].
  intros ms' PO. unfold memset_post in PO. destruct_exs PO. destruct PO as [Ems [MUc [WMc [MIc FRc]]]]. subst ms'.
  rewrite Ua0, Ua2 in MUc, FRc.

  transport_after_call rsegs m2 x13 MUc WMc.
  clear MUc WMc MI. rename MIc into MI.
  rewrite (ret_pc_even 89232) by (first [lia | reflexivity]).
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (b8 0) in FRc.
  replace (Z.to_nat (s8v + 18)) with (18 + (Z.to_nat len + Z.to_nat (s8v - len)))%nat in FRc by lia.
  apply bar_cb_split in FRc. apply bar_rw_cons in FRc as [FRh FRc]. cbn [csize] in FRc.
  apply bar_cb_split in FRc. apply bar_rw_cons in FRc as [FRb FRz]. cbn [csize] in FRz.
  replace (bv_unsigned sp + -1584 + Z.of_nat 18) with (bv_unsigned sp + -1566) in FRb, FRz by lia.
  replace (bv_unsigned sp + -1566 + Z.of_nat (Z.to_nat len)) with (bv_unsigned sp + -1566 + len) in FRz by lia.

  clear Ua0 Ua2 RD0 RD1 RD2 RD3 RD4 RD5 jm.
  do 4 step.
  assert (Ub0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1590)) = bv_unsigned sp + -1590) by (apply unsigned_lit; lia).
  assert (Ub1 : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (Ub2 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evt_cut; [eapply MCPY with (src := src); [rewrite Ub1; exact HS | rewrite Ub2, LS; reflexivity | rewrite Ub0, Ub2; exact FRsrc | rewrite Ub0, Ub1, Ub2; lia | exact MI] | ].
  intros ms' PO. unfold memcpy_post in PO. destruct_exs PO. destruct PO as [Ems [MUc [WMc [MIc [FRc HSc]]]]]. subst ms'.
  rewrite Ub0, Ub2 in MUc, FRc. rewrite Ub1 in HSc. clear HS.

  transport_after_call rsegs x13 x28 MUc WMc.
  clear MUc WMc MI Ub0 Ub1 Ub2. rename MIc into MI. rename FRc into FRsrc. rename HSc into HS.
  rewrite (ret_pc_even 89248) by (first [lia | reflexivity]).
  do 8 step.

  enough (K2 : forall q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word,
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp q5 q6 q7
        (Z_to_bv 64 len) (Z_to_bv 64 P) (Z_to_bv 64 (sum_bytes body)) q11 q12 q13 q14 q15 q16 q17
        a2 (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 (Z_to_bv 64 S)
        (Z_to_bv 64 (bv_unsigned sp + -1590)) (Z_to_bv 64 s8v) s9 s10 s11 q28 q29 q30 q31)
      F (Z_to_bv 64 89308) fc None m0 (seg_rom rsegs))).
  step.
  replace (bv_eqb (Z_to_bv 64 len) (Z_to_bv 64 0)) with (len =? 0)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; reflexivity).
  destruct (Z.eqb_spec len 0) as [E0|E0]; cbv iota.
  { assert (Eb : body = []) by (apply length_zero_iff_nil; unfold len in E0; lia).
    rewrite Eb in K2. cbn [sum_bytes] in K2. apply K2. }
  rewrite (EPb E0) in HPb, BP, DPb.
  do 2 step.

  assert (LOOP : forall (k : nat) (i sm pi : Z) (q1 q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
    Z.of_nat k = len - i -> 0 <= i < len -> sm = sum_bytes (firstn (Z.to_nat i) body) -> pi = P + i ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp q5 q6 q7
        (Z_to_bv 64 len) (Z_to_bv 64 P) (Z_to_bv 64 sm) (Z_to_bv 64 (P + len)) (Z_to_bv 64 pi) q13 q14 q15 q16 q17
        a2 (Z_to_bv 64 cmd) (Z_to_bv 64 retry) a3 (Z_to_bv 64 S)
        (Z_to_bv 64 (bv_unsigned sp + -1590)) (Z_to_bv 64 s8v) s9 s10 s11 q28 q29 q30 q31)
      F (Z_to_bv 64 89292) fc None m0 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i sm pi q1 q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 Hk Hi Esm Epi; [lia|].
    subst sm pi.
    destruct (nth_error body (Z.to_nat i)) as [bi|] eqn:Ebi; [|apply nth_error_None in Ebi; lia].
    pose proof (bytes_at_read rsegs m0 P body i 1 HPb ltac:(lia) ltac:(lia)) as RDi.
    rewrite (bar_firstn1_skipn body (Z.to_nat i) bi Ebi) in RDi.
    pose proof (bar_sum_firstn_range body (Z.to_nat i)) as SR.
    pose proof (bz_range bi) as RB.
    do 4 step.
    assert (BQ : 0 < P + i + 1 <= 2 ^ 64) by lia.
    assert (BL : 0 < P + len <= 2 ^ 64) by lia.
    rewrite (bar_eqb_le (P + i + 1) (P + len) ltac:(lia) ltac:(lia)).
    rewrite kb_unsigned_zxb.
    destruct (Z.eqb_spec (P + i + 1) (P + len)) as [EQ|NE]; cbn [negb]; cbv iota.
    - assert (ESUM : sum_bytes (firstn (Z.to_nat i) body) + bv_unsigned bi = sum_bytes body).
      { change (bv_unsigned bi) with (bz bi). rewrite <- (bar_sum_firstn body (Z.to_nat i) bi Ebi).
        rewrite firstn_all2 by lia. reflexivity. }
      rewrite ESUM. apply K2.
    - apply (IH (i + 1) (sum_bytes (firstn (Z.to_nat i) body) + bv_unsigned bi) (P + i + 1)); try lia.
      change (bv_unsigned bi) with (bz bi). replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia.
      rewrite (bar_sum_firstn body (Z.to_nat i) bi Ebi). reflexivity. }
  apply (LOOP (Z.to_nat len) 0 0 P); try lia.
  change (Z.to_nat 0) with 0%nat. rewrite firstn_O. reflexivity.

  intros r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31.
  do 19 step.
  rewrite (bar_val4 d0 d1 d2 d3), (bar_val2 d4 d5) in FRdst.
  apply bar_rw_bytes in FRdst. cbn [cells_bytes cbytes] in FRdst.
  rewrite bar_le4, bar_le2, app_nil_r in FRdst. cbn [app] in FRdst.
  apply bar_rw_bytes in FRsrc. cbn [cells_bytes cbytes] in FRsrc. rewrite app_nil_r in FRsrc.
  apply bar_rw_bytes in FRz. cbn [cells_bytes cbytes] in FRz. rewrite app_nil_r in FRz.
  pose proof (bar_sum_range body) as SRB.

  enough (K3 : forall (m4 : word -> option byte)
      (u1 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u28 u29 u30 u31 : word),
    munch [(bv_unsigned sp - 1616, bv_unsigned sp)] m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
    bytes_at rsegs m4 (bv_unsigned sp + -1596) [d0; d1; d2; d3; d4; d5] ->
    bytes_at rsegs m4 (bv_unsigned sp + -1590) src ->
    bytes_at rsegs m4 (bv_unsigned sp + -1584) (bar_hdr len send ack retry cmd body) ->
    bytes_at rsegs m4 (bv_unsigned sp + -1566) body ->
    bytes_at rsegs m4 (bv_unsigned sp + -1566 + len) (repeat (b8 0) (Z.to_nat (s8v - len))) ->
    rw_cells rsegs m4 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs QQ (MS (mkR u1 (Z_to_bv 64 (bv_unsigned sp + -1616)) gp tp u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17
        u18 u19 u20 u21 u22 u23 (Z_to_bv 64 s8v) s9 s10 s11 u28 u29 u30 u31)
      F (Z_to_bv 64 89404) fc None m4 (seg_rom rsegs))).
  step.
  replace (bv_eqb (Z_to_bv 64 len) (Z_to_bv 64 0)) with (len =? 0)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; reflexivity).
  destruct (Z.eqb_spec len 0) as [E1|E1]; cbv iota.
  {
  apply bar_rw_bytes in FRh.
  rewrite (bar_hdr_bytes a2 a3 len send ack retry cmd (sum_bytes body) HA2 Hsend HA3 Hack Hretry Hcmd
             ltac:(lia) ltac:(lia)) in FRh.
  replace (sum_bytes body mod 2 ^ 16) with (spec_sum body) in FRh by (rewrite spec_sum_eq; reflexivity).
  fold (bar_hdr len send ack retry cmd body) in FRh.
    assert (Eb : body = []) by (apply length_zero_iff_nil; unfold len in E1; lia).
    apply bar_rw_bytes in FRb. cbn [cells_bytes cbytes] in FRb.
    rewrite E1 in FRb. change (Z.to_nat 0) with 0%nat in FRb. cbn [repeat app] in FRb.
    rewrite <- Eb in FRb.
    apply (K3 m3); assumption. }
  rewrite (EPb E1) in HPb, BP, DPb.
  do 4 step.
  assert (Uc0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1566)) = bv_unsigned sp + -1566) by (apply unsigned_lit; lia).
  assert (Uc1 : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (Uc2 : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  eapply evt_cut; [eapply MCPY with (src := body);
    [rewrite Uc1; exact HPb | rewrite Uc2; lia | rewrite Uc0, Uc2; exact FRb | rewrite Uc0, Uc1, Uc2; lia | exact MI] | ].
  intros ms' PO. unfold memcpy_post in PO. destruct_exs PO.
  destruct PO as [Ems [MUd [WMd [MId [FRd HSd]]]]]. subst ms'.
  rewrite Uc0, Uc2 in MUd, FRd.
  transport_after_call rsegs m3 x42 MUd WMd.

  clear MUd WMd MI. rename MId into MI.
  rewrite (ret_pc_even 89404) by (first [lia | reflexivity]).
  apply bar_rw_bytes in FRd. cbn [cells_bytes cbytes] in FRd. rewrite app_nil_r in FRd.

  apply bar_rw_bytes in FRh.
  rewrite (bar_hdr_bytes a2 a3 len send ack retry cmd (sum_bytes body) HA2 Hsend HA3 Hack Hretry Hcmd
             ltac:(lia) ltac:(lia)) in FRh.
  replace (sum_bytes body mod 2 ^ 16) with (spec_sum body) in FRh by (rewrite spec_sum_eq; reflexivity).
  fold (bar_hdr len send ack retry cmd body) in FRh.
  apply (K3 x42); assumption.

  intros m4 u1 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u28 u29 u30 u31
    HMU HWM HMI HD HSR HH HB HZ HSV.
  do 5 step.
  apply bar_rw_bytes in HSV. cbn [cells_bytes cbytes] in HSV. rewrite app_nil_r in HSV.
  assert (LFR : Z.of_nat (length (bar_frame [d0;d1;d2;d3;d4;d5] src send ack retry cmd body)) = s8v + 30).
  { unfold bar_frame. rewrite (bar_frame_shape d0 d1 d2 d3 d4 d5 src body send ack retry cmd LS Hlen).
    rewrite !app_length, repeat_length, LS,
      (bar_hdr_len (Z.of_nat (length body)) send ack retry cmd body).
    cbn [length]. unfold s8v, len. lia. }
  assert (HFR : bytes_at rsegs m4 (bv_unsigned sp + -1596)
                  (bar_frame [d0;d1;d2;d3;d4;d5] src send ack retry cmd body)).
  { unfold bar_frame. rewrite (bar_frame_shape d0 d1 d2 d3 d4 d5 src body send ack retry cmd LS Hlen).
    apply bytes_at_app. split; [exact HD|]. cbn [length].
    replace (bv_unsigned sp + -1596 + Z.of_nat 6) with (bv_unsigned sp + -1590) by lia.
    apply bytes_at_app. split; [exact HSR|]. rewrite LS.
    replace (bv_unsigned sp + -1590 + Z.of_nat 6) with (bv_unsigned sp + -1584) by lia.
    apply bytes_at_app. split; [exact HH|].
    rewrite (bar_hdr_len (Z.of_nat (length body)) send ack retry cmd body).
    replace (bv_unsigned sp + -1584 + Z.of_nat 18) with (bv_unsigned sp + -1566) by lia.
    apply bytes_at_app. split; [exact HB|].
    replace (bv_unsigned sp + -1566 + Z.of_nat (length body)) with (bv_unsigned sp + -1566 + len) by (unfold len; lia).
    exact HZ. }
  apply evt_done. unfold QQ, bar_q. rewrite LFR.
  do 21 eexists. split; [reflexivity|].
  split; [exact HMU|]. split; [exact HWM|]. split; [exact HMI|].
  split; [exact HFR | exact HSV].
Qed.

Lemma bar_epi : forall (ra0 sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v28 v29 v30 v31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  bytes_at rsegs m (bv_unsigned sp0 - 80)
    (le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra0) ->
  2 ^ 20 + 1616 <= bv_unsigned sp0 < 2 ^ 63 ->
  Q (MS (mkR ra0 sp0 gp tp v5 v6 v7 s0 s1 v10 v11 v12 v13 v14 v15 v16 v17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           v28 v29 v30 v31)
       F (ret_pc ra0) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp0 - 1616)) gp tp v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
        v18 v19 v20 v21 v22 v23 v24 s9 s10 s11 v28 v29 v30 v31)
      F (Z_to_bv 64 89424) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v28 v29 v30 v31 F fc m Q HB HSP HQ.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  rewrite !app_length, !length_le8 in BB. cbn [Nat.add] in BB.
  apply bar_split8 in HB as [R8 HB]. replace (bv_unsigned sp0 - 80 + 8) with (bv_unsigned sp0 - 72) in HB by lia.
  apply bar_split8 in HB as [R7 HB]. replace (bv_unsigned sp0 - 72 + 8) with (bv_unsigned sp0 - 64) in HB by lia.
  apply bar_split8 in HB as [R6 HB]. replace (bv_unsigned sp0 - 64 + 8) with (bv_unsigned sp0 - 56) in HB by lia.
  apply bar_split8 in HB as [R5 HB]. replace (bv_unsigned sp0 - 56 + 8) with (bv_unsigned sp0 - 48) in HB by lia.
  apply bar_split8 in HB as [R4 HB]. replace (bv_unsigned sp0 - 48 + 8) with (bv_unsigned sp0 - 40) in HB by lia.
  apply bar_split8 in HB as [R3 HB]. replace (bv_unsigned sp0 - 40 + 8) with (bv_unsigned sp0 - 32) in HB by lia.
  apply bar_split8 in HB as [R2 HB]. replace (bv_unsigned sp0 - 32 + 8) with (bv_unsigned sp0 - 24) in HB by lia.
  apply bar_split8 in HB as [R1 HB]. replace (bv_unsigned sp0 - 24 + 8) with (bv_unsigned sp0 - 16) in HB by lia.
  apply bar_split8 in HB as [R0 HRA]. replace (bv_unsigned sp0 - 16 + 8) with (bv_unsigned sp0 - 8) in HRA by lia.
  pose proof (bar_rd8 m _ _ R8) as D8. pose proof (bar_rd8 m _ _ R7) as D7.
  pose proof (bar_rd8 m _ _ R6) as D6. pose proof (bar_rd8 m _ _ R5) as D5.
  pose proof (bar_rd8 m _ _ R4) as D4. pose proof (bar_rd8 m _ _ R3) as D3.
  pose proof (bar_rd8 m _ _ R2) as D2. pose proof (bar_rd8 m _ _ R1) as D1.
  pose proof (bar_rd8 m _ _ R0) as D0. pose proof (bar_rd8 m _ _ HRA) as DRA.
  do 12 step.
  replace (bv_unsigned sp0 - 1616 + 1616) with (bv_unsigned sp0) by lia.
  rewrite Z_to_bv_bv_unsigned.
  apply evt_done. exact HQ.
Qed.


Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Theorem build_and_receive_holds :
  memset_contract -> memcpy_contract -> receive_contract B API -> build_and_receive_contract B API.
Proof.
  intros MSET MCPY RECV.
  unfold build_and_receive_contract.
  intros BI L A regs mem md b Bw dstp srcp bodyp dst src body send ack retry cmd HPRE HFRM HARGS HROOM.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HGUARD & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  pose proof HPRE as (HCP & HID & HHALT & HLAZY & HRO & HRES & HWOFF & HWM & HGF & HRELRO).

  pose proof HCP as (HMR & HWF & HBD & HRET & HSP16 & HSPLO & HSPHI & HWIN & HTP & HERRW & HAUX).
  rewrite SEGS in HRO, HWIN, HERRW.
  pose proof YM05.alloc_ceiling_value as HAC.
  unfold build_and_receive_FRAME, receive_FRAME, ALLOC_STACK in *.
  assert (HSTK : Frame.stk rsegs (normalize rsegs mem) (spZ regs - 1616) (spZ regs)).
  { apply (norm_stk B SEGS mem); [exact HRO | unfold SR_RES_TOP; lia | lia |].
    intros a Ha. rewrite SEGS. apply HWIN. lia. }
  assert (HMI : Mem.mem_inv rsegs (normalize rsegs mem)) by apply mem_inv_normalize.
  assert (HRELN : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact HRO).

  assert (BLK : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> blk_data B mem a bs ->
                 bytes_at rsegs (normalize rsegs mem) a bs).
  { intros a bs H0 H1 HD. apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HRELN)).
    split; [exact H0|]. split; [exact H1|]. intros i Hi.
    pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity. }
  assert (ROLOW : forall x, Mem.ro_addr rsegs (Z_to_bv 64 x) = true -> 0 <= x mod 2 ^ 64 < SR_RES_TOP).
  { intros x E. unfold Mem.ro_addr in E. rewrite unsigned_lit_wrap in E.
    destruct (find_segment rsegs (x mod 2 ^ 64) 1) as [seg|] eqn:Fseg; [|discriminate E].
    exact (sr_in_img_top B _ SEGS (sr_find_img B (x mod 2 ^ 64) seg SEGS Fseg)). }
  assert (MOD : forall a bs, blk_data B mem a bs -> blk_data B mem (a mod 2 ^ 64) bs).
  { intros a bs HD i Hi. rewrite <- (HD i Hi). unfold mbyte.
    assert (EQ : Z_to_bv 64 (a mod 2 ^ 64 + i) = Z_to_bv 64 (a + i)).
    { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Zplus_mod (a mod 2 ^ 64) i), Zmod_mod, <- Zplus_mod. reflexivity. }
    rewrite EQ. reflexivity. }

  pose proof HARGS as (HA10 & HMACD & HA11 & HMACS & HA12 & HSEND & HA13 & HACK & HA14 & HRETRY
    & HA15 & HCMD & HA16 & HA17 & HBODY & HSRC & HMODEL).
  pose proof HMACD as (LD6 & HDBLK & HDRO). pose proof HMACS as (LS6 & HSBLK & HSRO).
  assert (HLEN : Z.of_nat (length body) <= 1484).
  { pose proof (HMODEL 1 ltac:(unfold h_addr_ok; lia)) as HM1. unfold build_and_receive_m in HM1.
    destruct (Z.ltb_spec SPEC_MAX_BODY (Z.of_nat (length body))) as [Hlt|Hle];
      [exfalso; apply HM1; reflexivity | unfold SPEC_MAX_BODY in Hle; lia]. }
  assert (RD0 : 0 <= dstp mod 2 ^ 64 < SR_RES_TOP) by (apply ROLOW; rewrite <- (Z.add_0_r dstp); apply HDRO; lia).
  assert (RD5 : 0 <= (dstp + 5) mod 2 ^ 64 < SR_RES_TOP) by (apply ROLOW; apply HDRO; lia).
  assert (RS0 : 0 <= srcp mod 2 ^ 64 < SR_RES_TOP) by (apply ROLOW; rewrite <- (Z.add_0_r srcp); apply HSRO; lia).
  assert (RS5 : 0 <= (srcp + 5) mod 2 ^ 64 < SR_RES_TOP) by (apply ROLOW; apply HSRO; lia).
  assert (RDOK : dstp mod 2 ^ 64 + 6 <= 2 ^ 20).
  { destruct (Z_lt_le_dec (dstp mod 2 ^ 64) (2 ^ 64 - 5)) as [Hl|Hl].
    - rewrite (Zplus_mod dstp 5), (Z.mod_small 5) in RD5 by lia.
      rewrite (Z.mod_small (dstp mod 2 ^ 64 + 5)) in RD5 by lia. unfold SR_RES_TOP in *. lia.
    - exfalso. unfold SR_RES_TOP in RD0. lia. }
  assert (RSOK : srcp mod 2 ^ 64 + 6 <= 2 ^ 20).
  { destruct (Z_lt_le_dec (srcp mod 2 ^ 64) (2 ^ 64 - 5)) as [Hl|Hl].
    - rewrite (Zplus_mod srcp 5), (Z.mod_small 5) in RS5 by lia.
      rewrite (Z.mod_small (srcp mod 2 ^ 64 + 5)) in RS5 by lia. unfold SR_RES_TOP in *. lia.
    - exfalso. unfold SR_RES_TOP in RS0. lia. }
  assert (HDB : bytes_at rsegs (normalize rsegs mem) (dstp mod 2 ^ 64) dst)
    by (apply BLK; [lia | rewrite LD6; lia | apply MOD; exact HDBLK]).
  assert (HSB : bytes_at rsegs (normalize rsegs mem) (srcp mod 2 ^ 64) src)
    by (apply BLK; [lia | rewrite LS6; lia | apply MOD; exact HSBLK]).

  assert (HBB : bytes_at rsegs (normalize rsegs mem) (bodyp mod 2 ^ 64) body /\
                (Z.of_nat (length body) = 0 \/
                 bodyp mod 2 ^ 64 + Z.of_nat (length body) <= spZ regs - 1616 \/
                 spZ regs <= bodyp mod 2 ^ 64)).
  { destruct HSRC as [HN0 | (HOW & [(q & k & Hqin & Hq1 & Hq2) | (Hs1 & Hs2)])].
    - assert (Eb : body = []) by (apply length_zero_iff_nil; lia).
      split; [rewrite Eb; apply bytes_at_nil; pose proof (Z.mod_pos_bound bodyp (2 ^ 64) ltac:(lia)); lia
             | left; exact HN0].
    - destruct (mr_blocks_range B (aa_MR API) (aa_laws API) L A mem md q k HMR Hqin) as (RQ1 & RQ2).
      assert (EM : bodyp mod 2 ^ 64 = bodyp) by (apply Z.mod_small; lia).
      split; [rewrite EM; apply BLK; [lia | lia | exact HBODY] | right; left; lia].
    - assert (EM : bodyp mod 2 ^ 64 = bodyp) by (apply Z.mod_small; lia).
      split; [rewrite EM; apply BLK; [lia | lia | exact HBODY] | right; right; lia]. }
  destruct HBB as (HBB1 & HBB2).

  assert (ZMOD : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
  assert (ED : YK11.getr regs 10 = Z_to_bv 64 (dstp mod 2 ^ 64)) by (rewrite HA10; apply ZMOD).
  assert (ES : YK11.getr regs 11 = Z_to_bv 64 (srcp mod 2 ^ 64)) by (rewrite HA11; apply ZMOD).
  assert (EP : YK11.getr regs 16 = Z_to_bv 64 (bodyp mod 2 ^ 64)) by (rewrite HA16; apply ZMOD).

  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG WORLD (1616 + (48 + 8192)) (spZ regs) L A mem md fx regs
            (Z_to_bv 64 build_and_receive_ENTRY) mem md L A
            (bar_q (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4)
               (YK11.getr regs 8) (YK11.getr regs 9) (YK11.getr regs 18) (YK11.getr regs 19)
               (YK11.getr regs 20) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23)
               (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27)
               fp_regs fp_csr (normalize rsegs mem) (bar_frame dst src send ack retry cmd body))).
  1: exact (sr_fr_init B API SEGS _ L A regs mem md b Bw HPRE).
  1: lia.
  1: lia.
  eapply bar_walk.

  1: exact MSET. 1: exact MCPY. 1: exact ED. 1: exact ES. 1: exact HA12. 1: exact HSEND.
  1: exact HA13. 1: exact HACK. 1: exact HA14. 1: exact HRETRY. 1: exact HA15. 1: exact HCMD.
  1: exact EP. 1: exact HA17. 1: exact HLEN. 1: exact LD6. 1: exact HDB. 1: exact RDOK.
  1: exact LS6. 1: exact HSB. 1: exact RSOK. 1: exact HBB1. 1: exact HBB2. 1: exact HSP16.
  1: (replace (bv_unsigned (Sem.reg_get regs 2)) with (spZ regs) by reflexivity; lia).
  1: exact HSTK. 1: exact HMI.

  1: { intros ms HQ. unfold bar_q in HQ. destruct_exs HQ.
       destruct HQ as (Eq & MUq & WMq & MIq & HFRq & HSVq). subst ms.
       do 5 eexists. exists [(spZ regs - 1616, spZ regs)].
       split; [reflexivity|]. split; [exact MUq|]. split; [exact WMq|].
       intros z Hz HOz. left.
       destruct (Z_le_dec (spZ regs - 1616) z) as [H1|H1];
         [destruct (Z_lt_dec z (spZ regs)) as [H2|H2]|];
         [lia | exfalso | exfalso];
         apply HOz; apply kb_outside; intros lo hi Hin; cbn [In] in Hin;
         destruct Hin as [E|[]]; injection E as <- <-; lia. }

  intros R Ff pc' fcc m0' HQ regs' m' Hxq Hrel FR2.
  unfold bar_q in HQ. destruct_exs HQ.
  destruct HQ as (Eq & MUq & WMq & MIq & HFRq & HSVq).
  injection Eq as ER EF EP2 EC EM. subst Ff pc' fcc m0'.
  pose proof (sr_getr_eqv R regs') as GR. specialize (fun r => GR r Hxq).

  assert (SPE : bv_unsigned (YK11.getr regs 2) = spZ regs) by reflexivity.
  assert (WM1 : wmem rsegs m' Bw).
  { apply (sr_wmem_back m' x19 Bw Hrel).
    apply (Frame.rw_cells_transport rsegs _ (normalize rsegs mem) x19 _ _
             (sr_wmem_norm mem Bw HRO HWM) MUq WMq).
    cbn [Frame.disjoint_from cells_size csize]. rewrite SPE.
    unfold W_BASE_PLAIN, W_LEN. split; [lia | exact I]. }
  assert (RL1 : relro_img m').
  { apply (sr_relro_back m' x19 Hrel). intros i Hi.
    pose proof (sr_relro_norm mem HRO HRELRO i Hi) as Ei.
    change (mrd rsegs x19 (wa (RELRO_BASE + i)) = seg_rom rsegs (wa (RELRO_BASE + i))).
    rewrite <- Ei. change (mbyte rsegs x19 (RELRO_BASE + i) = mbyte rsegs (normalize rsegs mem) (RELRO_BASE + i)).
    apply (mbyte_munch rsegs _ (normalize rsegs mem) x19 _ MUq);
      [unfold RELRO_BASE, RELRO_LEN in *; lia |].
    apply kb_outside. intros lo hi Hin. cbn [In] in Hin. destruct Hin as [E|[]]. injection E as <- <-.
    rewrite SPE. unfold RELRO_BASE, RELRO_LEN in *. lia. }

  assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 89424) by (rewrite GR, ER; reflexivity).
  assert (G2 : YK11.getr regs' 2 = Z_to_bv 64 (spZ regs - 1616)) by (rewrite GR, ER, SPE; reflexivity).
  assert (G4 : YK11.getr regs' 4 = YK11.getr regs 4) by (rewrite GR, ER; reflexivity).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (spZ regs - 1596)) by (rewrite GR, ER, SPE; reflexivity).
  assert (G11 : YK11.getr regs' 11 = Z_to_bv 64 (Z.of_nat (length (bar_frame dst src send ack retry cmd body))))
    by (rewrite GR, ER; reflexivity).
  assert (G12 : YK11.getr regs' 12 = Z_to_bv 64 0) by (rewrite GR, ER; reflexivity).
  assert (G13 : YK11.getr regs' 13 = Z_to_bv 64 0) by (rewrite GR, ER; reflexivity).
  assert (GSP : spZ regs' = spZ regs - 1616) by (unfold spZ; rewrite G2; apply unsigned_lit; lia).
  assert (LFR2 : Z.of_nat (length (bar_frame dst src send ack retry cmd body))
                 = 30 + Z.max 30 (Z.of_nat (length body))).
  { destruct dst as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 [|? ?]]]]]]]; try discriminate LD6.
    unfold bar_frame. rewrite (bar_frame_shape d0 d1 d2 d3 d4 d5 src body send ack retry cmd LS6 HLEN).
    rewrite !app_length, repeat_length, LS6,
      (bar_hdr_len (Z.of_nat (length body)) send ack retry cmd body). cbn [length]. lia. }

  pose proof FR2 as (FM & FW & FB & FID & Fmd & Fhigh & Fimg & Fub & Fbyt & Fstw & Ferr & Fgd & FRO & Fle & Flen).
  assert (B2B : forall m0 a bs, bytes_at rsegs m0 a bs -> blk_data B m0 a bs).
  { intros m0 a bs (H0 & H1 & H2) i Hi. rewrite SEGS.
    pose proof (H2 (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E. }
  assert (HFR2 : bytes_at rsegs m' (spZ regs - 1596) (bar_frame dst src send ack retry cmd body)).
  { rewrite <- SPE in *. exact (proj2 (bytes_at_rel rsegs m' x19 _ _ Hrel) HFRq). }
  assert (HMOD2 : forall a, h_addr_ok a ->
            receive_m timg_plain Bw a (bar_frame dst src send ack retry cmd body) 0 0 <> None).
  { intros a Ha. pose proof (HMODEL a Ha) as HM. unfold build_and_receive_m in HM.
    destruct (Z.ltb_spec SPEC_MAX_BODY (Z.of_nat (length body))) as [Hl|Hl];
      [unfold SPEC_MAX_BODY in Hl; lia|].
    unfold bar_frame. destruct (spec_build_frame dst src send ack retry cmd 1 body 0) as [fr n] eqn:Esb.
    cbn [fst]. exact HM. }
  assert (HPRE2 : h_pre B API receive_FRAME L A regs' m' md b Bw).
  { unfold h_pre, receive_FRAME, ALLOC_STACK.
    split; [| split; [exact HID | split; [exact HHALT | split; [exact HLAZY |
      split; [rewrite SEGS; exact FRO | split; [exact HRES | split; [| split; [exact WM1 |
      split; [exact HGF | exact RL1]]]]]]]]].
    - apply (g_pre B API (1616 + (48 + 8192)) (spZ regs) L A mem md L A m' md regs' (48 + 8192) FR2);
        [rewrite G1; vm_compute; reflexivity | rewrite GSP; lia | rewrite GSP; lia | rewrite GSP; lia
         | lia | lia | rewrite GSP; lia | rewrite G4; exact HTP].
    - unfold w_off_stack in *. rewrite G2, unsigned_lit by lia. unfold W_BASE_PLAIN, W_LEN in *. lia. }

  assert (HARG2 : receive_args B L A regs' m' Bw (spZ regs - 1596)
                    (bar_frame dst src send ack retry cmd body) 0 0).
  { unfold receive_args.
    split; [exact G10|]. split; [exact G11|]. split; [exact G12|]. split; [lia|].
    split; [rewrite G13, unsigned_lit by lia; reflexivity|]. split; [lia|].
    split; [lia|].
    split; [apply B2B; exact HFR2|].
    split; [| exact HMOD2].
    unfold h_src. right. split.
    - unfold off_world. right. unfold W_BASE_PLAIN, W_LEN in *. lia.
    - right. rewrite GSP. split; [lia | lia]. }
  rewrite <- SEGS.
  eapply SR_bind.
  { apply (RECV BI L A regs' m' md b Bw (spZ regs - 1596)
             (bar_frame dst src send ack retry cmd body) 0 0 HPRE2 HFRM HARG2 HROOM). }

  intros c2 (a & Bw' & HAOK & HACEIL & HAIMG & HRM & HPOST).
  destruct HPOST as (fx2 & L2 & A2 & regs2 & mem2 & md2 & Ec2 & HFRM2 & HCPK & HID2 & HHALT2 & HLAZY2
    & HBLK2 & HUB2 & HREG2 & HRES2 & HRO2 & HGK2 & HWM2 & HGF2 & HRL2). subst c2.

  pose proof HCPK as (PM & PW & PB & Ple & Pstab & Prp & Pvm & Pfr & Pblk & Pscr).
  assert (ENOW : forall xw, (h_world xw \/ a <= xw < a + Z.max 1 (Z.of_nat (length (bar_frame dst src send ack retry cmd body)))
                            \/ ms_ctx B <= xw < ms_ctx B + CTX_SIZE) -> xw < YM05.alloc_ceiling).
  { intros xw [Hw | [Hr | Hc]]; [unfold h_world, W_BASE_PLAIN, W_LEN in Hw | | ]; lia. }
  assert (FR3 : sr_fr B API (1616 + (48 + 8192)) (spZ regs) L A mem md L2 A2 mem2 md2).
  { eapply (sr_fr_call B API SEGS AX ERRNO_LOW WORLD (1616 + (48 + 8192)) (spZ regs) L A mem md
              L A m' md receive_FRAME regs' _ L2 A2 regs2 mem2 md2 FR2);
      [lia | lia | exact HCPK
       | rewrite GSP; unfold receive_FRAME, ALLOC_STACK; lia | rewrite GSP; lia
       | | | | exact HUB2 | | exact HID2 | rewrite <- SEGS; exact HRO2 | exact HGK2 | exact HREG2].
    - intros xw [Hw | [Hr | Hc]].
      + right; right; left; exact Hw.
      + right; left. split; [lia|]. replace xw with (a + (xw - a)) by lia. apply HAIMG. lia.
      + right; right; right; exact Hc.
    - intros xw Hxw. right. intros HE. pose proof (ENOW xw HE). lia.
    - intros xw HE Hxw. exfalso. pose proof (ENOW xw HE). lia.
    - intros ab k i Hinb Hi. apply blocks_In in Hinb as (pb & Hpb & Hpinb). rewrite <- Hpb.
      exact (Pblk pb k i Hpinb (HUB2 pb k Hpinb) Hi). }

  assert (P2 : YK11.getr regs2 2 = YK11.getr regs' 2) by (apply (Prp 2); unfold callee_saved; lia).
  assert (P3 : YK11.getr regs2 3 = YK11.getr regs' 3) by (apply (Prp 3); unfold callee_saved; lia).
  assert (P4 : YK11.getr regs2 4 = YK11.getr regs' 4) by (apply (Prp 4); unfold callee_saved; lia).
  assert (P25 : YK11.getr regs2 25 = YK11.getr regs' 25) by (apply (Prp 25); unfold callee_saved; lia).
  assert (P26 : YK11.getr regs2 26 = YK11.getr regs' 26) by (apply (Prp 26); unfold callee_saved; lia).
  assert (P27 : YK11.getr regs2 27 = YK11.getr regs' 27) by (apply (Prp 27); unfold callee_saved; lia).
  assert (GAB : forall xq, spZ regs' <= xq < spZ regs ->
                  mbyte (ms_segs B) mem2 xq = mbyte (ms_segs B) m' xq /\
                  (writable_at (ms_segs B) m' xq <-> writable_at (ms_segs B) mem2 xq)).
  { apply (g_above B API ERRNO_LOW (1616 + (48 + 8192)) (spZ regs) L A regs' m' md receive_FRAME _
             L2 A2 regs2 mem2 md2 FM HCPK);
      [lia | rewrite GSP; unfold receive_FRAME, ALLOC_STACK; lia | lia
       | unfold receive_FRAME, ALLOC_STACK; lia | exact ENOW]. }
  assert (HSV2 : bytes_at rsegs (normalize rsegs mem2) (spZ regs - 80)
                   (le8 (YK11.getr regs 24) ++ le8 (YK11.getr regs 23) ++ le8 (YK11.getr regs 22) ++
                    le8 (YK11.getr regs 21) ++ le8 (YK11.getr regs 20) ++ le8 (YK11.getr regs 19) ++
                    le8 (YK11.getr regs 18) ++ le8 (YK11.getr regs 9) ++ le8 (YK11.getr regs 8) ++
                    le8 (YK11.getr regs 1))).
  { apply (bytes_at_normalize rsegs mem2); [rewrite <- SEGS; exact HRO2|].
    apply (KindB.bytes_at_transfer rsegs m' mem2).
    - rewrite <- SPE in *. exact (proj2 (bytes_at_rel rsegs m' x19 _ _ Hrel) HSVq).
    - intros i Hi. rewrite !app_length, !length_le8 in Hi. cbn [Nat.add] in Hi.
      rewrite <- SEGS. apply (proj1 (GAB (spZ regs - 80 + i) ltac:(rewrite GSP; lia))). }

  assert (Q2 : Sem.reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (YK11.getr regs 2) - 1616))
    by (change (Sem.reg_get regs2 2) with (YK11.getr regs2 2); rewrite P2, G2, SPE; reflexivity).
  assert (Q3 : Sem.reg_get regs2 3 = YK11.getr regs 3)
    by (change (Sem.reg_get regs2 3) with (YK11.getr regs2 3); rewrite P3, GR, ER; reflexivity).
  assert (Q4 : Sem.reg_get regs2 4 = YK11.getr regs 4)
    by (change (Sem.reg_get regs2 4) with (YK11.getr regs2 4); rewrite P4, GR, ER; reflexivity).
  assert (Q25 : Sem.reg_get regs2 25 = YK11.getr regs 25)
    by (change (Sem.reg_get regs2 25) with (YK11.getr regs2 25); rewrite P25, GR, ER; reflexivity).
  assert (Q26 : Sem.reg_get regs2 26 = YK11.getr regs 26)
    by (change (Sem.reg_get regs2 26) with (YK11.getr regs2 26); rewrite P26, GR, ER; reflexivity).
  assert (Q27 : Sem.reg_get regs2 27 = YK11.getr regs 27)
    by (change (Sem.reg_get regs2 27) with (YK11.getr regs2 27); rewrite P27, GR, ER; reflexivity).
  rewrite G1, SEGS.
  eapply (g_run B API SEGS AX HGG WORLD (1616 + (48 + 8192)) (spZ regs) L A mem md fx2 regs2
            (Z_to_bv 64 89424) mem2 md2 L2 A2
            (fun ms => exists (q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
               ms = MS (mkR (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4)
                          q5 q6 q7 (YK11.getr regs 8) (YK11.getr regs 9) q10 q11 q12 q13 q14 q15 q16 q17
                          (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 20) (YK11.getr regs 21)
                          (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25)
                          (YK11.getr regs 26) (YK11.getr regs 27) q28 q29 q30 q31)
                       (@fp_regs fx2) (ret_pc (YK11.getr regs 1)) (@fp_csr fx2) None
                       (normalize rsegs mem2) (YK11.seg_rom rsegs))).
  1: exact FR3. 1: lia. 1: lia.
  1: { unfold Regs6ss.mkR_of. rewrite Q2, Q3, Q4, Q25, Q26, Q27.
       apply (bar_epi (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4)
                (YK11.getr regs 8) (YK11.getr regs 9) (YK11.getr regs 18) (YK11.getr regs 19)
                (YK11.getr regs 20) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23)
                (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27));
         [rewrite <- SPE in HSV2; exact HSV2 | rewrite SPE; lia |].
       do 15 eexists. reflexivity. }

  1: { intros ms (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & Eqf).
       subst ms. do 5 eexists. exists (@nil ivl).
       split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
       intros xz Hxz HOz. exfalso. apply HOz. apply kb_outside. intros lo hi Hin. destruct Hin. }

  intros R3 F3 pc3 fc3 m03
    (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & Eq3)
    regs3 m3 Hx3 Hrel3 FR4.
  injection Eq3 as ER3 EF3 EPC3 EFC3 EM3. subst F3 pc3 fc3 m03.
  pose proof (fun r => sr_getr_eqv R3 regs3 r Hx3) as GR3.

  pose proof FR4 as (FM4 & FW4 & FB4 & FID4 & Fmd4 & Fhigh4 & Fimg4 & Fub4 & Fbyt4 & Fstw4 & Ferr4 & Fgd4
    & FRO4 & Fle4 & Flen4).
  assert (RPC : ret_pc (YK11.getr regs 1) = YK11.getr regs 1) by (apply sr_ret_pc; exact HRET).
  rewrite RPC.
  apply SR_ret. unfold bar_ret. exists a, Bw'.
  split; [exact HAOK|]. split; [exact HACEIL|]. split; [exact HAIMG|].
  split.
  { unfold build_and_receive_m.
    destruct (Z.ltb_spec SPEC_MAX_BODY (Z.of_nat (length body))) as [Hl2|Hl2];
      [unfold SPEC_MAX_BODY in Hl2; lia|].
    unfold bar_frame in HRM.
    destruct (spec_build_frame dst src send ack retry cmd 1 body 0) as [fr nn] eqn:Esb.
    cbn [fst] in HRM. exact HRM. }
  exists fx2, L2, A2, regs3, m3, md2.
  split; [rewrite <- SEGS; reflexivity|].
  split; [exact HFRM2|].
  split.
  { apply (sr_post B API (1616 + (48 + 8192)) _ L A regs mem md L2 A2 regs3 m3 md2 FR4).
    - intros r Hcs. rewrite GR3, ER3.
      destruct Hcs as [->|[->|[->|[->|[->|Hr]]]]];
        [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
      assert (Hd : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25
                   \/ r = 26 \/ r = 27) by lia.
      destruct Hd as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; subst r; reflexivity.
    - intros az Hw. left. exact Hw.
    - intros az2 Hc. right. right. exact Hc. }
  split; [exact HID2|]. split; [exact HHALT2|]. split; [exact HLAZY2|].
  split; [exact HBLK2|]. split; [exact HUB2|]. split; [exact HREG2|].
  split; [exact HRES2|].
  split; [rewrite SEGS; exact FRO4|].
  split; [exact Fgd4|].
  split; [exact (sr_wmem_back m3 (normalize rsegs mem2) Bw' Hrel3
                   (sr_wmem_norm mem2 Bw' ltac:(rewrite <- SEGS; exact HRO2) HWM2))|].
  split; [exact HGF2|].
  exact (sr_relro_back m3 (normalize rsegs mem2) Hrel3
           (sr_relro_norm mem2 ltac:(rewrite <- SEGS; exact HRO2) HRL2)).
Qed.

End K.
