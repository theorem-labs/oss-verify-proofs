(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 552 of its 576 lines of code are new or changed and 120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/diginet_sysex_encode.v, with its module names, addresses and numbers changed; 705 of its 796 lines of code are new or changed and 485 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_seg7_c diginet_counter_text_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_of_u32arr : forall m A ws,
  u32arr rsegs m A ws -> rw_cells rsegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [Hb Hw]. split.
  - split. { cbn. split; [apply u32s_length | exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

Lemma rw_cells_CB_length : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[Hwf _] _]. cbn in Hwf. tauto. Qed.

Lemma dot_zero_u32arr : forall m A,
  rw_cells rsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  u32arr rsegs m A (map (Z_to_bv 64) (repeat 0 8)).
Proof.
  intros m A [[_ Hb] Hw]. split.
  - replace (u32s (map (Z_to_bv 64) (repeat 0 8)))
      with (cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (vm_compute; reflexivity).
    exact Hb.
  - exact Hw.
Qed.

Lemma bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma u_swrap1 : forall z, 0 <= z < 2^31 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 z)) = z.
Proof.
  intros z Hz. rewrite (bv_swrap_small 32) by (change (bv_half_modulus 32) with (2^31); lia).
  apply unsigned_lit. lia.
Qed.

Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply (bv_swrap_small 32). change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma shiftl2 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.

Lemma land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof.
  intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small.
  change (2^8) with 256. lia.
Qed.

Lemma le1_one : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Lemma z8_of_64 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  apply mod_mod8_of_modw. lia.
Qed.

Lemma z8_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma nth_zb : forall l i, nth i (zb l) 0 = bv_unsigned (nth i l (Z_to_bv 8 0)).
Proof. intros l i. unfold zb. exact (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) i). Qed.

Lemma nth_error_mapz : forall (l : list Z) j, (j < length l)%nat ->
  nth_error (map (Z_to_bv 64) l) j = Some (Z_to_bv 64 (nth j l 0)).
Proof. intros l j H. rewrite nth_error_map, (nth_error_nth' l 0 H). reflexivity. Qed.

Lemma sb_nth : forall (sb : list byte) s n j, firstn n sb = bz s -> (j < n)%nat -> (n <= length sb)%nat ->
  nth_error sb j = Some (b8 (nth j s 0)).
Proof.
  intros sb s n j H Hj Hn.
  assert (Ls : length s = n).
  { apply (f_equal (@length byte)) in H. unfold bz in H. rewrite length_firstn, length_map in H. lia. }
  rewrite <- (firstn_skipn n sb), nth_error_app1 by (rewrite length_firstn; lia). rewrite H.
  assert (Hj' : (j < length s)%nat) by lia.
  unfold bz. rewrite nth_error_map, (nth_error_nth' s 0 Hj'). reflexivity.
Qed.

Lemma firstn_upd_snoc : forall (l pre : list byte) i b, firstn i l = pre -> (i < length l)%nat ->
  firstn (S i) (upd l i b) = pre ++ [b].
Proof.
  intros l pre i b H Hi. rewrite upd_firstn_skipn by exact Hi. rewrite firstn_app.
  assert (L : length (firstn i l) = i) by (apply firstn_length_le; lia).
  rewrite L, firstn_all2 by lia. replace (S i - i)%nat with 1%nat by lia. cbn. rewrite H. reflexivity.
Qed.

Lemma map_upd_at : forall (l : list Z) j v, (Z.to_nat j < length l)%nat ->
  upd (map (Z_to_bv 64) l) (Z.to_nat j) (Z_to_bv 64 v) = map (Z_to_bv 64) (upd_at l j v).
Proof.
  intros l j v H. rewrite upd_firstn_skipn by (rewrite length_map; exact H).
  unfold upd_at. rewrite map_app. cbn [map]. rewrite firstn_map, skipn_map. reflexivity.
Qed.

Lemma bz_snoc : forall l v, bz (l ++ [v]) = bz l ++ [b8 v].
Proof. intros l v. unfold bz. rewrite map_app. reflexivity. Qed.

Lemma sx32_small : forall v, 0 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma Forall_nth01 : forall (l : list Z) j, Forall (fun v => 0 <= v <= 1) l -> 0 <= nth j l 0 <= 1.
Proof. intros l j H. apply (nth_Forall (fun v => 0 <= v <= 1)); [exact H | lia]. Qed.

Lemma Z2N_succ : forall i, 0 <= i -> Z.to_nat (i + 1) = S (Z.to_nat i).
Proof. intros i Hi. lia. Qed.

Lemma bit_i : forall i, 0 <= i <= 6 -> bv_swrap 32 (Z.shiftl 1 (i mod 32)) mod 18446744073709551616 = 2 ^ i.
Proof.
  intros i Hi. rewrite (Z.mod_small i 32) by lia. rewrite Z.shiftl_1_l.
  assert (H : 0 < 2 ^ i <= 2 ^ 6) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  change (2 ^ 6) with 64 in H. rewrite swrap32_id by lia. apply Z.mod_small. lia.
Qed.

Lemma lor_bit_lt : forall d i, 0 <= d < 128 -> 0 <= i <= 6 -> 0 <= Z.lor d (2 ^ i) < 128.
Proof.
  intros d i Hd Hi. pose proof (lor_lt_pow2 d (2 ^ i) 7) as Hl. change (2 ^ 7) with 128 in Hl. apply Hl; [lia|].
  split; [apply Z.pow_nonneg; lia|]. change 128 with (2 ^ 7). apply Z.pow_lt_mono_r; lia.
Qed.

(** The result of diginet_counter_text for the outcome of its first loop. *)
Definition ct_res (o : option (Z * list Z * list Z)) : Z * list Z * Z :=
  match o with None => (E_RANGE, [], 0) | Some (n', s', dot') => ct2 n' s' dot' end.

(** The rest of one step of the first loop once the digit pattern v of character ch is known. *)
Definition ct1_rest (v ch : Z) (t' : list Z) (n : Z) (s dot : list Z) : option (Z * list Z * list Z) :=
  if (v <? 0) || (n =? 8) then None
  else ct1_lib t' (n + 1) (s ++ [v]) (if ch =? 46 then upd_at dot n 1 else dot).

Lemma ct1_cons : forall ch t' n s dot, ch <> 0 ->
  ct1_lib (ch :: t') n s dot =
  if (ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0) then ct1_lib t' n s (upd_at dot (n - 1) 1)
  else ct1_rest (seg7_spec (if ch =? 46 then 32 else ch)) ch t' n s dot.
Proof. intros ch t' n s dot H. cbn [ct1_lib]. rewrite (proj2 (Z.eqb_neq ch 0) H). reflexivity. Qed.

Lemma ifb_false : forall {A} (b : bool) (x y : A), b = false -> (if b then x else y) = y.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ifb_true : forall {A} (b : bool) (x y : A), b = true -> (if b then x else y) = x.
Proof. intros A b x y ->. reflexivity. Qed.

Lemma skip_step : forall (t : list Z) i ch, In 0 (skipn i t) -> nth i t 0 = ch -> ch <> 0 ->
  skipn i t = ch :: skipn (S i) t /\ In 0 (skipn (S i) t) /\ (S i < length t)%nat.
Proof.
  intros t i ch HIn Hn Hc.
  assert (Hi : (i < length t)%nat).
  { destruct (Nat.lt_ge_cases i (length t)) as [H|H]; [exact H|]. rewrite skipn_all2 in HIn by exact H. destruct HIn. }
  pose proof (skipn_cons_nth t i 0 Hi) as E. rewrite Hn in E.
  rewrite E in HIn. destruct HIn as [H0 | HIn]; [congruence|].
  split; [exact E|]. split; [exact HIn|].
  destruct (Nat.lt_ge_cases (S i) (length t)) as [H|H]; [exact H|]. rewrite skipn_all2 in HIn by exact H. destruct HIn.
Qed.

Lemma In_skipn_len : forall (t : list Z) i, In 0 (skipn i t) -> (i < length t)%nat.
Proof.
  intros t i HIn. destruct (Nat.lt_ge_cases i (length t)) as [H|H]; [exact H|].
  rewrite skipn_all2 in HIn by exact H. destruct HIn.
Qed.

Lemma length_zb : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma seg7_range : forall c, 0 <= c < 256 -> seg7_spec c = -1 \/ 0 <= seg7_spec c < 128.
Proof. intros c Hc. rewrite seg7_agree by exact Hc. apply owed_seg7_range. Qed.

Lemma Forall_upd_at : forall (P : Z -> Prop) l j v, Forall P l -> P v -> Forall P (upd_at l j v).
Proof.
  intros P l j v H Hv. unfold upd_at. generalize (Z.to_nat j) as k. clear j.
  induction H as [|x l Hx Hl IH]; intros [|k]; cbn.
  - constructor; [exact Hv | constructor].
  - constructor; [exact Hv | constructor].
  - constructor; [exact Hv | exact Hl].
  - constructor; [exact Hx | apply IH].
Qed.

Lemma ct_inv_mono : forall n dot, ct_inv n dot -> n < 8 -> ct_inv (n + 1) dot.
Proof. intros n dot (Hn & Hl & Hz) H8. split; [lia|]. split; [exact Hl|]. intros j Hj. apply Hz. lia. Qed.

Lemma signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt z (2^63))) by lia. reflexivity.
Qed.

Ltac refute K := exfalso; zify_cond K; try (rewrite ?zb_lxor_ones in K by lia); try (rewrite ?signed_small in K by lia);
  first [ lia | (Z.div_mod_to_equations; lia) ].

Ltac nobr := let K := fresh "K" in if_cases K; [refute K | clear K].
Ltac yesbr := let K := fresh "K" in if_cases K; [clear K | refute K].

Ltac rw_regs := repeat match goal with
  | E : bv_unsigned ?x = _ |- context [bv_unsigned ?x] => is_var x; rewrite E
  end.

Ltac zs := zstep; rw_regs; zsimp; rewrite ?shiftl2.

Section CT.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z) (A0 A1 A2 : word) (tb : list byte).
Hypothesis LO : lo + 160 <= bv_unsigned sp.
Hypothesis L0 : bv_unsigned sp <= bv_unsigned A0.
Hypothesis L1 : bv_unsigned sp <= bv_unsigned A1.
Hypothesis L2 : bv_unsigned sp <= bv_unsigned A2.
Hypothesis DJ12 : disj (bv_unsigned A1) 8 (bv_unsigned A2) 1.
Hypothesis SEG7 : diginet_seg7_contract.

Definition saved : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Wct : list ivl :=
  [(bv_unsigned sp - DIGINET_COUNTER_TEXT_DEPTH, bv_unsigned sp); (bv_unsigned A1, bv_unsigned A1 + 8);
   (bv_unsigned A2, bv_unsigned A2 + 1)].

Definition Qc (res : Z * list Z * Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch Wct m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, sg, d) := res in
    a0' = Z_to_bv 64 rc /\
    (rc = 0 -> rw_cells rsegs m' (bv_unsigned A1) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned A2) [C1 (b8 d)]) /\
    (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned A1) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned A2) [C1 dv]).

(** The epilogue at 0x16130: a1 holds the code rc; the frame is released and the saved registers come back. *)
Lemma ct_exit : forall (ra' t0' t1' t2' x8 x9 a0' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        t3' t4' : word) (m1 : word -> option byte) (cs16 : list cell) (dws : list word)
                       (sb segb : list byte) (dv : byte) (rc : Z) (sg : list Z) (d : Z),
  cells_size cs16 = 16%nat -> length dws = 8%nat -> length sb = 8%nat -> length segb = 8%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -160) cs16 ->
  u32arr rsegs m1 (bv_unsigned sp + -144) dws ->
  u8arr rsegs m1 (bv_unsigned sp + -112) sb ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  u8arr rsegs m1 (bv_unsigned A1) segb ->
  rw_cells rsegs m1 (bv_unsigned A2) [C1 dv] ->
  stk rsegs m1 lo (bv_unsigned sp + -160) ->
  munch Wct m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  (rc = 0 -> segb = bz sg /\ dv = b8 d) ->
  evt rsegs (Qc (rc, sg, d))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x8 x9 a0' (Z_to_bv 64 rc) a2' a3' a4' a5' a6' a7'
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5 t6)
        F (Z_to_bv 64 0x16130) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 a0' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4'
         m1 cs16 dws sb segb dv rc sg d H16 HLD HLS HLG FRL DOT SAR FRH SEG DTS ST MU WM HMI HOK.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as [Hlo _].
  unfold saved in FRH.
  do 15 zstep.
  eapply stk_release in FRL; [ | exact ST | lia ]. rewrite H16 in FRL.
  replace (bv_unsigned sp + -160 + Z.of_nat 16) with (bv_unsigned sp + -144) in FRL by lia.
  apply rw_cells_of_u32arr in DOT.
  eapply stk_release in DOT; [ | exact FRL | lia ]. cbn [cells_size csize] in DOT. rewrite HLD in DOT.
  replace (bv_unsigned sp + -144 + Z.of_nat (4 * 8 + 0)) with (bv_unsigned sp + -112) in DOT by lia.
  apply rw_cells_of_u8arr in SAR.
  eapply stk_release in SAR; [ | exact DOT | lia ]. cbn [cells_size csize] in SAR. rewrite HLS in SAR.
  replace (bv_unsigned sp + -112 + Z.of_nat (8 + 0)) with (bv_unsigned sp + -104) in SAR by lia.
  eapply stk_release in FRH; [ | exact SAR | lia ]. cbn [cells_size csize Nat.add] in FRH.
  replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in FRH by lia.
  clear ST FRL DOT SAR.
  zstep.
  apply evt_done. unfold Qc. hot_eexists_all. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|]. split; [exact FRH|].
  cbv beta iota. split; [reflexivity|]. split.
  - intros H0. destruct (HOK H0) as [-> ->]. split; [|exact DTS].
    apply rw_cells_of_u8arr in SEG. rewrite HLG in SEG. exact SEG.
  - intros _. exists segb, dv. split; [|exact DTS].
    apply rw_cells_of_u8arr in SEG. rewrite HLG in SEG. exact SEG.
Qed.


(** The memory between the prologue and the epilogue: frame pieces (dots pointer, dot[8], s[8], saved registers),
    seg and *dots, the stack below the frame, and the footprint so far. *)
Definition fr_ok (m1 : word -> option byte) (j0 : list byte) (dot : list Z) (sb segb : list byte) (dv : byte) : Prop :=
  rw_cells rsegs m1 (bv_unsigned sp + -160) [CB 8 j0; C8 A2] /\
  u32arr rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) /\
  u8arr rsegs m1 (bv_unsigned sp + -112) sb /\
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved /\
  u8arr rsegs m1 (bv_unsigned A1) segb /\
  rw_cells rsegs m1 (bv_unsigned A2) [C1 dv] /\
  stk rsegs m1 lo (bv_unsigned sp + -160) /\
  munch Wct m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1.

Definition vinv (n : Z) (s dot : list Z) (sb : list byte) : Prop :=
  ct_inv n dot /\ Forall (fun v => 0 <= v <= 1) dot /\ Z.of_nat (length s) = n /\
  length sb = 8%nat /\ firstn (Z.to_nat n) sb = bz s.

Ltac open_fr H :=
  destruct H as (FRL & DOT & SAR & FRH & SEG & DTS & ST & MU & WM & HMI);
  unfold Wct, DIGINET_COUNTER_TEXT_DEPTH in MU; unfold saved in FRH.

Ltac close_fr :=
  unfold fr_ok;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))));
  try eassumption.

Ltac basics :=
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; pose proof (bv_unsigned_in_range 64 A1) as RA1;
  pose proof (bv_unsigned_in_range 64 A2) as RA2; unfold bv_modulus in Rsp, RA1, RA2;
  match goal with ST : stk _ _ lo _ |- _ => pose proof ST as [Hlo _] end.

Local Abbreviation R2 r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 :=
  (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp (Z_to_bv 64 (bv_unsigned sp + -144)) (Z_to_bv 64 1) r7
       r8 A1 (Z_to_bv 64 8) r11 r12 r13 (Z_to_bv 64 (Z.lxor (bv_unsigned A1) 18446744073709551615)) r15 (Z_to_bv 64 7)
       (Z_to_bv 64 (bv_unsigned sp + -112)) r18 (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -144) 18446744073709551615))
       (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -112) 18446744073709551615)) r21 r22 r23 r24 r25 r26 r27 r28 r29 t5 t6).

(** The second loop (head 0x160b4), digit i of 8 with k = 8 - i digits left: the result is ct2_go from that state;
    seg[0..i) holds the digits so far and a2 the dots so far. *)
Definition l2_ok (k : nat) : Prop :=
  forall (r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 : word)
         (n : Z) (s dot : list Z) (i : Z) (seg : list Z) (d : Z) (j0 sb segb : list byte) (dv : byte)
         (m1 : word -> option byte),
  (1 <= k)%nat -> i + Z.of_nat k = 8 -> 0 <= i ->
  vinv n s dot sb ->
  bv_unsigned r11 = i -> bv_unsigned r13 = i -> bv_unsigned r12 = d -> 0 <= d < 128 -> bv_unsigned r15 = 8 - n ->
  Z.of_nat (length seg) = i -> length segb = 8%nat -> firstn (Z.to_nat i) segb = bz seg ->
  fr_ok m1 j0 dot sb segb dv ->
  evt rsegs (Qc (ct2_go n s dot i k seg d))
    (MS (R2 r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29) F (Z_to_bv 64 0x160b4) fc None m1
        (seg_rom rsegs)).

Lemma l2_tail : forall k', l2_ok k' ->
  forall (r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 : word)
         (n : Z) (s dot : list Z) (i : Z) (seg : list Z) (d : Z) (j0 sb segb : list byte) (dv : byte)
         (m1 : word -> option byte),
  i + 1 + Z.of_nat k' = 8 -> 0 <= i ->
  vinv n s dot sb ->
  bv_unsigned r11 = i -> bv_unsigned r13 = i -> bv_unsigned r12 = d -> 0 <= d < 128 -> bv_unsigned r15 = 8 - n ->
  Z.of_nat (length seg) = i + 1 -> length segb = 8%nat -> firstn (Z.to_nat (i + 1)) segb = bz seg ->
  fr_ok m1 j0 dot sb segb dv ->
  evt rsegs (Qc (ct2_go n s dot (i + 1) k' seg d))
    (MS (R2 r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29) F (Z_to_bv 64 0x16110) fc None m1
        (seg_rom rsegs)).
Proof.
  intros k' IH r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 n s dot i seg d j0 sb segb dv m1
         Hk Hi VI E11 E13 E12 Hd E15 Lseg Lsegb Fseg FR.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  open_fr FR. basics.
  pose proof (eq_trans (length_map (Z_to_bv 64) dot) Ldot) as LDW.
  pose proof (u8arr_bound _ _ _ _ SEG) as BSEG. rewrite Lsegb in BSEG.
  unfold disj in DJ12.
  zs. zs. zs.
  destruct k' as [|k''].
  - nobr.
    zs. zs. zs.
    rewrite le1_one. rw_regs. mem_after_store.
    zs.
    cbn [ct2_go].
    eapply ct_exit with (cs16 := [CB 8 j0; C8 A2]) (dws := map (Z_to_bv 64) dot) (sb := sb) (segb := segb)
      (dv := Z_to_bv 8 d); try eassumption.
    + reflexivity.
    + intros _. split; [|reflexivity].
      rewrite <- Fseg. replace (Z.to_nat (i + 1)) with 8%nat by lia. symmetry. apply firstn_all2. lia.
  - yesbr.
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot (i + 1) seg d j0 sb segb dv); try eassumption.
    all: first [ lia | (apply u_swrap1; lia) | (apply unsigned_lit; lia) | close_fr ].
Qed.


Lemma l2_store : forall k', l2_ok k' ->
  forall (r1 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 : word)
         (n : Z) (s dot : list Z) (i : Z) (seg : list Z) (d : Z) (j0 sb segb : list byte) (dv : byte)
         (m1 : word -> option byte),
  i + Z.of_nat (S k') = 8 -> 0 <= i ->
  vinv n s dot sb ->
  bv_unsigned r11 = i -> bv_unsigned r13 = i -> bv_unsigned r12 = d -> 0 <= d < 128 -> bv_unsigned r15 = 8 - n ->
  Z.of_nat (length seg) = i -> length segb = 8%nat -> firstn (Z.to_nat i) segb = bz seg ->
  Z_to_bv 8 (bv_unsigned r28) = b8 (if i - (8 - n) <? 0 then 0 else nth (Z.to_nat (i - (8 - n))) s 0) ->
  fr_ok m1 j0 dot sb segb dv ->
  evt rsegs (Qc (ct2_go n s dot i (S k') seg d))
    (MS (R2 r1 (Z_to_bv 64 (i - (8 - n))) r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29) F
        (Z_to_bv 64 0x160e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros k' IH r1 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 n s dot i seg d j0 sb segb dv m1
         Hk Hi VI E11 E13 E12 Hd E15 Lseg Lsegb Fseg E28 FR.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  open_fr FR. basics.
  pose proof (eq_trans (length_map (Z_to_bv 64) dot) Ldot) as LDW.
  pose proof (u8arr_bound _ _ _ _ SEG) as BSEG. rewrite Lsegb in BSEG.
  unfold disj in DJ12.
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned A1 + i)) 1 = true)
    by (apply (u8arr_store_ok rsegs m1 (bv_unsigned A1) segb i); [exact SEG | lia | reflexivity]).
  zs. zs.
  rewrite le1_one.
  pose proof (u8arr_write rsegs m1 (bv_unsigned A1) segb i (Z_to_bv 8 (bv_unsigned r28)) SEG ltac:(lia)) as SEG'.
  clear SEG. store_done.
  assert (Lsegb' : length (upd segb (Z.to_nat i) (Z_to_bv 8 (bv_unsigned r28))) = 8%nat)
    by (rewrite Arr.upd_length; exact Lsegb).
  assert (Fseg' : forall v, Z_to_bv 8 (bv_unsigned r28) = b8 v ->
            firstn (Z.to_nat (i + 1)) (upd segb (Z.to_nat i) (Z_to_bv 8 (bv_unsigned r28))) = bz (seg ++ [v])).
  { intros v Ev. rewrite Z2N_succ by lia. rewrite (firstn_upd_snoc segb (bz seg)); [| exact Fseg | lia].
    rewrite bz_snoc, Ev. reflexivity. }
  assert (Lseg' : forall v, Z.of_nat (length (seg ++ [v])) = i + 1) by (intros v; rewrite length_app; cbn [length]; lia).
  cbn [ct2_go].
  zs.
  destruct (Z.ltb_spec (i - (8 - n)) 0) as [Hneg | Hnn].
  - yesbr.
    try rewrite (proj2 (Z.leb_gt 0 (i - (8 - n))) Hneg). cbn [andb] in E28 |- *.
    eapply (l2_tail k' IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot i (seg ++ [0]) d j0 sb _ dv);
      try eassumption; try lia.
    + apply Lseg'.
    + apply Fseg'. exact E28.
    + close_fr.
  - nobr.
    try rewrite (proj2 (Z.leb_le 0 (i - (8 - n))) Hnn). cbn [andb] in E28 |- *.
    zs. zs. nobr. zs.
    pose proof (Forall_nth01 dot (Z.to_nat (i - (8 - n))) D01) as Hfv.
    match goal with D : u32arr rsegs ?mm (bv_unsigned sp + -144) _ |- _ =>
      pose proof (u32arr_read rsegs mm (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) (i - (8 - n)) _ _ D
                    (nth_error_mapz dot (Z.to_nat (i - (8 - n))) ltac:(lia)) ltac:(lia) eq_refl) as HR
    end.
    zs. rewrite sx32_small by lia.
    zs.
    destruct (Z.eq_dec (nth (Z.to_nat (i - (8 - n))) dot 0) 0) as [Hz | Hnz].
    + yesbr. rewrite Hz. cbn [Z.eqb negb].
      eapply (l2_tail k' IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot i (seg ++ [nth (Z.to_nat (i - (8 - n))) s 0]) d
                j0 sb _ dv); try eassumption; try lia.
      * apply Lseg'.
      * apply Fseg'. exact E28.
      * close_fr.
    + nobr. rewrite (proj2 (Z.eqb_neq _ 0) Hnz). cbn [negb].
      zs.
      destruct (Z.eq_dec i 7) as [H7 | H7].
      * yesbr. rewrite (proj2 (Z.eqb_eq i 7) H7). cbn [andb]. unfold E_RANGE.
        zs.
        eapply ct_exit with (cs16 := [CB 8 j0; C8 A2]) (dws := map (Z_to_bv 64) dot) (sb := sb)
          (segb := upd segb (Z.to_nat i) (Z_to_bv 8 (bv_unsigned r28))) (dv := dv); try eassumption.
        -- reflexivity.
        -- intros H0. discriminate H0.
      * nobr. rewrite (proj2 (Z.eqb_neq i 7) H7). cbn [andb].
        zs. zs.
        rewrite bit_i by lia.
        pose proof (lor_bit_lt d i Hd ltac:(lia)) as Hd'.
        eapply (l2_tail k' IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot i (seg ++ [nth (Z.to_nat (i - (8 - n))) s 0])
                  (Z.lor d (2 ^ i)) j0 sb _ dv); try eassumption; try lia.
        -- apply unsigned_lit. lia.
        -- apply Lseg'.
        -- apply Fseg'. exact E28.
        -- close_fr.
Qed.


Lemma l2_body : forall k', l2_ok k' -> l2_ok (S k').
Proof.
  intros k' IH r1 r7 r8 r11 r12 r13 r15 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 n s dot i seg d j0 sb segb dv m1
         Hk1 Hk Hi VI E11 E13 E12 Hd E15 Lseg Lsegb Fseg FR.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  pose proof FR as FR0.
  open_fr FR. basics.
  pose proof (eq_trans (length_map (Z_to_bv 64) dot) Ldot) as LDW.
  pose proof (u8arr_bound _ _ _ _ SEG) as BSEG. rewrite Lsegb in BSEG.
  pose proof (u8arr_bound _ _ _ _ SAR) as BSAR. rewrite Lsb in BSAR.
  unfold disj in DJ12.
  zs. rewrite swrap32_id by lia.
  zs. zs. nobr.
  zs.
  destruct (Z.ltb_spec (i - (8 - n)) 0) as [Hneg | Hnn].
  - yesbr. zs. zs. nobr.
    eapply (l2_store k' IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot i seg d j0 sb segb dv m1); try eassumption; try lia.
    rewrite (proj2 (Z.ltb_lt _ 0) Hneg). reflexivity.
  - nobr. zs. nobr. zs. nobr. zs.
    pose proof (u8arr_read rsegs m1 (bv_unsigned sp + -112) sb (i - (8 - n)) _ _ SAR
                  (sb_nth sb s (Z.to_nat n) (Z.to_nat (i - (8 - n))) Fsb ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as HR.
    zs. zs. nobr. zs.
    eapply (l2_store k' IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot i seg d j0 sb segb dv m1); try eassumption; try lia.
    rewrite (proj2 (Z.ltb_ge _ 0) Hnn). rewrite z8_of_64. apply z8_self.
Qed.

Lemma l2_all : forall k, l2_ok k.
Proof.
  induction k as [|k IH].
  - unfold l2_ok. intros. lia.
  - apply l2_body. exact IH.
Qed.


Ltac side := first [ lia | reflexivity | (apply u_swrap1; lia) | (rewrite Z.add_0_r; apply u_swrap1; lia)
                   | (apply unsigned_lit; lia) | close_fr ].

Lemma l2_entry : forall (r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 : word)
    (n : Z) (s dot : list Z) (j0 sb segb : list byte) (dv : byte) (m1 : word -> option byte),
  vinv n s dot sb -> bv_unsigned r22 = n -> length segb = 8%nat -> fr_ok m1 j0 dot sb segb dv ->
  evt rsegs (Qc (ct2 n s dot))
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp r5 r6 r7 r8 A1 r10 r11 r12 r13 r14 r15 r16 r17 r18
             (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -144) 18446744073709551615))
             (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -112) 18446744073709551615))
             r21 r22 r23 r24 r25 r26 r27 r28 r29 t5 t6)
        F (Z_to_bv 64 0x16080) fc None m1 (seg_rom rsegs)).
Proof.
  intros r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r18 r21 r22 r23 r24 r25 r26 r27 r28 r29 n s dot j0 sb segb
         dv m1 VI E22 Lsegb FR.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  pose proof FR as FR0. open_fr FR. basics.
  zs. zs. zs. rewrite swrap32_id by lia.
  zs. nobr.
  do 4 zs. zs. do 4 zs.
  unfold ct2.
  eapply (l2_all 8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n s dot 0 [] 0 j0 sb segb dv m1); try exact FR0; try eassumption.
  all: side.
Qed.


Local Abbreviation R1 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r22 r26 r28 r29 :=
  (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp r5 r6 r7 (Z_to_bv 64 8) A1 r10 r11 r12 r13 r14 r15 r16 r17 r18
       (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -144) 18446744073709551615))
       (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -112) 18446744073709551615))
       (Z_to_bv 64 (bv_unsigned sp + -144)) r22 (Z_to_bv 64 (bv_unsigned sp + -112)) (Z_to_bv 64 46) (Z_to_bv 64 7) r26
       (Z_to_bv 64 (-1)) r28 r29 t5 t6).

(** The first loop (head 0x15fdc) at text byte i = ch, non-zero, with n digits placed: the result is that of
    ct1_lib on the text from i; k bounds the bytes left. *)
Definition l1_ok (k : nat) : Prop :=
  forall (r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 : word) (i : nat) (ch n : Z) (s dot : list Z)
         (j0 sb segb : list byte) (dv : byte) (m1 : word -> option byte),
  (length tb - i <= k)%nat -> In 0 (skipn i (zb tb)) -> nth i (zb tb) 0 = ch -> ch <> 0 ->
  bv_unsigned r18 = bv_unsigned A0 + Z.of_nat i ->
  vinv n s dot sb -> length segb = 8%nat -> fr_ok m1 j0 dot sb segb dv -> bytes_at rsegs m1 (bv_unsigned A0) tb ->
  evt rsegs (Qc (ct_res (ct1_lib (skipn i (zb tb)) n s dot)))
    (MS (R1 r1 r5 r6 r7 (Z_to_bv 64 ch) r11 r12 r13 r14 r15 r16 r17 r18 (Z_to_bv 64 n) r26 r28 r29) F
        (Z_to_bv 64 0x15fdc) fc None m1 (seg_rom rsegs)).

Lemma l1_next : forall k, l1_ok k ->
  forall (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 : word) (i : nat) (n : Z) (s dot : list Z)
         (j0 sb segb : list byte) (dv : byte) (m1 : word -> option byte),
  (length tb - S i <= k)%nat -> In 0 (skipn (S i) (zb tb)) ->
  bv_unsigned r18 = bv_unsigned A0 + Z.of_nat i ->
  vinv n s dot sb -> length segb = 8%nat -> fr_ok m1 j0 dot sb segb dv -> bytes_at rsegs m1 (bv_unsigned A0) tb ->
  evt rsegs (Qc (ct_res (ct1_lib (skipn (S i) (zb tb)) n s dot)))
    (MS (R1 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 (Z_to_bv 64 n) r26 r28 r29) F
        (Z_to_bv 64 0x16060) fc None m1 (seg_rom rsegs)).
Proof.
  intros k IH r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 i n s dot j0 sb segb dv m1
         Hk HIn E18 VI Lsegb FR TXT.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  pose proof FR as FR0. open_fr FR. basics.
  pose proof (bytes_at_bound _ _ _ _ TXT) as BT.
  pose proof (In_skipn_len _ _ HIn) as Hi1. rewrite length_zb in Hi1.
  pose proof (bytes_at_byte m1 (bv_unsigned A0) tb (Z.of_nat (S i)) TXT ltac:(lia)) as HB.
  rewrite Nat2Z.id in HB.
  pose proof (bv_unsigned_in_range 8 (nth (S i) tb (Z_to_bv 8 0))) as Rb. unfold bv_modulus in Rb.
  zs. zs. zs.
  destruct (Z.eq_dec (bv_unsigned (nth (S i) tb (Z_to_bv 8 0))) 0) as [Hz | Hnz].
  - yesbr.
    assert (Ez : skipn (S i) (zb tb) = 0 :: skipn (S (S i)) (zb tb)).
    { rewrite (skipn_cons_nth _ (S i) 0) by (rewrite length_zb; lia). rewrite nth_zb, Hz. reflexivity. }
    rewrite Ez. cbn [ct1_lib Z.eqb ct_res].
    eapply l2_entry; try exact FR0; try eassumption.
    apply unsigned_lit. lia.
  - nobr. zs.
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S i) (bv_unsigned (nth (S i) tb (Z_to_bv 8 0))) n s dot j0 sb segb dv m1);
      try exact FR0; try eassumption.
    + apply nth_zb.
    + rewrite unsigned_lit by lia. lia.
Qed.

Lemma l1_tail : forall k, l1_ok k ->
  forall (r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 : word) (i : nat) (n v : Z) (s dot : list Z)
         (j0 sb segb : list byte) (dv : byte) (m1 : word -> option byte),
  (length tb - S i <= k)%nat -> In 0 (skipn (S i) (zb tb)) ->
  bv_unsigned r18 = bv_unsigned A0 + Z.of_nat i ->
  0 <= n < 8 -> 0 <= v < 128 ->
  ct_inv (n + 1) dot -> Forall (fun x => 0 <= x <= 1) dot -> Z.of_nat (length s) = n -> length sb = 8%nat ->
  firstn (Z.to_nat n) sb = bz s -> length segb = 8%nat ->
  fr_ok m1 j0 dot sb segb dv -> bytes_at rsegs m1 (bv_unsigned A0) tb ->
  evt rsegs (Qc (ct_res (ct1_lib (skipn (S i) (zb tb)) (n + 1) (s ++ [v]) dot)))
    (MS (R1 r1 r5 r6 r7 (Z_to_bv 64 v) r11 r12 r13 r14 r15 r16 r17 r18 (Z_to_bv 64 n) r26 r28 r29) F
        (Z_to_bv 64 0x16040) fc None m1 (seg_rom rsegs)).
Proof.
  intros k IH r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 i n v s dot j0 sb segb dv m1
         Hk HIn E18 Hn Hv CI D01 Ls Lsb Fsb Lsegb FR TXT.
  open_fr FR. basics.
  pose proof CI as (_ & Ldot & _).
  pose proof (eq_trans (length_map (Z_to_bv 64) dot) Ldot) as LDW.
  pose proof (u8arr_bound _ _ _ _ SEG) as BSEG. rewrite Lsegb in BSEG.
  pose proof (bytes_at_bound _ _ _ _ TXT) as BT.
  pose proof (In_skipn_len _ _ HIn) as Hi1. rewrite length_zb in Hi1.
  pose proof (u8arr_bound _ _ _ _ SAR) as BSAR. rewrite Lsb in BSAR.
  zs. rewrite swrap32_id by lia.
  zs. nobr. zs. nobr. zs. nobr. zs.
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -112 + n)) 1 = true)
    by (apply (u8arr_store_ok rsegs m1 (bv_unsigned sp + -112) sb n); [exact SAR | lia | reflexivity]).
  zs.
  rewrite le1_one, z8_of_64.
  pose proof (u8arr_write rsegs m1 (bv_unsigned sp + -112) sb n (Z_to_bv 8 v) SAR ltac:(lia)) as SAR'.
  clear SAR. store_done.
  zs. zs. nobr.
  eapply (l1_next k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i (n + 1) (s ++ [v]) dot j0
            (upd sb (Z.to_nat n) (Z_to_bv 8 v)) segb dv); try eassumption.
  - split; [exact CI|]. split; [exact D01|]. split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite Arr.upd_length; exact Lsb|].
    rewrite Z2N_succ by lia. rewrite (firstn_upd_snoc sb (bz s)); [| exact Fsb | lia].
    rewrite bz_snoc. reflexivity.
  - close_fr.
Qed.


Lemma l1_after : forall k, l1_ok k ->
  forall (r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r28 r29 : word) (i : nat) (ch v n : Z) (s dot : list Z)
         (j0 sb segb : list byte) (dv : byte) (m1 : word -> option byte),
  (length tb - S i <= k)%nat -> In 0 (skipn (S i) (zb tb)) -> bv_unsigned r18 = bv_unsigned A0 + Z.of_nat i ->
  (v = -1 \/ 0 <= v < 128) -> 0 <= ch < 256 ->
  vinv n s dot sb -> length segb = 8%nat -> fr_ok m1 j0 dot sb segb dv -> bytes_at rsegs m1 (bv_unsigned A0) tb ->
  evt rsegs (Qc (ct_res (ct1_rest v ch (skipn (S i) (zb tb)) n s dot)))
    (MS (R1 r1 r5 r6 r7 (Z_to_bv 64 v) r11 r12 r13 r14 r15 r16 r17 r18 (Z_to_bv 64 n) (Z_to_bv 64 ch) r28 r29) F
        (Z_to_bv 64 0x16018) fc None m1 (seg_rom rsegs)).
Proof.
  intros k IH r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r28 r29 i ch v n s dot j0 sb segb dv m1
         Hk HIn E18 Hv Hch VI Lsegb FR TXT.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  open_fr FR. basics.
  pose proof (eq_trans (length_map (Z_to_bv 64) dot) Ldot) as LDW.
  pose proof (u8arr_bound _ _ _ _ SEG) as BSEG. rewrite Lsegb in BSEG.
  pose proof (u8arr_bound _ _ _ _ SAR) as BSAR. rewrite Lsb in BSAR.
  pose proof (bytes_at_bound _ _ _ _ TXT) as BT.
  pose proof (In_skipn_len _ _ HIn) as Hi1. rewrite length_zb in Hi1.
  unfold ct1_rest.
  zs. zs.
  destruct Hv as [Hv | Hv].
  - yesbr. rewrite (proj2 (Z.ltb_lt v 0)) by lia. cbn [orb ct_res]. unfold E_RANGE.
    eapply ct_exit with (cs16 := [CB 8 j0; C8 A2]) (dws := map (Z_to_bv 64) dot) (sb := sb) (segb := segb)
      (dv := dv); try eassumption.
    + reflexivity.
    + intros H0. discriminate H0.
  - nobr. rewrite (proj2 (Z.ltb_ge v 0)) by lia. cbn [orb].
    zs.
    destruct (Z.eq_dec n 8) as [H8 | H8].
    + yesbr. rewrite (proj2 (Z.eqb_eq n 8) H8). cbn [ct_res]. unfold E_RANGE.
      eapply ct_exit with (cs16 := [CB 8 j0; C8 A2]) (dws := map (Z_to_bv 64) dot) (sb := sb) (segb := segb)
        (dv := dv); try eassumption.
      * reflexivity.
      * intros H0. discriminate H0.
    + nobr. rewrite (proj2 (Z.eqb_neq n 8) H8). cbn [orb].
      zs.
      destruct (Z.eq_dec ch 46) as [Hc | Hc].
      * nobr. rewrite (proj2 (Z.eqb_eq ch 46) Hc). cbn [orb].
        zs. nobr. zs. zs. nobr. zs. zs.
        assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -144 + 4 * n)) 4 = true)
          by (apply (u32arr_store_ok rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) n); [exact DOT | lia | reflexivity]).
        zs.
        pose proof (u32arr_write rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) n (Z_to_bv 64 1) DOT ltac:(lia))
          as DOT'.
        rewrite map_upd_at in DOT' by lia.
        clear DOT. store_done.
        eapply (l1_tail k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i n v s (upd_at dot n 1) j0 sb segb dv);
          try eassumption; try lia.
        -- apply ct_inv_next; [exact CI | lia].
        -- apply Forall_upd_at; [exact D01 | lia].
        -- close_fr.
      * yesbr. rewrite (proj2 (Z.eqb_neq ch 46) Hc). cbn [orb].
        eapply (l1_tail k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i n v s dot j0 sb segb dv);
          try eassumption; try lia.
        -- apply ct_inv_mono; [exact CI | lia].
        -- close_fr.
Qed.


Lemma l1_call : forall k, l1_ok k ->
  forall (r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r28 r29 : word) (i : nat) (ch n : Z) (s dot : list Z)
         (j0 sb segb : list byte) (dv : byte) (m1 : word -> option byte),
  (length tb - S i <= k)%nat -> In 0 (skipn (S i) (zb tb)) -> bv_unsigned r18 = bv_unsigned A0 + Z.of_nat i ->
  0 <= ch < 256 ->
  vinv n s dot sb -> length segb = 8%nat -> fr_ok m1 j0 dot sb segb dv -> bytes_at rsegs m1 (bv_unsigned A0) tb ->
  evt rsegs (Qc (ct_res (ct1_rest (seg7_spec (if ch =? 46 then 32 else ch)) ch (skipn (S i) (zb tb)) n s dot)))
    (MS (R1 r1 r5 r6 r7 (Z_to_bv 64 ch) r11 r12 r13 r14 r15 r16 r17 r18 (Z_to_bv 64 n) (Z_to_bv 64 ch) r28 r29) F
        (Z_to_bv 64 0x16008) fc None m1 (seg_rom rsegs)).
Proof.
  intros k IH r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r28 r29 i ch n s dot j0 sb segb dv m1
         Hk HIn E18 Hch VI Lsegb FR TXT.
  pose proof FR as FR0. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HMI).
  pose proof (seg7_range (if ch =? 46 then 32 else ch) ltac:(destruct (ch =? 46); lia)) as Hv.
  zs.
  destruct (Z.eq_dec ch 46) as [Hc | Hc].
  - nobr. zs. zs. zs.
    eapply evt_cut; [eapply SEG7; exact HMI | intros ms' [a1' ->]].
    replace (ret_pc (Z_to_bv 64 90136)) with (Z_to_bv 64 90136) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    match goal with |- context [Z_to_bv 64 (seg7_spec ?x)] =>
      replace x with (if ch =? 46 then 32 else ch)
        by (transitivity 32; [rewrite (proj2 (Z.eqb_eq ch 46) Hc); reflexivity | rewrite ?unsigned_lit by lia; reflexivity])
    end.
    eapply (l1_after k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ i ch (seg7_spec (if ch =? 46 then 32 else ch)) n s dot j0 sb segb dv m1);
      try exact FR0; try eassumption; try lia.
  - yesbr. zs. rewrite land255 by lia. zs.
    eapply evt_cut; [eapply SEG7; exact HMI | intros ms' [a1' ->]].
    replace (ret_pc (Z_to_bv 64 90136)) with (Z_to_bv 64 90136) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    match goal with |- context [Z_to_bv 64 (seg7_spec ?x)] =>
      replace x with (if ch =? 46 then 32 else ch)
        by (transitivity ch; [rewrite (proj2 (Z.eqb_neq ch 46) Hc); reflexivity
                             | rewrite ?unsigned_lit by lia; symmetry; apply Z.mod_small; lia])
    end.
    eapply (l1_after k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ i ch (seg7_spec (if ch =? 46 then 32 else ch)) n s dot j0 sb segb dv m1);
      try exact FR0; try eassumption; try lia.
Qed.

Lemma l1_body : forall k, l1_ok k -> l1_ok (S k).
Proof.
  intros k IH r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 i ch n s dot j0 sb segb dv m1
         Hk HIn Ech Hc0 E18 VI Lsegb FR TXT.
  pose proof VI as (CI & D01 & Ls & Lsb & Fsb). pose proof CI as (Hn & Ldot & Zdot).
  pose proof FR as FR0. open_fr FR. basics.
  pose proof (eq_trans (length_map (Z_to_bv 64) dot) Ldot) as LDW.
  pose proof (u8arr_bound _ _ _ _ SEG) as BSEG. rewrite Lsegb in BSEG.
  pose proof (u8arr_bound _ _ _ _ SAR) as BSAR. rewrite Lsb in BSAR.
  pose proof (bytes_at_bound _ _ _ _ TXT) as BT.
  destruct (skip_step _ _ _ HIn Ech Hc0) as (Esk & HIn' & Hi1). rewrite length_zb in Hi1.
  assert (Hch : 0 <= ch < 256).
  { rewrite <- Ech, nth_zb. pose proof (bv_unsigned_in_range 8 (nth i tb (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. exact R. }
  assert (Hk' : (length tb - S i <= k)%nat) by lia.
  rewrite Esk, ct1_cons by exact Hc0.
  zs. rewrite land255 by lia.
  zs.
  destruct (Z.eq_dec ch 46) as [Hc | Hc].
  - nobr. zs.
    destruct (Z.eq_dec n 0) as [Hn0 | Hnp].
    + yesbr.
      assert (Hcond : (ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0) = false)
        by (apply andb_false_iff; left; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      rewrite (ifb_false _ _ _ Hcond).
      eapply (l1_call k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ i ch n s dot j0 sb segb dv m1); try exact FR0; try eassumption.
    + nobr. zs. zs. nobr. zs. zs. zs. nobr. zs.
      pose proof (Forall_nth01 dot (Z.to_nat (n - 1)) D01) as Hfv.
      pose proof (u32arr_read rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) (n - 1) _ _ DOT
                    (nth_error_mapz dot (Z.to_nat (n - 1)) ltac:(lia)) ltac:(lia) eq_refl) as HR.
      zs. rewrite sx32_small by lia. zs.
      destruct (Z.eq_dec (nth (Z.to_nat (n - 1)) dot 0) 0) as [Hz | Hnz].
      * yesbr.
        assert (Hcond : (ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0) = true).
        { apply andb_true_iff. split; [apply andb_true_iff; split; [apply Z.eqb_eq; exact Hc | apply Z.ltb_lt; lia]|].
          apply Z.eqb_eq. exact Hz. }
        rewrite (ifb_true _ _ _ Hcond).
        zs.
        assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -144 + 4 * (n - 1))) 4 = true)
          by (apply (u32arr_store_ok rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) (n - 1));
              [exact DOT | lia | reflexivity]).
        zs.
        pose proof (u32arr_write rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) (n - 1) (Z_to_bv 64 1) DOT
                      ltac:(lia)) as DOT'.
        rewrite map_upd_at in DOT' by lia.
        clear DOT. store_done.
        zs. nobr. zs.
        eapply (l1_next k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i n s (upd_at dot (n - 1) 1) j0 sb segb dv);
          try eassumption.
        -- split; [apply ct_inv_dot; [exact CI | lia]|]. split; [apply Forall_upd_at; [exact D01 | lia]|].
           split; [exact Ls|]. split; [exact Lsb | exact Fsb].
        -- close_fr.
      * nobr.
        assert (Hcond : (ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0) = false)
          by (apply andb_false_iff; right; apply Z.eqb_neq; exact Hnz).
        rewrite (ifb_false _ _ _ Hcond).
        eapply (l1_call k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ i ch n s dot j0 sb segb dv m1); try exact FR0; try eassumption.
  - yesbr.
    assert (Hcond : (ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0) = false)
      by (rewrite (proj2 (Z.eqb_neq ch 46) Hc); reflexivity).
    rewrite (ifb_false _ _ _ Hcond).
    eapply (l1_call k IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ i ch n s dot j0 sb segb dv m1); try exact FR0; try eassumption.
Qed.

Lemma l1_all : forall k, l1_ok k.
Proof.
  induction k as [|k IH].
  - intros r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r18 r26 r28 r29 i ch n s dot j0 sb segb dv m1 Hk HIn.
    pose proof (In_skipn_len _ _ HIn) as H. rewrite length_zb in H. lia.
  - apply l1_body. exact IH.
Qed.

(** From the entry of diginet_counter_text: frame, NULL tests (not taken), the first byte, then either loop. *)
Lemma ct_entry : forall (sj : list byte) (dj : byte) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 : word),
  bv_unsigned A0 <> 0 -> bytes_at rsegs m (bv_unsigned A0) tb -> In (b8 0) tb ->
  bv_unsigned A1 <> 0 -> rw_cells rsegs m (bv_unsigned A1) [CB 8 sj] ->
  bv_unsigned A2 <> 0 -> rw_cells rsegs m (bv_unsigned A2) [C1 dj] ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs (Qc (counter_text_spec (zb tb)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 A0 A1 A2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15f4c) fc None m (seg_rom rsegs)).
Proof.
  intros sj dj t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 NZ0 TXT ZT NZ1 SEGC NZ2 DTS HMI ST.
  pose proof (munch_refl Wct m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold Wct, DIGINET_COUNTER_TEXT_DEPTH in MU.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 A0) as RA0.
  pose proof (bv_unsigned_in_range 64 A1) as RA1. pose proof (bv_unsigned_in_range 64 A2) as RA2.
  unfold bv_modulus in Rsp, RA0, RA1, RA2.
  pose proof ST as [Hlo _].
  pose proof (bytes_at_bound _ _ _ _ TXT) as BT.
  pose proof (rw_cells_CB_length _ _ _ _ SEGC) as LSJ.
  apply u8arr_of_rw_cells in SEGC.
  carve_frame 160%nat ST.
  do 14 zstep.
  zstep.
  do 4 zstep.
  zstep.
  zstep. nobr.
  zstep. nobr.
  zstep.
  zstep. nobr.
  zstep.
  assert (LT0 : (0 < length tb)%nat) by (destruct tb; [destruct ZT | cbn; lia]).
  pose proof (bytes_at_byte _ _ _ 0 TXT ltac:(lia)) as HB0.
  rewrite Z.add_0_r in HB0. unfold wa in HB0. rewrite Z_to_bv_bv_unsigned in HB0.
  pose proof (bv_unsigned_in_range 8 (nth 0 tb (Z_to_bv 8 0))) as Rb0. unfold bv_modulus in Rb0.
  zstep.
  do 5 zstep.
  match type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
    change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c1; c2] ++ [c3; c4; c5; c6] ++ [c7] ++ rest) in FR
  end.
  apply rw_cells_app_split in FR. destruct FR as [FRL FR]. cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -160 + Z.of_nat 16) with (bv_unsigned sp + -144) in FR by lia.
  apply rw_cells_app_split in FR. destruct FR as [DOT FR]. cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -144 + Z.of_nat 32) with (bv_unsigned sp + -112) in FR by lia.
  apply rw_cells_app_split in FR. destruct FR as [SAR FRH]. cbn [cells_size csize Nat.add] in FRH.
  replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -104) in FRH by lia.
  apply dot_zero_u32arr in DOT.
  pose proof (rw_cells_CB_length _ _ _ _ SAR) as LSB. apply u8arr_of_rw_cells in SAR.
  match type of SAR with u8arr _ _ _ ?sbj =>
    assert (VI : vinv 0 [] (repeat 0 8) sbj)
  end.
  { split; [apply ct_inv_0|]. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
    split; [reflexivity|]. split; [exact LSB | reflexivity]. }
  change (counter_text_spec (zb tb)) with (ct_res (ct1_lib (zb tb) 0 [] (repeat 0 8))).
  zstep. if_cases K.
  - zify_cond K. change (Z.to_nat 0) with 0%nat in K.
    assert (E0 : zb tb = 0 :: skipn 1 (zb tb)).
    { pose proof (skipn_cons_nth (zb tb) 0 0 ltac:(rewrite length_zb; lia)) as E. cbn [skipn] in E.
      rewrite nth_zb, K in E. exact E. }
    rewrite E0. cbn [ct1_lib Z.eqb ct_res].
    eapply l2_entry with (n := 0) (s := []) (dot := repeat 0 8) (segb := sj) (dv := dj); try eassumption.
    + apply unsigned_lit. lia.
    + close_fr.
  - zify_cond K. change (Z.to_nat 0) with 0%nat in K. do 4 zstep.
    eapply (l1_all (length tb) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%nat (bv_unsigned (nth 0 tb (Z_to_bv 8 0))) 0 [] (repeat 0 8) _ _ sj dj);
      try eassumption.
    all: first [ lia | (cbn [skipn]; apply (in_map (fun b : byte => bv_unsigned b) tb (b8 0) ZT)) | apply nth_zb
               | close_fr ].
Qed.

End CT.

Theorem diginet_counter_text_holds : diginet_seg7_contract -> diginet_counter_text_contract.
Proof.
  intros SEG7. unfold diginet_counter_text_contract, DIGINET_COUNTER_TEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo tb sj dj PRE.
  destruct PRE as (NZ0 & [TXT ZT] & NZ1 & SEGC & NZ2 & DTS & DJ & L0 & L1 & L2 & HMI & ST & LO).
  unfold DIGINET_COUNTER_TEXT_DEPTH in LO.
  eapply ct_entry; eassumption.
Qed.
