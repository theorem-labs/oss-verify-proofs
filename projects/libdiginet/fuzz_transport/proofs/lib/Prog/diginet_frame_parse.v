(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_parse.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_frame_parse (src/diginet_frame.c:60-91 at 835f336c) in fuzz_transport.plain,
   0x1771c..0x178d8, against diginet_frame_parse_c.v. The binary inlines rd16 (0x1775c,
   0x17778, 0x177cc, 0x17838), rd32 (0x177e0, 0x1780c) and the diginet_sum16 loop
   (0x17888..0x17894, then the cut to 16 bits at 0x17898); it calls memcpy (0x1f910) for dst
   and src. The callee contract memcpy_contract is the premise of the theorem.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import FrameBytes memcpy_c diginet_frame_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** * Arithmetic of the inlined rd16, rd32 and diginet_sum16 *)

Lemma testbit_split_k : forall x y k i, 0 <= k -> 0 <= x < 2^k -> 0 <= i ->
  Z.testbit (x + y * 2^k) i = if i <? k then Z.testbit x i else Z.testbit y (i - k).
Proof.
  intros x y k i Hk Hx Hi. destruct (Z.ltb_spec i k) as [L|L].
  - rewrite <- (Z.mod_pow2_bits_low (x + y * 2^k) k i) by lia.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
  - replace i with ((i - k) + k) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.div_add by (apply Z.pow_nonzero; lia). rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma lor_shl : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, testbit_split_k by lia.
  destruct (Z.ltb_spec i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply orb_false_r.
  - rewrite Z.mul_pow2_bits by lia. rewrite (testbit_high_false x k i) by lia. reflexivity.
Qed.

(* rd16 at index i: (p[0] << 8) | p[1], as slli and or compute it. *)
Lemma pack16_be : forall l i,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (Z_to_bv 8 0)))) 8)))
        (bv_unsigned (zxb (nth (S i) l (Z_to_bv 8 0)))) = be16 l i.
Proof.
  intros l i. unfold be16, at8, bz, b8, zxb.
  set (x0 := bv_unsigned (nth i l (Z_to_bv 8 0))).
  set (x1 := bv_unsigned (nth (S i) l (Z_to_bv 8 0))).
  assert (R0 : 0 <= x0 < 256) by apply byte_range.
  assert (R1 : 0 <= x1 < 256) by apply byte_range.
  rewrite (unsigned_lit x0), (unsigned_lit x1) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (x0 * 2^8)) by lia.
  rewrite Z.lor_comm, lor_shl by lia. lia.
Qed.

(* rd32 at index i: the two high bytes or-ed first, then the rd16 of the two low bytes. *)
Lemma pack32_be : forall l i,
  Z.lor (bv_unsigned (Z_to_bv 64
          (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth (S i) l (Z_to_bv 8 0)))) 16)))
                 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (Z_to_bv 8 0)))) 24))))))
        (bv_unsigned (Z_to_bv 64 (be16 l (S (S i))))) = be32 l i.
Proof.
  intros l i. unfold be32, be16, at8, bz, b8, zxb.
  set (x0 := bv_unsigned (nth i l (Z_to_bv 8 0))).
  set (x1 := bv_unsigned (nth (S i) l (Z_to_bv 8 0))).
  set (x2 := bv_unsigned (nth (S (S i)) l (Z_to_bv 8 0))).
  set (x3 := bv_unsigned (nth (S (S (S i))) l (Z_to_bv 8 0))).
  assert (R0 : 0 <= x0 < 256) by apply byte_range.
  assert (R1 : 0 <= x1 < 256) by apply byte_range.
  assert (R2 : 0 <= x2 < 256) by apply byte_range.
  assert (R3 : 0 <= x3 < 256) by apply byte_range.
  rewrite (unsigned_lit x0), (unsigned_lit x1) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x1 * 2^16)), (unsigned_lit (x0 * 2^24)) by lia.
  rewrite (lor_shl (x1 * 2^16) x0 24) by lia.
  rewrite (unsigned_lit (x1 * 2^16 + x0 * 2^24)) by lia.
  rewrite (unsigned_lit (x2 * 2^8 + x3)) by lia.
  rewrite Z.lor_comm.
  replace (x1 * 2^16 + x0 * 2^24) with ((x1 + x0 * 2^8) * 2^16) by ring.
  rewrite (lor_shl (x2 * 2^8 + x3) (x1 + x0 * 2^8) 16) by lia. lia.
Qed.

(* The cut of the 64-bit sum to uint16_t: slli 48, then srli 48. *)
Lemma shl48_shr48 : forall s,
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 s)) 48))) 48 = s mod 2^16.
Proof.
  intros s. rewrite (unsigned_lit_wrap s). rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((s mod 2^64 * 2^48) mod 2^64) with ((s mod 2^64 * 2^48) mod (2^16 * 2^48)) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
  apply mod_mod_pow2. lia.
Qed.

(* sum_matches: xor of the two sums, then seqz, stored as one byte. *)
Lemma seqz_cell : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 ->
  Z_to_bv 8 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 y)))) 1))
  = b8 (if y =? x then 1 else 0).
Proof.
  intros x y Hx Hy. rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  assert (RX : 0 <= Z.lxor x y < 2^16).
  { split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [rewrite E; lia|].
    apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg x y); lia|].
    pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)) as L.
    assert (Z.log2 x < 16) by (destruct (Z.eq_dec x 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
    assert (Z.log2 y < 16) by (destruct (Z.eq_dec y 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
    lia. }
  unfold v_sltiu. rewrite (unsigned_lit (Z.lxor x y)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec y x) as [->|N].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (NZ : Z.lxor x y <> 0) by (intros E; apply (proj1 (Z.lxor_eq_0_iff x y)) in E; exact (N (eq_sym E))).
    replace (Z.lxor x y <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma le1_any : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma bv_eqb_pos : forall x y, 0 < x <= 2^64 -> 0 < y <= 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (Mx : x mod 2^64 = if x =? 2^64 then 0 else x).
  { destruct (Z.eqb_spec x (2^64)) as [->|]; [apply Z_mod_same_full | apply Z.mod_small; lia]. }
  assert (My : y mod 2^64 = if y =? 2^64 then 0 else y).
  { destruct (Z.eqb_spec y (2^64)) as [->|]; [apply Z_mod_same_full | apply Z.mod_small; lia]. }
  rewrite Mx, My in E.
  destruct (Z.eqb_spec x (2^64)); destruct (Z.eqb_spec y (2^64)); lia.
Qed.

(** * Memory facts *)

Lemma bytes_at_sub : forall m A l k n, bytes_at rsegs m A l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hkn. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_cut : forall m A n l k, rw_cells rsegs m A [CB n l] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k l)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k l)].
Proof.
  intros m A n l k [[Hwf Hb] Hw] Hk. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. destruct Hw as (W1 & W2 & W).
  rewrite <- (firstn_skipn k l) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min k (length l)) with k in B2 by lia.
  split; split; [split| |split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2, rw_cells rsegs m A cs1 ->
  rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] R1] [[W2 B2] R2].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. destruct R1 as (a1 & a2 & R1). destruct R2 as (b1 & b2 & R2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i (Z.of_nat (cells_size cs1))); [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma rw_cells_ext : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros; subst; assumption. Qed.

(* The stack stays readable and writable across a callee whose footprint is a cell block it
   leaves readable. *)
Lemma stk_after_call : forall m m' lo hi a n cs,
  stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' -> rw_cells rsegs m' a cs ->
  Z.of_nat (cells_size cs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n cs (H1 & H2 & H) MU WM RW Hn.
  pose proof (stk_of_rw_cells rsegs m' a cs RW) as (S1 & S2 & S).
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw [b0 Hb]].
  split; [apply WM; exact Hw|].
  destruct (Z_le_gt_dec a x) as [Ha|Ha]; [destruct (Z_lt_ge_dec x (a + n)) as [Hb2|Hb2]|].
  - destruct (S x ltac:(lia)) as [_ E]. exact E.
  - exists b0. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia.
    cbn [outside]. split; [lia|exact I].
  - exists b0. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia.
    cbn [outside]. split; [lia|exact I].
Qed.

(** * The post and the epilogue (0x178bc) *)

(* The post of diginet_frame_parse_contract, as a definition; every exit of the walk ends in it. *)
Definition fp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo buf f : Z) (b fj : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fr_code b)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp); (f, f + 64)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' f (if fr_code b =? 0 then parse_cells buf b fj else [CB 64 fj]).

(* 0x178bc: the epilogue loads ra and s0..s3 back, frees the 48-byte frame and returns. *)
Lemma fp_exit : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo buf f : Z) (b fj : list byte) (m1 : word -> option byte) (j8 : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  lo + 48 <= bv_unsigned sp ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (f, f + 64)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 f (if fr_code b =? 0 then parse_cells buf b fj else [CB 64 fj]) ->
  x10 = Z_to_bv 64 (fr_code b) ->
  evt rsegs (fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf f b fj)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x178bc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf f b fj m1 j8
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 HLO ST FR MU WM MI HCf E10.
  subst x10. pose proof (u64_range sp) as Rsp.
  do 7 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold fp_post.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact HCf].
Qed.

(** * The loop of diginet_sum16 (0x17888..0x17894) and the cut to 16 bits (0x17898) *)

Lemma sum_loop : forall (P : machine_state -> Prop) (m : word -> option byte) (A : Z) (body : list byte)
    (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (k i : nat) (x10 x12 x14 : word),
  bytes_at rsegs m A body -> 0 < A ->
  (i + S k = length body)%nat ->
  x10 = Z_to_bv 64 (A + Z.of_nat i) ->
  x12 = Z_to_bv 64 (sum_bytes (firstn i body)) ->
  x13 = Z_to_bv 64 (A + Z.of_nat (length body)) ->
  (forall x10' x14' : word,
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' x11 (Z_to_bv 64 (sum16 body)) x13 x14' x15 x16 x17 x18 x19
                          x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x178a0) fc None m (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x17888) fc None m (seg_rom rsegs)).
Proof.
  intros P m A body F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 k.
  induction k as [|k IH]; intros i x10 x12 x14 HB HA Hk E10 E12 E13 K; subst x10 x12 x13.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: pose proof (rd1 _ _ _ i HB ltac:(lia)) as R.
  all: assert (ES : sum_bytes (firstn i body) + bv_unsigned (zxb (nth i body (Z_to_bv 8 0)))
                    = sum_bytes (firstn (S i) body))
         by (rewrite (sum_bytes_firstn_S body i) by lia; unfold at8, bz, b8, zxb;
             rewrite unsigned_lit by (pose proof (byte_range (nth i body (Z_to_bv 8 0))); lia); reflexivity).
  all: step; step; step; rewrite ES; step.
  all: rewrite bv_eqb_pos by lia.
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat (length body)) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota.
    step. step. rewrite shl48_shr48.
    rewrite firstn_all2 by lia. apply K.
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat (length body)) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    eapply (IH (S i)); [exact HB | exact HA | lia | f_equal; lia | reflexivity | reflexivity | exact K].
Qed.

(** * The walk *)

Lemma rw_cells_addr : forall m A A' cs, rw_cells rsegs m A cs -> A = A' -> rw_cells rsegs m A' cs.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_join3 : forall m A c1 c2 cs, rw_cells rsegs m A [c1] -> rw_cells rsegs m (A + 6) [c2] ->
  rw_cells rsegs m (A + 12) cs -> csize c1 = 6%nat -> csize c2 = 6%nat -> rw_cells rsegs m A (c1 :: c2 :: cs).
Proof.
  intros m A c1 c2 cs H1 H2 H3 S1 S2.
  change (c1 :: c2 :: cs) with ([c1] ++ [c2] ++ cs).
  apply rw_cells_app; [exact H1|].
  apply rw_cells_app.
  - eapply rw_cells_addr; [exact H2|]. cbn [cells_size]. rewrite S1. lia.
  - eapply rw_cells_addr; [exact H3|]. cbn [cells_size]. rewrite S1, S2. lia.
Qed.

(* A byte store of a register that is not a loaded byte: le1 v is the one byte of v. *)
Ltac mem_after_store_opt ::=
  try rewrite le1_zxb;
  try rewrite le1_any;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
Ltac st := step; rewrite ?pack32_be, ?pack16_be.
Ltac rdb HB i :=
  let R := fresh "R" in pose proof (rd1 _ _ _ i HB ltac:(lia)) as R;
  let z := eval vm_compute in (Z.of_nat i) in change (Z.of_nat i) with z in R.
Ltac fc_tac := unfold fr_code, fr_ethertype, fr_numbytes;
  repeat match goal with
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec x y)
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
  end; cbn [negb orb]; lia.
Ltac fix_ret := lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
(* The exits with a code that is not 0: f is untouched. *)
Ltac exit_nz := eapply fp_exit;
  [ lia | eassumption | eassumption | eassumption | eassumption | eassumption
  | lazymatch goal with |- rw_cells _ _ _ (if ?c then _ else _) =>
      replace c with false by (symmetry; apply Z.eqb_neq; fc_tac) end; eassumption
  | f_equal; fc_tac ].

(* 0x178a0: sum_matches and body_sum stored, then the return. The 64 bytes at f are the cells
   parse_cells gives: the five cells that are not equal by computation are the EtherType (the
   constant 0x885F, tested at 0x17774), cmd and num_commands (loaded bytes), pad_len (sub and
   addi) and sum_matches (xor and seqz). *)
Ltac fp_tail FC0 ET RWc RWc2 H12 :=
  do 6 st;
  eapply fp_exit;
  [ lia | eassumption | eassumption | eassumption | eassumption | eassumption
  | | rewrite FC0; reflexivity ];
  rewrite FC0; change (0 =? 0) with true; cbv iota beta;
  eapply rw_cells_ext;
  [ eapply rw_cells_join3; [exact RWc | exact RWc2 | exact H12 | reflexivity | reflexivity] | ];
  unfold parse_cells, fr_dst, fr_src; rewrite ?skipn_skipn; cbn [Nat.add];
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end;
  first
    [ unfold fr_ethertype; rewrite ET; reflexivity
    | unfold fr_cmd, fr_ncmds, at8; rewrite b8_bz; reflexivity
    | f_equal; apply seqz_cell; [apply sum16_range | apply be16_range]
    | f_equal; uns; unfold fr_pad_len, fr_body_len, fr_numbytes; f_equal; lia ].

Theorem diginet_frame_parse_holds : memcpy_contract -> diginet_frame_parse_contract.
Proof.
  intros MC. unfold memcpy_contract in MC. unfold diginet_frame_parse_contract, DIGINET_FRAME_PARSE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f lo b fj
    Hbuf Hf HB HC DBF ST LO DBS DFS MI.
  lazymatch goal with |- evt _ ?Q _ =>
    change Q with (fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf f b fj) end.
  pose proof (u64_range sp) as Rsp.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. cbn [cells_size csize Nat.add] in BC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (f, f + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  (* 0x1771c: the frame; ra, s0..s3 saved *)
  do 6 step.
  (* 0x17734: buf and f are not NULL *)
  do 3 step. br false.
  do 2 step. br false.
  (* 0x17748: fewer than 30 bytes *)
  do 3 step.
  destruct (Nat.ltb_spec (length b) 30) as [L30|L30].
  { br false. do 2 step. exit_nz. }
  br true.
  pose proof (be16_range b 12) as R12. pose proof (be16_range b 14) as R14.
  (* 0x1775c: rd16 (buf + 12), the EtherType *)
  rdb HB 12%nat. rdb HB 13%nat.
  do 7 st.
  destruct (Z.eqb_spec (be16 b 12) 0x885f) as [ET|ET].
  2:{ br true. step. exit_nz. }
  br false.
  (* 0x17778: rd16 (buf + 14), numbytes *)
  rdb HB 14%nat. rdb HB 15%nat.
  do 7 st.
  destruct (Z.ltb_spec (be16 b 14) 16) as [N16|N16].
  { br true. exit_nz. }
  br false.
  do 2 st.
  destruct (Z.ltb_spec (Z.of_nat (length b) - 14) (be16 b 14)) as [NL|NL].
  { br true. exit_nz. }
  br false.
  assert (FC0 : fr_code b = 0) by fc_tac.
  (* f in three pieces: dst, src and the rest *)
  destruct (rw_cells_cut _ _ _ _ 6 HC ltac:(lia)) as [HD0 HC6]. clear HC.
  change (64 - 6)%nat with 58%nat in HC6. change (f + Z.of_nat 6) with (f + 6) in HC6.
  destruct (rw_cells_cut _ _ _ _ 6 HC6 ltac:(lia)) as [HS0 H12]. clear HC6.
  change (58 - 6)%nat with 52%nat in H12. rewrite skipn_skipn in H12.
  replace (f + 6 + Z.of_nat 6) with (f + 12) in H12 by lia. change (6 + 6)%nat with 12%nat in H12.
  (* 0x1779c: memcpy (f, buf, 6) *)
  do 4 st.
  eapply evt_cut.
  { eapply MC with (src := firstn 6 b) (junk := firstn 6 fj).
    - rewrite (unsigned_lit buf) by lia. pose proof (bytes_at_sub _ _ _ 0 6 HB ltac:(lia)) as X.
      cbn [Z.of_nat skipn] in X. rewrite Z.add_0_r in X. exact X.
    - rewrite length_firstn. change (bv_unsigned (Z_to_bv 64 6)) with 6. lia.
    - rewrite (unsigned_lit f) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6.
      change (Z.to_nat 6) with 6%nat. exact HD0.
    - rewrite (unsigned_lit f), (unsigned_lit buf) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6. lia.
    - exact MI. }
  intros ms' POST.
  destruct POST as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1
                    & E & MUc & WMc & MIc & RWc & BAc).
  subst ms'.
  rewrite (unsigned_lit f) in MUc, RWc by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6 in MUc, RWc.
  change (Z.to_nat 6) with 6%nat in RWc. clear BAc.
  eapply stk_after_call in ST; [ | exact MUc | exact WMc | exact RWc | reflexivity ].
  lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call rsegs mo mn MUc WMc end.
  clear MUc WMc MI. rename MIc into MI. fix_ret.
  (* 0x177ac: memcpy (f + 6, buf + 6, 6) *)
  do 4 st.
  eapply evt_cut.
  { eapply MC with (src := firstn 6 (skipn 6 b)) (junk := firstn 6 (skipn 6 fj)).
    - rewrite (unsigned_lit (buf + 6)) by lia. pose proof (bytes_at_sub _ _ _ 6 6 HB ltac:(lia)) as X.
      change (Z.of_nat 6) with 6 in X. exact X.
    - rewrite length_firstn, length_skipn. change (bv_unsigned (Z_to_bv 64 6)) with 6. lia.
    - rewrite (unsigned_lit (f + 6)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6.
      change (Z.to_nat 6) with 6%nat. exact HS0.
    - rewrite (unsigned_lit (f + 6)), (unsigned_lit (buf + 6)) by lia.
      change (bv_unsigned (Z_to_bv 64 6)) with 6. lia.
    - exact MI. }
  intros ms' POST.
  destruct POST as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m2
                    & E & MUc & WMc & MIc & RWc2 & BAc).
  subst ms'.
  rewrite (unsigned_lit (f + 6)) in MUc, RWc2 by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6 in MUc, RWc2.
  change (Z.to_nat 6) with 6%nat in RWc2. clear BAc.
  eapply stk_after_call in ST; [ | exact MUc | exact WMc | exact RWc2 | reflexivity ].
  lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call rsegs mo mn MUc WMc end.
  clear MUc WMc MI. rename MIc into MI. fix_ret.
  (* 0x177bc: the EtherType and numbytes stored *)
  do 4 st.
  (* 0x177cc: rd16 (h + 2), the sum *)
  rdb HB 16%nat. rdb HB 17%nat. do 5 st.
  (* 0x177e0: rd32 (h + 4), the send counter *)
  rdb HB 18%nat. rdb HB 19%nat. rdb HB 20%nat. rdb HB 21%nat. do 11 st.
  (* 0x1780c: rd32 (h + 8), the ack counter *)
  rdb HB 22%nat. rdb HB 23%nat. rdb HB 24%nat. rdb HB 25%nat. do 11 st.
  (* 0x17838: rd16 (h + 12), retry *)
  rdb HB 26%nat. rdb HB 27%nat. do 5 st.
  (* 0x1784c: cmd, num_commands, body, body_len, pad_len *)
  rdb HB 28%nat. do 3 st.
  rdb HB 29%nat. do 8 st.
  (* 0x17878: the sum of the body *)
  do 2 st.
  pose proof (fr_body_len_ok b FC0) as (BL0 & PL0 & BLe).
  pose proof (length_fr_body b FC0) as LFB.
  assert (BLv : fr_body_len b = be16 b 14 - 16) by reflexivity.
  destruct (Z.eqb_spec (be16 b 14) 16) as [B16|B16].
  - (* body_len = 0: the loop is skipped, the sum is 0 *)
    br true.
    assert (S0 : sum16 (fr_body b) = 0) by (unfold fr_body, fr_body_len, fr_numbytes; rewrite B16; reflexivity).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (sum16 (fr_body b))) by (rewrite S0; reflexivity).
    fp_tail FC0 ET RWc RWc2 H12.
  - (* 0x17880: the end of the body, then the loop over buf + 30 .. buf + 30 + body_len *)
    br false. do 2 st.
    pose proof (bytes_at_sub _ _ _ 30 (Z.to_nat (fr_body_len b)) HB ltac:(lia)) as HB30.
    change (Z.of_nat 30) with 30 in HB30.
    eapply (sum_loop _ _ (buf + 30) (fr_body b)) with (k := (length (fr_body b) - 1)%nat) (i := 0%nat);
      [ exact HB30 | lia | lia | f_equal; lia | reflexivity
      | f_equal; rewrite LFB; lia | intros x10' x14'; clear HB30; fp_tail FC0 ET RWc RWc2 H12 ].
Qed.
