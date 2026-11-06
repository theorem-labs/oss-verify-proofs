(* Walks of fuzz_lock.ubsan's LLVMFuzzerTestOneInput (fuzz_lock.c:181-207), 0x12bbc, between its two calls:
   lt_entry (0x12bbc to the return or to check_no_overread's entry), lt_mid (0x12cec to check_lookup's entry) and
   lt_exit (0x12d04 through the epilogue to the return). The UBSan trap [unimp] at 0x12d28 is reached from six
   branches and none is taken:
   - 0x12be4 [beqz a0], a0 = data: data is a block of the caller, 4096 <= data;
   - 0x12c18 [bltu ~RATES, a3], a3 = 8 * (data[0] mod 5) <= 32: RATES + a3 does not wrap;
   - 0x12c20 [beq a0, -1], a0 = data: data < 2 ^ 63;
   - 0x12c74 [beqz a5], a5 = (data + 2) masked by -(data <u -2): 4096 <= data < 2 ^ 63, so a5 = data + 2 <> 0;
   - 0x12cac [bltu ~(sp + 8), s0] and 0x12cc8 [bltu ~(data + 2), s0], s0 = k <= 15: sp + 8 + k and data + 2 + k
     do not wrap;
   - 0x12cbc [bltu -3, a0], a0 = data: data + 2 does not wrap.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac showc := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => idtac "C:" c end.
Ltac lt_w :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end;
  first [ reflexivity
        | match goal with |- Z_to_bv 64 ?a = ?x => replace a with (bv_unsigned x) by lia; apply Z_to_bv_bv_unsigned end
        | f_equal; lia
        | apply Z_to_bv_eqm; f_equal; lia ].
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
(* the UBSan pointer-overflow check [not r, x; bltu r, n]: not taken when x + n < 2 ^ 64 *)
Ltac trapbr x := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota
      | symmetry; unfold_cond; fold_lit_ux; rewrite (unsigned_lit x) by lia;
        try change (bv_wrap 64 (-1)) with 18446744073709551615;
        rewrite zb_lxor_ones by lia; uns; solve_cond_rec]
  end.

Lemma land_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply firstn1_skipn. exact N.
Qed.

(* the value the compiler leaves in a3 for RATES[data[0] % 5] is 8 * (data[0] mod 5): the division by 5 by
   multiplication (0xcd, shift 10) of 0x12be8-0x12c10, checked on every byte *)
Ltac idx_rw b :=
  lazymatch goal with
  | |- context [bv_ltu (Z_to_bv 64 18446744073709485167) ?X] =>
      let EX := fresh "EX" in
      assert (EX : X = Z_to_bv 64 (8 * (bv_unsigned b mod 5)));
      [ unfold zxb; pose proof (byte_range b) as RB; revert RB; generalize (bv_unsigned b); intros c Hc;
        apply bv_eq; apply Z.eqb_eq; revert c Hc; apply brute256_ok; vm_compute; reflexivity
      | rewrite EX; clear EX ]
  end.

(* the name length: k = data[1] mod 16 *)
Lemma k_mach : forall b : byte, Z.land (bv_unsigned (zxb b)) 15 = bv_unsigned b mod 16.
Proof.
  intros b. unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by (pose proof (byte_range b); lia).
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* the byte class the compiler tests at 0x12c7c-0x12c88: c > 32 is good, else bit c of 0x100002601
   (NUL, tab, LF, CR, space) *)
Definition bad_mach (c : Z) : bool :=
  if bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 c) then false
  else negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64
          (Z.shiftr 4294977025 (bv_unsigned (Z_to_bv 64 c) mod 64)))) 1)) (Z_to_bv 64 0)).

Lemma bad_mach_ok : forall c, 0 <= c < 256 -> bad_mach c = ((c =? 0) || (c =? 10) || is_sep c).
Proof.
  intros c Hc.
  pose proof (brute256_ok (fun c => Bool.eqb (bad_mach c) ((c =? 0) || (c =? 10) || is_sep c))
                ltac:(vm_compute; reflexivity) c Hc) as H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma bad_hi : forall b : byte, bv_ltu (Z_to_bv 64 32) (zxb b) = true -> lock_bad b = false.
Proof.
  intros b H. unfold lock_bad. rewrite <- (bad_mach_ok (bz b) (byte_range b)).
  unfold bad_mach, bz. unfold zxb in H. rewrite H. reflexivity.
Qed.

Lemma bad_lo : forall b : byte, bv_ltu (Z_to_bv 64 32) (zxb b) = false ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64
          (Z.shiftr 4294977025 (bv_unsigned (zxb b) mod 64)))) 1)) (Z_to_bv 64 0)) = lock_bad b.
Proof.
  intros b H. unfold lock_bad. rewrite <- (bad_mach_ok (bz b) (byte_range b)).
  unfold bad_mach, bz. unfold zxb in H |- *. rewrite H. reflexivity.
Qed.

(* a byte that is not lock_bad is not NUL *)
Lemma bad_nz : forall b : byte, lock_bad b = false -> b <> Z_to_bv 8 0.
Proof.
  intros b H E. subst b. unfold lock_bad, bz in H. vm_compute in H. discriminate H.
Qed.

Lemma notin_zero : forall l : list byte, existsb lock_bad l = false -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin.
  assert (E : existsb lock_bad l = true) by (apply existsb_exists; exists (Z_to_bv 8 0); split; [exact Hin|];
    unfold lock_bad, bz; vm_compute; reflexivity).
  rewrite E in H. discriminate H.
Qed.

Lemma existsb_nth : forall (l : list byte) i b, nth_error l i = Some b -> lock_bad b = true ->
  existsb lock_bad l = true.
Proof.
  intros l i b N Hb. apply existsb_exists. exists b. split; [|exact Hb].
  eapply nth_error_In. exact N.
Qed.

Lemma firstn_S_nth : forall (l : list byte) i b, nth_error l i = Some b ->
  firstn (S i) l = firstn i l ++ [b].
Proof.
  intros l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - rewrite (IH i b N). reflexivity.
Qed.


Lemma rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma rw_wr : forall m A cs, rw_cells rsegs m A cs -> wr_at rsegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ H]. exact H. Qed.

Lemma wr_at_le : forall m A n n', wr_at rsegs m A n -> 0 <= n' <= n -> wr_at rsegs m A n'.
Proof. intros m A n n' (Ha & Hn & H) Hle. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

(* the size test of 0x12bd4-0x12be0: size - 2 ^ 26 <u 2 - 2 ^ 26 holds exactly for size < 2 or 2 ^ 26 <= size *)
Lemma size_early : forall z, 0 <= z < 2 ^ 64 -> (z < 2 \/ 2 ^ 26 <= z) ->
  bv_ltu (Z_to_bv 64 (z + -67108864)) (Z_to_bv 64 (-67108862)) = true.
Proof.
  intros z Hz Hc. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  assert (E2 : (-67108862) mod 2 ^ 64 = 2 ^ 64 - 67108862)
    by (rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia).
  rewrite E2. destruct Hc as [Hc|Hc].
  - assert (E1 : (z + -67108864) mod 2 ^ 64 = z + -67108864 + 2 ^ 64)
      by (rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia).
    rewrite E1. apply Z.ltb_lt. lia.
  - assert (E1 : (z + -67108864) mod 2 ^ 64 = z + -67108864) by (apply Z.mod_small; lia).
    rewrite E1. apply Z.ltb_lt. lia.
Qed.

Lemma size_ok : forall z, 2 <= z < 2 ^ 26 ->
  bv_ltu (Z_to_bv 64 (z + -67108864)) (Z_to_bv 64 (-67108862)) = false.
Proof.
  intros z Hz. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  assert (E2 : (-67108862) mod 2 ^ 64 = 2 ^ 64 - 67108862)
    by (rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia).
  assert (E1 : (z + -67108864) mod 2 ^ 64 = z + -67108864 + 2 ^ 64)
    by (rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia).
  rewrite E1, E2. apply Z.ltb_ge. lia.
Qed.


Lemma rw_cells_tl : forall m A c cs, rw_cells rsegs m A (c :: cs) ->
  rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[Hc Hwf] Hb] (W0 & W1 & Hw)].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb as [_ Hb]. rewrite cbytes_length in Hb by exact Hc.
  split; [split; [exact Hwf | exact Hb]|]. cbn [cells_size] in W1, Hw.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

(* the port bytes: the k bytes of the name *)
Definition lt_port (pl : list byte) (k : nat) : list byte := firstn k (skipn 2 pl).

Lemma lt_port_length : forall pl k, (2 + k <= length pl)%nat -> length (lt_port pl k) = k.
Proof. intros pl k H. unfold lt_port. rewrite firstn_length, skipn_length. lia. Qed.

Lemma lt_port_nth : forall pl k i b, (i < k)%nat -> nth_error (lt_port pl k) i = Some b ->
  nth_error pl (2 + i) = Some b.
Proof.
  intros pl k i b Hi N. unfold lt_port in N. rewrite nth_error_firstn, nth_error_skipn in N.
  destruct (Nat.ltb_spec i k) as [_|H]; [exact N | lia].
Qed.

Lemma lt_port_nth' : forall pl k i, (i < k)%nat -> (2 + k <= length pl)%nat ->
  exists b, nth_error (lt_port pl k) i = Some b.
Proof.
  intros pl k i Hi Hk. destruct (nth_error (lt_port pl k) i) as [b|] eqn:N; [exists b; reflexivity|].
  apply nth_error_None in N. rewrite lt_port_length in N by exact Hk. lia.
Qed.

Section E.
Variables (ra sp gp tp s0e s1e s2e s3e s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p n lo : Z) (pl : list byte).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : lo + 64 <= bv_unsigned sp.
Hypothesis SP63 : bv_unsigned sp < 2 ^ 63.
Hypothesis MI : mem_inv rsegs m.
Hypothesis HL : Z.of_nat (length pl) = n.

Local Notation SPv := (bv_unsigned sp).
Local Notation kk := (bv_unsigned (nth 1 pl (Z_to_bv 8 0)) mod 16).
Local Notation Pb := (lt_port pl (Z.to_nat kk)).

(* the state after the epilogue: a0 = r, every callee-saved register restored, sp back at its entry value *)
Definition lt_ret_post (r : Z) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 : word) (m' : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2e s3e s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(SPv - 64, SPv)] m m' /\ wmono rsegs m m'.

(* the state at check_no_overread's entry, 0x12d2c: ra = 0x12cec, the port holds the name and its NUL *)
Definition lt_call_post : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 : word) (m' : word -> option byte) (SL : list byte) (rate : Z),
    ms = MS (mkR (Z_to_bv 64 0x12cec) (Z_to_bv 64 (SPv - 64)) gp tp t0 t1 t2
                 (Z_to_bv 64 kk) (Z_to_bv 64 rate)
                 (Z_to_bv 64 (p + 2 + kk)) (Z_to_bv 64 (n - 2 - kk)) (Z_to_bv 64 (SPv - 56)) (Z_to_bv 64 rate)
                 a4 a5 a6 a7
                 (Z_to_bv 64 (p + 2 + kk)) (Z_to_bv 64 (n - 2 - kk)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x12d2c) fc None m' (seg_rom rsegs) /\
    0 <= rate < 2 ^ 64 /\ 1 <= kk <= 15 /\ 2 + kk <= n /\ lock_ret pl = 0 /\
    length (Pb ++ Z_to_bv 8 0 :: SL) = 16%nat /\
    bytes_at rsegs m' (SPv - 56) (Pb ++ Z_to_bv 8 0 :: SL) /\
    existsb lock_bad Pb = false /\
    bytes_at rsegs m' p pl /\
    rw_cells rsegs m' (SPv - 40) [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] /\
    munch [(SPv - 64, SPv)] m m' /\ wmono rsegs m m'.

(* the epilogue, 0x12d0c-0x12d24: restore ra, s0, s1, s2, s3 and return *)
Lemma lt_epi : forall (r : Z) (m' : word -> option byte)
    (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0' s1' s2' s3' u3 u4 u5 u6 : word),
  rw_cells rsegs m' (SPv - 40) [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
  munch [(SPv - 64, SPv)] m m' -> wmono rsegs m m' ->
  evt rsegs (lt_ret_post r)
    (MS (mkR ra' (Z_to_bv 64 (SPv - 64)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x12d0c) fc None m' (seg_rom rsegs)).
Proof.
  intros r m' ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0' s1' s2' s3' u3 u4 u5 u6 FRM MU WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  replace (SPv - 40) with (SPv - 64 + 24) in FRM by lia.
  do 7 step.
  apply evt_done. unfold lt_ret_post. do 15 eexists.
  split; [|split; [exact MU | exact WM]].
  f_equal. unfold mkR. repeat (match goal with |- TNode _ _ _ = TNode _ _ _ => f_equal
                               | |- Some _ = Some _ => f_equal end).
  all: lt_w.
Qed.

Definition lt_post (ms : machine_state) : Prop := lt_ret_post (lock_ret pl) ms \/ lt_call_post ms.

(* the name's bytes are in the payload: 2 + k <= size *)
Lemma lt_Pb_length : 2 + kk <= n -> length Pb = Z.to_nat kk.
Proof. intros KN. apply lt_port_length. lia. Qed.

(* i bytes of the name are in the frame, none of them NUL, LF or a separator, and the rest of the frame is as
   the prologue left it *)
Definition lt_inv (i : nat) (mi : word -> option byte) (W : list byte) : Prop :=
  bytes_at rsegs mi (SPv - 56) (firstn i Pb ++ W) /\
  length (firstn i Pb ++ W) = 16%nat /\
  wr_at rsegs mi (SPv - 56) 16 /\
  bytes_at rsegs mi p pl /\
  rw_cells rsegs mi (SPv - 40) [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] /\
  munch [(SPv - 64, SPv)] m mi /\ wmono rsegs m mi /\
  existsb lock_bad (firstn i Pb) = false.

(* the head of the loop of fuzz_lock.c:194-199, 0x12c74 *)
Definition lt_loop_state (mi : word -> option byte) (t0 t1 t2 : word) (rate ptr dst rem : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (SPv - 64)) gp tp t0 t1 t2 (Z_to_bv 64 kk) (Z_to_bv 64 rate)
          (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 ptr) (Z_to_bv 64 dst)
          (Z_to_bv 64 32) (Z_to_bv 64 ptr) (Z_to_bv 64 4294977025) (Z_to_bv 64 rem)
          s2e s3e s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x12c74) fc None mi (seg_rom rsegs).

(* the store of the name byte in the frame, 0x12c8c *)
Definition lt_store_state (mi : word -> option byte) (c : byte) (t1 t2 : word) (rate ptr dst rem : Z)
    : machine_state :=
  MS (mkR ra (Z_to_bv 64 (SPv - 64)) gp tp (zxb c) t1 t2 (Z_to_bv 64 kk) (Z_to_bv 64 rate)
          (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 ptr) (Z_to_bv 64 dst)
          (Z_to_bv 64 32) (Z_to_bv 64 ptr) (Z_to_bv 64 4294977025) (Z_to_bv 64 rem)
          s2e s3e s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x12c8c) fc None mi (seg_rom rsegs).

(* 0x12c8c-0x12ca0: the byte goes into the frame; then either the loop runs again or the name is read and
   0x12ca4-0x12ce8 writes its NUL and calls check_no_overread *)
Lemma lt_store : forall (i : nat) (mi : word -> option byte) (W : list byte) (c : byte) (t1 t2 : word)
    (rate ptr dst rem : Z),
  2 <= n < 2 ^ 26 -> 1 <= kk <= 15 -> 2 + kk <= n -> 4096 <= p < 2 ^ 63 -> p + n <= lo ->
  0 <= rate < 2 ^ 64 -> (i < Z.to_nat kk)%nat ->
  ptr = p + 2 + Z.of_nat i -> dst = SPv - 56 + Z.of_nat i -> rem = kk - Z.of_nat i ->
  lt_inv i mi W -> nth_error Pb i = Some c -> lock_bad c = false ->
  (forall (mi2 : word -> option byte) (W2 : list byte) (ptr2 dst2 rem2 : Z),
     (S i < Z.to_nat kk)%nat -> lt_inv (S i) mi2 W2 ->
     ptr2 = p + 2 + Z.of_nat (S i) -> dst2 = SPv - 56 + Z.of_nat (S i) -> rem2 = kk - Z.of_nat (S i) ->
     evt rsegs lt_post (lt_loop_state mi2 (zxb c) t1 t2 rate ptr2 dst2 rem2)) ->
  evt rsegs lt_post (lt_store_state mi c t1 t2 rate ptr dst rem).
Proof.
  intros i mi W c t1 t2 rate ptr dst rem HN KR KN HP HPL Hr Hi -> -> ->
    (BP & LW & WR & BLi & FRM & MU & WM & EXb) Nc Hgood KONT.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (lt_Pb_length KN) as PL.
  assert (HiZ : 0 <= Z.of_nat i < kk) by lia.
  assert (LF : length (firstn i Pb) = i) by (rewrite length_firstn; lia).
  destruct W as [|w0 W']; [rewrite length_app, LF in LW; cbn in LW; lia|].
  assert (LW' : length W' = (15 - i)%nat) by (rewrite length_app, LF in LW; cbn in LW; lia).
  assert (HS : store_ok rsegs mi (wa (SPv - 56 + Z.of_nat i)) 1 = true)
    by (apply (wr_at_store_ok rsegs mi (SPv - 56) 16 (Z.of_nat i) 1 WR); lia).
  unfold lt_store_state.
  step. rewrite (Mem.le1_zxb c).
  assert (BP' : bytes_at rsegs (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]) (SPv - 56)
                  (firstn (S i) Pb ++ W')).
  { replace (firstn i Pb ++ w0 :: W') with (firstn i Pb ++ [w0] ++ W') in BP by reflexivity.
    pose proof (bytes_at_write_inside rsegs mi (SPv - 56) (firstn i Pb ++ [w0] ++ W') (Z.of_nat i) [c] BP
                  ltac:(lia) ltac:(rewrite !length_app, LF; cbn; lia)) as HB.
    rewrite Nat2Z.id in HB.
    replace (upd_bytes (firstn i Pb ++ [w0] ++ W') i [c]) with (firstn i Pb ++ [c] ++ W') in HB
      by (rewrite <- (upd_bytes_mid (firstn i Pb) [w0] W' [c] eq_refl), LF; reflexivity).
    rewrite (firstn_S_nth Pb i c Nc), <- app_assoc. exact HB. }
  assert (LW2 : length (firstn (S i) Pb ++ W') = 16%nat) by (rewrite length_app, length_firstn; lia).
  assert (WR2 : wr_at rsegs (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]) (SPv - 56) 16)
    by (apply wr_at_write; exact WR).
  assert (BL2 : bytes_at rsegs (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]) p pl)
    by (apply (bytes_at_write_other rsegs mi (SPv - 56 + Z.of_nat i) [c] p pl BLi); cbn [length]; lia).
  assert (FR2 : rw_cells rsegs (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]) (SPv - 40)
                  [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra])
    by (apply (rw_cells_frame rsegs mi (SPv - 40) _ (SPv - 56 + Z.of_nat i) [c] FRM);
        cbn [length cells_size csize]; lia).
  assert (MU2 : munch [(SPv - 64, SPv)] m (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]))
    by (apply (munch_write _ m mi (SPv - 56 + Z.of_nat i) [c] MU); cbn [length inside]; lia).
  assert (WM2 : wmono rsegs m (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]))
    by (apply wmono_write; exact WM).
  assert (EX2 : existsb lock_bad (firstn (S i) Pb) = false)
    by (rewrite (firstn_S_nth Pb i c Nc), existsb_app, EXb; cbn [existsb orb]; rewrite Hgood; reflexivity).
  clear BP LW WR BLi FRM MU WM EXb HS.
  do 4 step. step.
  destruct (Nat.eq_dec (S i) (Z.to_nat kk)) as [EQ|NE].
  - br false.
    (* the name is read *)
    assert (FA : firstn (S i) Pb = Pb) by (apply firstn_all2; lia).
    rewrite FA in BP', EX2, LW2.
    rewrite length_app in LW2.
    assert (LPb : Z.of_nat (length Pb) = kk) by lia.
    destruct W' as [|w1 W'']; [cbn in LW2; lia|].
    assert (LW'' : length W'' = Z.to_nat (15 - kk)) by (cbn in LW2; lia).
    assert (HS2 : store_ok rsegs (write_to_mem mi (Z_to_bv 64 (SPv - 56 + Z.of_nat i)) [c])
                    (wa (SPv - 56 + kk)) 1 = true)
      by (apply (wr_at_store_ok rsegs _ (SPv - 56) 16 kk 1 WR2); lia).
    step. replace (bv_unsigned sp - 64 + 8) with (bv_unsigned sp - 56) by lia.
    do 2 step. trapbr (SPv - 56). do 3 step.
    replace (Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 (Z_to_bv 64 0)))) with [Z_to_bv 8 0] by reflexivity.
    set (m3 := write_to_mem (write_to_mem mi (wa (SPv - 56 + Z.of_nat i)) [c]) (wa (SPv - 56 + kk))
                 [Z_to_bv 8 0]).
    assert (BP3 : bytes_at rsegs m3 (SPv - 56) (Pb ++ Z_to_bv 8 0 :: W'')).
    { unfold m3.
      pose proof (bytes_at_write_inside rsegs _ (SPv - 56) (Pb ++ [w1] ++ W'') kk [Z_to_bv 8 0] BP'
                    ltac:(lia) ltac:(rewrite !length_app; cbn [length]; lia)) as HB.
      replace (upd_bytes (Pb ++ [w1] ++ W'') (Z.to_nat kk) [Z_to_bv 8 0]) with (Pb ++ [Z_to_bv 8 0] ++ W'') in HB
        by (rewrite <- (upd_bytes_mid Pb [w1] W'' [Z_to_bv 8 0] eq_refl), PL; reflexivity).
      exact HB. }
    assert (BL3 : bytes_at rsegs m3 p pl)
      by (unfold m3; apply (bytes_at_write_other rsegs _ (SPv - 56 + kk) [Z_to_bv 8 0] p pl BL2);
          cbn [length]; lia).
    assert (FR3 : rw_cells rsegs m3 (SPv - 40) [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra])
      by (unfold m3; apply (rw_cells_frame rsegs _ (SPv - 40) _ (SPv - 56 + kk) [Z_to_bv 8 0] FR2);
          cbn [length cells_size csize]; lia).
    assert (MU3 : munch [(SPv - 64, SPv)] m m3)
      by (unfold m3; apply (munch_write _ m _ (SPv - 56 + kk) [Z_to_bv 8 0] MU2); cbn [length inside]; lia).
    assert (WM3 : wmono rsegs m m3) by (unfold m3; apply wmono_write; exact WM2).
    assert (RET0 : lock_ret pl = 0).
    { unfold lock_ret, bz. cbv zeta. rewrite HL.
      rewrite (proj2 (Z.ltb_ge n 2) ltac:(lia)), (proj2 (Z.leb_gt (2 ^ 26) n) ltac:(lia)); cbn [orb].
      rewrite (proj2 (Z.ltb_ge n (2 + kk)) ltac:(lia)), (proj2 (Z.eqb_neq kk 0) ltac:(lia)).
      unfold lt_port in EX2. rewrite EX2. reflexivity. }
    step. br false. do 3 step. trapbr (p + 2). do 8 step.
    apply evt_done. unfold lt_post. right. unfold lt_call_post.
    do 7 eexists. exists m3, W'', rate.
    split.
    + f_equal. unfold mkR. repeat (match goal with |- TNode _ _ _ = TNode _ _ _ => f_equal
                                   | |- Some _ = Some _ => f_equal end).
      all: lt_w.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [exact RET0|].
      split; [rewrite length_app; cbn [length]; lia|].
      split; [exact BP3|]. split; [exact EX2|]. split; [exact BL3|]. split; [exact FR3|].
      split; [exact MU3 | exact WM3].
  - br true.
    apply (KONT _ W' _ _ _ ltac:(lia)); [| lia | lia | lia].
    split; [exact BP'|]. split; [exact LW2|]. split; [exact WR2|]. split; [exact BL2|].
    split; [exact FR2|]. split; [exact MU2|]. split; [exact WM2 | exact EX2].
Qed.

(* the loop of fuzz_lock.c:194-199 at 0x12c74: S K iterations are left *)
Lemma lt_loop : forall (K i : nat) (mi : word -> option byte) (W : list byte) (t0 t1 t2 : word)
    (rate ptr dst rem : Z),
  2 <= n < 2 ^ 26 -> 1 <= kk <= 15 -> 2 + kk <= n -> 4096 <= p < 2 ^ 63 -> p + n <= lo ->
  0 <= rate < 2 ^ 64 -> (i + S K)%nat = Z.to_nat kk -> lt_inv i mi W ->
  ptr = p + 2 + Z.of_nat i -> dst = SPv - 56 + Z.of_nat i -> rem = kk - Z.of_nat i ->
  evt rsegs lt_post (lt_loop_state mi t0 t1 t2 rate ptr dst rem).
Proof.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  induction K as [|K IH]; intros i mi W t0 t1 t2 rate ptr dst rem HN KR KN HP HPL Hr HK INV -> -> ->.
  all: pose proof (lt_Pb_length KN) as PL.
  all: pose proof INV as (BP & LW & WR & BLi & FRM & MU & WM & EXb).
  all: assert (Hi : (i < Z.to_nat kk)%nat) by lia.
  all: assert (HiZ : 0 <= Z.of_nat i < kk) by lia.
  all: destruct (lt_port_nth' pl (Z.to_nat kk) i Hi ltac:(lia)) as [c Nc].
  all: pose proof (rdb mi p pl (2 + i) c BLi (lt_port_nth pl (Z.to_nat kk) i c Hi Nc)) as R.
  all: replace (p + Z.of_nat (2 + i)) with (p + 2 + Z.of_nat i) in R by lia.
  all: unfold lt_loop_state.
  (* 0x12c74 beqz a5: the name's pointer is not null *)
  all: step; br false.
  (* 0x12c78 lbu t0, 0(a2); 0x12c7c bltu a4, t0 *)
  all: step; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (zxb c)) eqn:C1; cbv iota.
  (* a byte above 32 is no separator: store it *)
  1,3: (apply (lt_store i mi W c t1 t2 rate _ _ _ HN KR KN HP HPL Hr Hi eq_refl eq_refl eq_refl INV Nc
          (bad_hi c C1));
        intros mi2 W2 ptr2 dst2 rem2 Hlt INV2 Ep Ed Er;
        first [ exfalso; lia
              | exact (IH (S i) mi2 W2 (zxb c) t1 t2 rate ptr2 dst2 rem2 HN KR KN HP HPL Hr ltac:(lia) INV2
                         Ep Ed Er) ]).
  all: do 2 step; step.
  all: destruct (negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64
         (Z.shiftr 4294977025 (bv_unsigned (zxb c) mod 64)))) 1)) (Z_to_bv 64 0))) eqn:C2; cbv iota.
  all: rewrite (bad_lo c C1) in C2.
  all: lazymatch type of C2 with
  | lock_bad _ = true =>
      (* the byte is NUL, LF or a separator: 0x12d08 addi a0, zero, -1, then the epilogue *)
      assert (RET : lock_ret pl = -1) by
        (unfold lock_ret, bz; cbv zeta; rewrite HL;
         rewrite (proj2 (Z.ltb_ge n 2) ltac:(lia)), (proj2 (Z.leb_gt (2 ^ 26) n) ltac:(lia)); cbn [orb];
         rewrite (proj2 (Z.ltb_ge n (2 + kk)) ltac:(lia)), (proj2 (Z.eqb_neq kk 0) ltac:(lia));
         unfold lt_port in Nc;
         rewrite (existsb_nth (firstn (Z.to_nat kk) (skipn 2 pl)) i c Nc C2); reflexivity);
      step; apply (evt_mono rsegs (lt_ret_post (lock_ret pl)));
      [ rewrite RET; apply (lt_epi (-1) mi ra (zxb c)); [exact FRM | exact MU | exact WM]
      | intros ms' Hms'; unfold lt_post; left; exact Hms' ]
  | lock_bad _ = false =>
      (* a byte the mask does not catch: store it *)
      apply (lt_store i mi W c _ _ rate _ _ _ HN KR KN HP HPL Hr Hi eq_refl eq_refl eq_refl INV Nc C2);
      intros mi2 W2 ptr2 dst2 rem2 Hlt INV2 Ep Ed Er;
      first [ exfalso; lia
            | exact (IH (S i) mi2 W2 (zxb c) _ _ rate ptr2 dst2 rem2 HN KR KN HP HPL Hr ltac:(lia) INV2
                       Ep Ed Er) ]
  end.
Qed.


(* 0x12bbc-0x12c70: the prologue, the size test, the rate from RATES and the name's length, then the loop; or a
   return of 0 (the size is out of range, or it does not hold the name) or of -1 (the name is empty) *)
Lemma lt_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 : word),
  2 <= n < 2 ^ 26 -> 4096 <= p < 2 ^ 63 -> p + n <= lo -> bytes_at rsegs m p pl ->
  evt rsegs lt_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2e s3e s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12bbc) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 HNR HP HPL BL.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound rsegs m p pl BL) as BB.
  pose proof (munch_refl [(SPv - 64, SPv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HN0 : 0 <= n < 2 ^ 64) by lia.
  carve_frame 64%nat ST.
  do 10 step.
  (* the frame: 8 unused bytes, the 16 of port[16], the five saved registers *)
  match goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -64) (CB 24 ?j :: ?rest) |- _ =>
    pose proof (rw_cells_split_CB rsegs mm (bv_unsigned sp + -64) [] 24 j rest [8%nat; 16%nat] H eq_refl) as FR1
  end.
  cbn [app mk_CB_cells firstn skipn] in FR1.
  pose proof (cells_at_wf rsegs _ _ _ (proj1 FR1)) as HWF. cbn [cells_wf cell_wf] in HWF.
  destruct HWF as (HWF8 & HWF16 & HWFr).
  match type of FR1 with rw_cells _ ?mm _ (CB 8 ?j8 :: CB 16 ?W :: ?rest) =>
    pose proof (rw_cells_tl mm (bv_unsigned sp + -64) (CB 8 j8) (CB 16 W :: rest) FR1) as FR2
  end.
  cbn [csize] in FR2. replace (bv_unsigned sp + -64 + Z.of_nat 8) with (SPv - 56) in FR2 by lia.
  match type of FR2 with rw_cells _ ?mm _ (CB 16 ?W :: ?rest) =>
    pose proof (rw_cells_tl mm (SPv - 56) (CB 16 W) rest FR2) as FR3;
    pose proof (rw_bytes mm (SPv - 56) (CB 16 W :: rest) FR2) as BWa;
    pose proof (rw_wr mm (SPv - 56) (CB 16 W :: rest) FR2) as WRa
  end.
  cbn [csize] in FR3. replace (SPv - 56 + Z.of_nat 16) with (SPv - 40) in FR3 by lia.
  cbn [cells_bytes cbytes cells_size csize] in BWa, WRa.
  apply bytes_at_app in BWa. destruct BWa as [BWa _].
  pose proof (wr_at_le _ (SPv - 56) _ 16 WRa ltac:(lia)) as WRb.
  (* a return of 0 through 0x12c34, and a return of -1 through 0x12d08 *)
  assert (EARLY : forall (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 : word)
      (mm : word -> option byte) (pc : Z),
      (pc = 0x12c34 /\ lock_ret pl = 0) \/ (pc = 0x12d08 /\ lock_ret pl = -1) ->
      rw_cells rsegs mm (SPv - 40) [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
      munch [(SPv - 64, SPv)] m mm -> wmono rsegs m mm ->
      evt rsegs lt_post
        (MS (mkR ra (Z_to_bv 64 (SPv - 64)) gp tp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
                 r13 r14 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs))).
  { intros r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 mm pc Hpc FRM MUm WMm.
    destruct Hpc as [[-> R0]|[-> R0]].
    - do 2 step. apply (evt_mono rsegs (lt_ret_post 0));
        [ apply (lt_epi 0 mm ra); assumption
        | intros ms' Hms'; unfold lt_post; left; rewrite R0; exact Hms' ].
    - step. apply (evt_mono rsegs (lt_ret_post (-1)));
        [ apply (lt_epi (-1) mm ra); assumption
        | intros ms' Hms'; unfold lt_post; left; rewrite R0; exact Hms' ]. }
  (* 0x12be0 bltu: the size is in range *)
  if_false_by (size_ok n ltac:(lia)).
  (* the first two bytes of the payload *)
  destruct (nth_error pl 0) as [b0|] eqn:N0; [|apply nth_error_None in N0; lia].
  destruct (nth_error pl 1) as [b1|] eqn:N1; [|apply nth_error_None in N1; lia].
  assert (Eb1 : nth 1 pl (Z_to_bv 8 0) = b1) by (apply nth_error_nth; exact N1).
  match goal with H : bytes_at rsegs ?mm p pl |- _ =>
    pose proof (rdb mm p pl 0 b0 H N0) as R0; pose proof (rdb mm p pl 1 b1 H N1) as R1 end.
  cbn [Z.of_nat] in R0, R1. rewrite Z.add_0_r in R0.
  pose proof (byte_range b0) as RB0. pose proof (byte_range b1) as RB1.
  (* 0x12be4 beqz a0: the payload is not the null pointer *)
  step. br false.
  (* 0x12be8-0x12c18: the address of RATES[data[0] % 5] does not wrap *)
  do 13 step. idx_rw b0. br false.
  (* 0x12c1c-0x12c20 beq a0, -1: the payload is not the last byte of the address space *)
  step. step. br false.
  (* 0x12c24-0x12c30: k = data[1] % 16; a size that does not hold the name returns 0 *)
  do 3 step. rewrite k_mach, <- Eb1. step.
  destruct (Z_lt_le_dec n (2 + kk)) as [HK2|HK2].
  { br false. apply (EARLY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x12c34);
      [ left; split; [reflexivity|];
        unfold lock_ret, bz; cbv zeta; rewrite HL;
        rewrite (proj2 (Z.ltb_ge n 2) ltac:(lia)), (proj2 (Z.leb_gt (2 ^ 26) n) ltac:(lia)); cbn [orb];
        rewrite (proj2 (Z.ltb_lt n (2 + kk)) ltac:(lia)); reflexivity
      | exact FR3 | assumption | assumption ]. }
  br true.
  (* 0x12c3c beqz s0: an empty name returns -1 *)
  step.
  destruct (Z.eq_dec kk 0) as [HK0|HK0].
  { br true. apply (EARLY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x12d08);
      [ right; split; [reflexivity|];
        unfold lock_ret, bz; cbv zeta; rewrite HL;
        rewrite (proj2 (Z.ltb_ge n 2) ltac:(lia)), (proj2 (Z.leb_gt (2 ^ 26) n) ltac:(lia)); cbn [orb];
        rewrite (proj2 (Z.ltb_ge n (2 + kk)) ltac:(lia)), (proj2 (Z.eqb_eq kk 0) ltac:(lia)); reflexivity
      | exact FR3 | assumption | assumption ]. }
  br false.
  (* 0x12c40-0x12c58: the rate of RATES[data[0] % 5] *)
  do 6 step.
  assert (HI5 : bv_unsigned b0 mod 5 = 0 \/ bv_unsigned b0 mod 5 = 1 \/ bv_unsigned b0 mod 5 = 2 \/
                bv_unsigned b0 mod 5 = 3 \/ bv_unsigned b0 mod 5 = 4) by lia.
  destruct HI5 as [E5|[E5|[E5|[E5|E5]]]]; rewrite E5.
  all: step.
  (* 0x12c5c-0x12c70: the name's pointer and the mask of the bytes the name refuses *)
  all: match goal with |- context [v_sltiu (Z_to_bv 64 p) (-2)] =>
         replace (v_sltiu (Z_to_bv 64 p) (-2)) with (Z_to_bv 64 1) by
           (unfold v_sltiu; rewrite (unsigned_lit p) by lia;
            replace (bv_wrap 64 (-2)) with 18446744073709551614 by reflexivity;
            destruct (p <? 18446744073709551614) eqn:EL; [reflexivity | apply Z.ltb_ge in EL; lia]) end.
  all: do 6 step.
  all: rewrite (unsigned_lit (p + 2)) by lia; rewrite (land_ones64 (p + 2)) by lia.
  all: replace (bv_unsigned sp - 64 + 8) with (bv_unsigned sp - 56) by lia.
  (* the loop of fuzz_lock.c:194-199 *)
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (lt_loop (Z.to_nat kk - 1) 0%nat mm) end.
  all: try exact HP. all: try exact HPL.
  all: try lia.
  all: unfold lt_inv.
  all: split; [exact BWa|].
  all: split; [rewrite length_app; change (length (firstn 0 Pb)) with 0%nat; lia|].
  all: split; [exact WRb|]; split; [assumption|].
  all: split; [exact FR3|]; split; [assumption|]; split; [assumption | reflexivity].
Qed.


(* the state at check_lookup's entry, 0x12e34: ra = 0x12d04, the same memory as at check_no_overread's return *)
Definition lt_call2_post (mm : word -> option byte) (rate : Z) (u3 u4 u5 u6 : word)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a5 a6 a7 : word),
    ms = MS (mkR (Z_to_bv 64 0x12d04) (Z_to_bv 64 (SPv - 64)) gp tp t0 t1 t2 (Z_to_bv 64 kk) (Z_to_bv 64 rate)
                 (Z_to_bv 64 (p + 2 + kk)) (Z_to_bv 64 (n - 2 - kk)) (Z_to_bv 64 (SPv - 56)) (Z_to_bv 64 kk)
                 (Z_to_bv 64 rate) a5 a6 a7
                 (Z_to_bv 64 (p + 2 + kk)) (Z_to_bv 64 (n - 2 - kk)) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x12e34) fc None mm (seg_rom rsegs).

(* 0x12cec-0x12d00: the call of check_lookup, with the name's length and the rate *)
Lemma lt_mid : forall (mm : word -> option byte) (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 : word)
    (rate : Z),
  evt rsegs (lt_call2_post mm rate u3 u4 u5 u6)
    (MS (mkR ra' (Z_to_bv 64 (SPv - 64)) gp tp t0 t1 t2 (Z_to_bv 64 kk) (Z_to_bv 64 rate)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + 2 + kk)) (Z_to_bv 64 (n - 2 - kk))
             s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x12cec) fc None mm (seg_rom rsegs)).
Proof.
  intros mm ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 rate.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 step.
  apply evt_done. unfold lt_call2_post. do 6 eexists.
  f_equal. unfold mkR. repeat (match goal with |- TNode _ _ _ = TNode _ _ _ => f_equal
                               | |- Some _ = Some _ => f_equal end).
  all: lt_w.
Qed.

(* 0x12d04: check_lookup returned, so the harness returns 0 through 0x12c34 and the epilogue *)
Lemma lt_exit : forall (mm : word -> option byte)
    (ra' r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 u3 u4 u5 u6 : word),
  lock_ret pl = 0 ->
  rw_cells rsegs mm (SPv - 40) [C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
  munch [(SPv - 64, SPv)] m mm -> wmono rsegs m mm ->
  evt rsegs (lt_ret_post 0)
    (MS (mkR ra' (Z_to_bv 64 (SPv - 64)) gp tp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
             r13 r14 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x12d04) fc None mm (seg_rom rsegs)).
Proof.
  intros mm ra' r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 u3 u4 u5 u6 R0 FRM MUm WMm.
  do 3 step. apply (lt_epi 0 mm ra'); assumption.
Qed.


(* 0x12bbc-0x12be0 then 0x12c34: a size below 2 or of 2 ^ 26 and more returns 0 *)
Lemma lock_ret_early : (n < 2 \/ 2 ^ 26 <= n) -> lock_ret pl = 0.
Proof.
  intros HC. unfold lock_ret, bz. cbv zeta. rewrite HL. destruct HC as [HC'|HC'].
  - rewrite (proj2 (Z.ltb_lt n 2) ltac:(lia)). reflexivity.
  - rewrite (proj2 (Z.leb_le (2 ^ 26) n) ltac:(lia)), Bool.orb_true_r. reflexivity.
Qed.

Lemma lt_early : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 : word),
  0 <= n < 2 ^ 64 -> (n < 2 \/ 2 ^ 26 <= n) ->
  evt rsegs (lt_ret_post 0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2e s3e s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12bbc) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 HN0 HC.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(SPv - 64, SPv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  do 10 step.
  match goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -64) (CB 24 ?j :: ?rest) |- _ =>
    pose proof (rw_cells_split_CB rsegs mm (bv_unsigned sp + -64) [] 24 j rest [8%nat; 16%nat] H eq_refl) as FR1
  end.
  cbn [app mk_CB_cells firstn skipn] in FR1.
  match type of FR1 with rw_cells _ ?mm _ (CB 8 ?j8 :: CB 16 ?W :: ?rest) =>
    pose proof (rw_cells_tl mm (bv_unsigned sp + -64) (CB 8 j8) (CB 16 W :: rest) FR1) as FR2
  end.
  cbn [csize] in FR2. replace (bv_unsigned sp + -64 + Z.of_nat 8) with (SPv - 56) in FR2 by lia.
  match type of FR2 with rw_cells _ ?mm _ (CB 16 ?W :: ?rest) =>
    pose proof (rw_cells_tl mm (SPv - 56) (CB 16 W) rest FR2) as FR3
  end.
  cbn [csize] in FR3. replace (SPv - 56 + Z.of_nat 16) with (SPv - 40) in FR3 by lia.
  if_true_by (size_early n ltac:(lia) HC).
  do 2 step.
  apply (lt_epi 0 _ ra); assumption.
Qed.

End E.
