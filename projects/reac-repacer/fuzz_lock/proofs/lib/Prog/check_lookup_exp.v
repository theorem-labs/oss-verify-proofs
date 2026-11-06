(* Walk of the harness's own reading of the lock in check_lookup (fuzz_lock.c:146-147: [expected] of
   fuzz_lock.c:78-118, inlined) in fuzz_lock.plain: from 0x12e28, where rp_lock_lookup has returned got in a0,
   to 0x130d0, where [bne s6, s7] compares got with want.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import StrFun LockSpec LockSpecExp.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import bcmp_c field.
Import ListNotations.
Open Scope Z_scope.

(** * The machine's tests, as Z tests. *)

Lemma eqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_s : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros E. apply N.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ltu_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Lemma lts_s : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

Lemma slt_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_unsigned (v_slt (Z_to_bv 64 x) (Z_to_bv 64 y)) = Z.b2z (x <? y).
Proof. intros x y Hx Hy. unfold v_slt, c_lts. rewrite lts_s by lia. destruct (x <? y); vm_compute; reflexivity. Qed.

(* the 5% band test of fuzz_lock.c:113 at 0x130b4-0x130c0 *)
Lemma band_cond : forall per lo hi, 0 <= per < 2^63 -> 0 <= lo < 2^63 -> 0 <= hi < 2^63 ->
  negb (bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (v_slt (Z_to_bv 64 per) (Z_to_bv 64 lo)))
                                  (bv_unsigned (v_slt (Z_to_bv 64 hi) (Z_to_bv 64 per)))))
               (Z_to_bv 64 0)) = (per <? lo) || (hi <? per).
Proof.
  intros per lo hi H1 H2 H3. rewrite !slt_lit by lia.
  destruct (per <? lo), (hi <? per); vm_compute; reflexivity.
Qed.

(* the length test of [number] (fuzz_lock.c:67) at 0x13034 and 0x13074: len - 19 <u -18 *)
Lemma len_cond : forall x, 0 <= x < 2^63 ->
  bv_ltu (Z_to_bv 64 (x + -19)) (Z_to_bv 64 (-18)) = negb ((1 <=? x) && (x <=? 18)).
Proof.
  intros x Hx. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.leb_spec 1 x); destruct (Z.leb_spec x 18); cbn [andb negb].
  all: first [apply Z.ltb_ge | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

(* the digit test of [number] (fuzz_lock.c:70): c - 58 <u -10 *)
Lemma dig_cond : forall b : byte,
  bv_ltu (Z_to_bv 64 (bv_unsigned b + -58)) (Z_to_bv 64 (-10)) = negb ((48 <=? bz b) && (bz b <=? 57)).
Proof.
  intros b. pose proof (byte_range b) as R. unfold bz.
  pose proof (brute256_ok (fun c => Bool.eqb (bv_ltu (Z_to_bv 64 (c + -58)) (Z_to_bv 64 (-10)))
                                              (negb ((48 <=? c) && (c <=? 57))))
                ltac:(vm_compute; reflexivity) (bv_unsigned b) R) as H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma dig_val : forall b : byte, (48 <=? bz b) && (bz b <=? 57) = true ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) 15 = bz b - 48.
Proof.
  intros b D. pose proof (byte_range b) as R. unfold bz in *. rewrite unsigned_lit by lia.
  pose proof (brute256_ok (fun c => implb ((48 <=? c) && (c <=? 57)) (Z.land c 15 =? c - 48))
                ltac:(vm_compute; reflexivity) (bv_unsigned b) R) as H.
  cbv beta in H. rewrite D in H. cbn [implb] in H. apply Z.eqb_eq. exact H.
Qed.

Lemma seqz_byte : forall b : byte, bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned b)) 1) = Z.b2z (bz b =? 0).
Proof.
  intros b. pose proof (byte_range b) as R. unfold bz.
  pose proof (brute256_ok (fun c => bv_unsigned (v_sltiu (Z_to_bv 64 c) 1) =? Z.b2z (c =? 0))
                ltac:(vm_compute; reflexivity) (bv_unsigned b) R) as H.
  apply Z.eqb_eq. exact H.
Qed.

Lemma nul_cond : forall x : bool, negb (bv_eqb (Z_to_bv 64 (Z.b2z x)) (Z_to_bv 64 0)) = x.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma lor_b2z : forall x y : bool, Z.lor (Z.b2z x) (Z.b2z y) = Z.b2z (x || y).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma b2z_range : forall x : bool, 0 <= Z.b2z x <= 1.
Proof. intros [|]; cbn; lia. Qed.

(** * Bytes. *)

Lemma nth_firstn : forall {X} (l : list X) n j, (j < n)%nat -> nth_error (firstn n l) j = nth_error l j.
Proof.
  intros X l; induction l as [|x l IH]; intros [|n] [|j] H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_skipn : forall {X} (l : list X) i j, nth_error (skipn i l) j = nth_error l (i + j).
Proof.
  intros X l i; revert l; induction i as [|i IH]; intros l j; [reflexivity|].
  destruct l as [|x l]; [destruct j; reflexivity|]. cbn. apply IH.
Qed.

Lemma byte_at' : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia. Qed.

Lemma bytes_sub : forall m A (l : list byte) i n, bytes_at rsegs m A l -> (i + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat i) (firstn n (skipn i l)).
Proof.
  intros m A l i n (H1 & H2 & H) Hn. unfold bytes_at. rewrite length_firstn, length_skipn.
  split; [lia|]. split; [lia|]. intros j Hj.
  replace (A + Z.of_nat i + Z.of_nat j) with (A + Z.of_nat (i + j)) by lia.
  rewrite H by lia. rewrite nth_firstn by lia. rewrite nth_skipn. reflexivity.
Qed.

Lemma rd_at : forall m A (l : list byte) (j : nat) b, bytes_at rsegs m A l -> nth_error l j = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (A + Z.of_nat j)) 1 = Some [b].
Proof. intros m A l j b H N. exact (rdb m A l j b H N). Qed.

Lemma rd_at' : forall m A I (l : list byte) (j : nat) b, bytes_at rsegs m (A + I) l -> nth_error l j = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (A + (I + Z.of_nat j))) 1 = Some [b].
Proof. intros m A I l j b H N. rewrite Z.add_assoc. exact (rdb m (A + I) l j b H N). Qed.

Lemma rd0 : forall m A b (r : list byte), bytes_at rsegs m A (b :: r) -> ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [b].
Proof. intros m A b r H. pose proof (rdb m A (b :: r) 0 b H eq_refl) as R. rewrite Z.add_0_r in R. exact R. Qed.

Lemma bytes_tl : forall m A b (r : list byte), bytes_at rsegs m A (b :: r) -> bytes_at rsegs m (A + 1) r.
Proof. intros m A b r H. apply (bytes_at_app rsegs m A [b] r) in H. destruct H as [_ H]. exact H. Qed.

Lemma bytes_len : forall m A (l : list byte), bytes_at rsegs m A l -> 0 <= A /\ A + Z.of_nat (length l) <= 2^64.
Proof. intros m A l (H1 & H2 & _). lia. Qed.

Ltac zb_true := symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; lia.
Ltac zb_false := symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; lia.
Ltac setc v := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota|] end.
Ltac stp := step; try unfold zxb.

(** * The walk. *)
Section Walk.
Variables (gp tp s0 got : word) (F : bvmap 5 word) (fc : bv 32).
Variables (sp tx pa rate lo hi : Z) (T P SL : list byte).
Variable Q : machine_state -> Prop.

Local Notation PP := (P ++ Z_to_bv 8 0 :: SL).
Local Notation N := (Z.of_nat (length T)).

Hypothesis HSP : 0 <= sp.
Hypothesis HSPE : sp + 72 <= 2^64.
Hypothesis HTX : 0 <= tx.
Hypothesis HTE : tx + N < 2^64.
Hypothesis HPA : 0 <= pa.
Hypothesis HPE : pa + Z.of_nat (length PP) <= 2^64.
Hypothesis HN : N <= 65536.
Hypothesis HK : (length P <= 15)%nat.
Hypothesis HR : std_period rate <> 0.
Hypothesis HLO : lo = std_period rate - std_period rate / 20.
Hypothesis HHI : hi = std_period rate + std_period rate / 20.
Hypothesis DT : tx + N <= sp \/ sp + 72 <= tx.
Hypothesis DP : pa + Z.of_nat (length P + 1 + length SL) <= sp \/ sp + 72 <= pa.

Lemma rate_vals : (rate = 44100 /\ lo = 258504 /\ hi = 285714) \/ (rate = 48000 /\ lo = 237500 /\ hi = 262500) \/
  (rate = 96000 /\ lo = 118750 /\ hi = 131250).
Proof.
  rewrite HLO, HHI. destruct (std_period_nz rate HR) as [->|[->| ->]]; [left|right; left|right; right];
    repeat split; vm_compute; reflexivity.
Qed.

Lemma rate_rng : 0 <= rate < 2^63 /\ 0 <= lo < 2^63 /\ 0 <= hi < 2^63 /\ 0 <= lo.
Proof. destruct rate_vals as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]; lia. Qed.

(* the state inside the line loop: t0 = 2, t1 = '#', t2 = lo, t3 = hi, a6 = &fs, a7 = 1, s8 = 10, s9 = ' ',
   s10 = the separator mask, s11 = &fl *)
Local Notation ST pc ra a0 a1 a2 a3 a4 a5 s2 s7 t4 t5 t6 m :=
  (MS (mkR ra (Z_to_bv 64 sp) gp tp (Z_to_bv 64 2) (Z_to_bv 64 35) (Z_to_bv 64 lo) s0 (Z_to_bv 64 rate)
           a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (sp + 48)) (Z_to_bv 64 1)
           s2 (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx) got s7
           (Z_to_bv 64 10) (Z_to_bv 64 32) (Z_to_bv 64 4294976000) (Z_to_bv 64 (sp + 24))
           (Z_to_bv 64 hi) t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* the LF scan of fuzz_lock.c:86-87, at 0x12ed8: s2 runs from i to the line's end *)
Lemma eol_loop : forall m (i : nat) k o (ra a0 a2 a3 a4 a5 s7 t4 t5 t6 : word) (v2 : Z),
  bytes_at rsegs m tx T ->
  (o + S k = length (skipn i T))%nat -> find_byte 10 (firstn o (skipn i T)) = None ->
  v2 = Z.of_nat (i + o) ->
  (forall a2' : word, evt rsegs Q (ST 0x12ef0 ra a0 (Z_to_bv 64 N) a2' a3 a4 a5
                                   (Z_to_bv 64 (Z.of_nat (i + line_len (skipn i T)))) s7 t4 t5 t6 m)) ->
  evt rsegs Q (ST 0x12ed8 ra a0 (Z_to_bv 64 N) a2 a3 a4 a5 (Z_to_bv 64 v2) s7 t4 t5 t6 m).
Proof.
  intros m i k. induction k as [|k IH]; intros o ra a0 a2 a3 a4 a5 s7 t4 t5 t6 v2 BT Hk HF -> K.
  all: rewrite length_skipn in Hk.
  all: destruct (byte_at' (skipn i T) o ltac:(rewrite length_skipn; lia)) as [b Nb].
  all: pose proof Nb as NbT; rewrite nth_skipn in NbT.
  all: pose proof (rd_at m tx T (i + o) b BT NbT) as R.
  all: pose proof (byte_range b) as Rb.
  all: step; stp; step.
  all: rewrite eqb_u by lia.
  all: destruct (Z.eqb_spec (bv_unsigned b) 10) as [E|E]; cbv iota.
  1, 3: (replace (line_len (skipn i T)) with o in K; [apply K|];
         unfold line_len; rewrite (find_byte_at 10 (skipn i T) o b HF Nb E); reflexivity).
  - step. step. rewrite eqb_u by lia. replace (N =? Z.of_nat (i + o) + 1) with true by zb_true. cbn [negb]; cbv iota.
    step.
    replace (line_len (skipn i T)) with (length (skipn i T)) in K; [rewrite length_skipn in K;
      replace (Z.of_nat (i + (length T - i))) with N in K by lia; apply K|].
    unfold line_len. rewrite (find_byte_all 10 (skipn i T)); [reflexivity|].
    replace (length (skipn i T)) with (S o) by (rewrite length_skipn; lia).
    rewrite (firstn_snoc _ o b Nb). apply find_byte_snoc_none; assumption.
  - step. step. rewrite eqb_u by lia. replace (N =? Z.of_nat (i + o) + 1) with false by zb_false. cbn [negb]; cbv iota.
    eapply (IH (S o)); [exact BT | rewrite length_skipn; lia | | lia | exact K].
    rewrite (firstn_snoc _ o b Nb). apply find_byte_snoc_none; assumption.
Qed.

(* the NUL scan of fuzz_lock.c:92-93, at 0x12f18: a2 runs over the line l at tx + I *)
Lemma nul_loop : forall m (l : list byte) (I : Z) k o (ra a0 a4 a5 s2 s7 t4 t5 t6 : word) (v1 v2 v3 : Z),
  bytes_at rsegs m (tx + I) l -> 0 <= I -> tx + I + Z.of_nat (length l) < 2^64 -> (o + S k = length l)%nat ->
  v1 = Z.b2z (nulb (firstn o l)) -> v2 = tx + I + Z.of_nat o -> v3 = tx + I + Z.of_nat (length l) ->
  (forall (a2' a3' a4' : word) (w1 : Z), w1 = Z.b2z (nulb l) ->
     evt rsegs Q (ST 0x12f2c ra a0 (Z_to_bv 64 w1) a2' a3' a4' a5 s2 s7 t4 t5 t6 m)) ->
  evt rsegs Q (ST 0x12f18 ra a0 (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 v3) a4 a5 s2 s7 t4 t5 t6 m).
Proof.
  intros m l I k. induction k as [|k IH]; intros o ra a0 a4 a5 s2 s7 t4 t5 t6 v1 v2 v3 BL HI HE Hk -> -> -> K.
  all: destruct (byte_at' l o ltac:(lia)) as [b Nb].
  all: pose proof (rd_at m (tx + I) l o b BL Nb) as R.
  all: pose proof (byte_range b) as Rb. all: pose proof (b2z_range (nulb (firstn o l))) as Rn.
  all: stp; step; step; step; step.
  all: rewrite eqb_u by lia.
  - replace (tx + I + Z.of_nat o + 1 =? tx + I + Z.of_nat (length l)) with true by zb_true. cbn [negb]; cbv iota.
    apply K. rewrite unsigned_lit by lia. rewrite seqz_byte, lor_b2z, <- nulb_snoc, <- (firstn_snoc _ o b Nb).
    replace (S o) with (length l) by lia. rewrite firstn_all. reflexivity.
  - replace (tx + I + Z.of_nat o + 1 =? tx + I + Z.of_nat (length l)) with false by zb_false. cbn [negb]; cbv iota.
    eapply (IH (S o)); [exact BL | lia | lia | lia | | lia | reflexivity | exact K].
    rewrite unsigned_lit by lia. rewrite seqz_byte, lor_b2z, <- nulb_snoc, <- (firstn_snoc _ o b Nb). reflexivity.
Qed.

(* the separator skip of fuzz_lock.c:95-98, at 0x12f38: a3 runs from the line offset q *)
Lemma sep_loop : forall m (l : list byte) (I : Z) (q : nat) k o (ra a0 a1 a2 a4 a5 s7 t4 t5 t6 : word) (v3 v2 : Z),
  bytes_at rsegs m (tx + I) l -> 0 <= I -> tx + I + Z.of_nat (length l) < 2^64 ->
  (q + o + S k = length l)%nat -> sep_run (skipn q l) = (o + sep_run (skipn (q + o) l))%nat ->
  v3 = I + Z.of_nat (q + o) -> v2 = I + Z.of_nat (length l) ->
  (forall a0' a3' a4' : word, (q + sep_run (skipn q l) = length l)%nat ->
     evt rsegs Q (ST 0x12ffc ra a0' a1 a2 a3' a4' a5 (Z_to_bv 64 v2) s7 t4 t5 t6 m)) ->
  (forall a4' : word, (q + sep_run (skipn q l) < length l)%nat ->
     evt rsegs Q (ST 0x12f5c ra (Z_to_bv 64 (tx + (I + Z.of_nat (q + sep_run (skipn q l))))) a1 a2
                    (Z_to_bv 64 (I + Z.of_nat (q + sep_run (skipn q l)))) a4' a5 (Z_to_bv 64 v2) s7 t4 t5 t6 m)) ->
  evt rsegs Q (ST 0x12f38 ra a0 a1 a2 (Z_to_bv 64 v3) a4 a5 (Z_to_bv 64 v2) s7 t4 t5 t6 m).
Proof.
  intros m l I q k. induction k as [|k IH]; intros o ra a0 a1 a2 a4 a5 s7 t4 t5 t6 v3 v2 BL HI HE Hk Hsr -> -> K1 K2.
  all: destruct (byte_at' l (q + o) ltac:(lia)) as [b Nb].
  all: pose proof (rd_at' m tx I l (q + o) b BL Nb) as R.
  all: rewrite (skipn_nth l (q + o) b Nb) in Hsr; cbn [sep_run] in Hsr.
  all: step; stp; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota.
  all: lazymatch goal with
       | C1 : bv_ltu _ _ = true |- _ => pose proof (sep_hi b C1) as SB
       | C1 : bv_ltu _ _ = false |- _ =>
           step; step; step; rewrite (sep_lo b C1); destruct (is_sep (bz b)) eqn:SB; cbn [negb]; cbv iota
       end.
  all: try rewrite SB in Hsr; cbv iota in Hsr.
  all: lazymatch type of SB with
       | _ = false => replace (q + sep_run (skipn q l))%nat with (q + o)%nat in K2 by lia; apply K2; lia
       | _ = true => idtac
       end.
  - step. step. rewrite ltu_u by lia.
    replace (I + Z.of_nat (q + o) + 1 <? I + Z.of_nat (length l)) with false by zb_false. cbv iota.
    step. apply K1.
    assert (skipn (S (q + o)) l = []) by (apply skipn_all2; lia). rewrite H in Hsr. cbn in Hsr. lia.
  - step. step. rewrite ltu_u by lia.
    replace (I + Z.of_nat (q + o) + 1 <? I + Z.of_nat (length l)) with true by zb_true. cbv iota.
    eapply (IH (S o)); [exact BL | lia | lia | lia | | lia | reflexivity | exact K1 | exact K2].
    rewrite Hsr. replace (q + S o)%nat with (S (q + o)) by lia. lia.
Qed.

(* the field's run of fuzz_lock.c:100-101, at 0x12f74: a0 runs from the field's start o *)
Lemma tok_loop : forall m (l : list byte) (I : Z) (o : nat) k j (ra a1 a2 a4 a5 s7 t4 t5 t6 : word) (v0 v3 v2 : Z),
  bytes_at rsegs m (tx + I) l -> 0 <= I -> tx + I + Z.of_nat (length l) < 2^64 ->
  (o + j + S k = length l)%nat -> tok_run (skipn o l) = (j + tok_run (skipn (o + j) l))%nat ->
  v0 = I + Z.of_nat (o + j) -> v3 = I + Z.of_nat o -> v2 = I + Z.of_nat (length l) ->
  (forall (a5' : word) (w : Z), w = I + Z.of_nat (o + tok_run (skipn o l)) ->
     evt rsegs Q (ST 0x12f98 ra (Z_to_bv 64 w) a1 a2 (Z_to_bv 64 v3) a4 a5' (Z_to_bv 64 v2) s7 t4 t5 t6 m)) ->
  evt rsegs Q (ST 0x12f74 ra (Z_to_bv 64 v0) a1 a2 (Z_to_bv 64 v3) a4 a5 (Z_to_bv 64 v2) s7 t4 t5 t6 m).
Proof.
  intros m l I o. induction k as [|k IH]; intros j ra a1 a2 a4 a5 s7 t4 t5 t6 v0 v3 v2 BL HI HE Hk Htr -> -> -> K.
  all: destruct (byte_at' l (o + j) ltac:(lia)) as [b Nb].
  all: pose proof (rd_at' m tx I l (o + j) b BL Nb) as R.
  all: rewrite (skipn_nth l (o + j) b Nb) in Htr; cbn [tok_run] in Htr.
  all: step; stp; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota.
  all: lazymatch goal with
       | C1 : bv_ltu _ _ = true |- _ => pose proof (sep_hi b C1) as SB
       | C1 : bv_ltu _ _ = false |- _ =>
           step; step; step; rewrite (sep_lo b C1); destruct (is_sep (bz b)) eqn:SB; cbn [negb]; cbv iota
       end.
  all: try rewrite SB in Htr; cbv iota in Htr.
  (* a separator ends the field at o + j; else the field goes on: a0 + 1 *)
  all: lazymatch type of SB with
       | _ = true => apply K; lia
       | _ = false => step; step; rewrite eqb_u by lia
       end.
  all: first
       [ replace (I + Z.of_nat (length l) =? I + Z.of_nat (o + j) + 1) with true by zb_true; cbn [negb]; cbv iota;
         step; apply K; assert (skipn (S (o + j)) l = []) by (apply skipn_all2; lia);
         rewrite H in Htr; cbn in Htr; lia
       | replace (I + Z.of_nat (length l) =? I + Z.of_nat (o + j) + 1) with false by zb_false; cbn [negb]; cbv iota;
         eapply (IH (S j)); [exact BL | lia | lia | lia | | lia | reflexivity | reflexivity | exact K];
         rewrite Htr; replace (o + S j)%nat with (S (o + j)) by lia; lia ].
Qed.

(* the digit loop of [number] for the period (fuzz_lock.c:69-73), at 0x13040: a0 the value, a1 the bytes left *)
Lemma dig1_loop : forall m (A : Z) (ls : list byte) k (v : Z) (ra a3 a4 a5 s2 s7 t5 t6 : word) (v0 v1 v2 : Z),
  bytes_at rsegs m A ls -> length ls = S k -> (length ls <= 18)%nat -> 0 <= v < 10 ^ Z.of_nat (18 - length ls) ->
  v0 = v -> v1 = Z.of_nat (length ls) -> v2 = A -> A + Z.of_nat (length ls) < 2^64 ->
  (forall (a1' a2' a3' a4' : word) (w : Z), w = dig_go ls v ->
     evt rsegs Q (ST 0x1306c ra (Z_to_bv 64 w) a1' a2' a3' a4' a5 s2 s7 (Z_to_bv 64 (-10)) t5 t6 m)) ->
  evt rsegs Q (ST 0x13040 ra (Z_to_bv 64 v0) (Z_to_bv 64 v1) (Z_to_bv 64 v2) a3 a4 a5 s2 s7 (Z_to_bv 64 (-10)) t5 t6 m).
Proof.
  intros m A ls k. revert A ls. induction k as [|k IH];
    intros A ls v ra a3 a4 a5 s2 s7 t5 t6 v0 v1 v2 BL Hl H18 Hv -> -> -> HA K.
  all: destruct ls as [|b r]; [discriminate|]. all: cbn [length] in Hl; injection Hl as Hl.
  all: pose proof (rd0 m A b r BL) as R. all: pose proof (byte_range b) as Rb.
  all: assert (P10 : 10 ^ Z.of_nat (18 - length (b :: r)) * 10 <= 1000000000000000000)
         by (change 1000000000000000000 with (10 ^ 18); rewrite Z.mul_comm, <- Z.pow_succ_r by lia;
             apply Z.pow_le_mono_r; cbn [length] in *; lia).
  all: stp; step; step; rewrite dig_cond; destruct ((48 <=? bz b) && (bz b <=? 57)) eqn:D; cbn [negb]; cbv iota.
  2, 4: (step; apply K; cbn [dig_go]; rewrite D; reflexivity).
  all: do 6 step; rewrite eqb_u by (cbn [length] in *; lia).
  - replace (Z.of_nat (length (b :: r)) + -1 =? 0) with true by (cbn [length]; zb_true). cbn [negb]; cbv iota.
    step. apply K. cbn [dig_go]. rewrite D. destruct r; [|cbn in Hl; discriminate Hl]. cbn [dig_go].
    rewrite unsigned_lit by lia. rewrite dig_val by exact D. reflexivity.
  - replace (Z.of_nat (length (b :: r)) + -1 =? 0) with false by (cbn [length]; zb_false). cbn [negb]; cbv iota.
    pose proof (bytes_tl m A b r BL) as BR.
    eapply (IH (A + 1) r (v * 10 + (bz b - 48))); [exact BR | exact Hl | cbn [length] in H18; lia | | | | reflexivity | | ].
    + apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1, D2.
      cbn [length] in Hv, H18. replace (Z.of_nat (18 - S (length r))) with (Z.of_nat (18 - length r) - 1) in Hv by lia.
      assert (E : 10 ^ Z.of_nat (18 - length r) = 10 * 10 ^ (Z.of_nat (18 - length r) - 1))
        by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      rewrite E. unfold bz in *. lia.
    + rewrite unsigned_lit by lia. rewrite dig_val by exact D. reflexivity.
    + cbn [length]. lia.
    + cbn [length] in HA. lia.
    + intros a1' a2' a3' a4' w Hw. apply K. cbn [dig_go]. rewrite D. exact Hw.
Qed.

(* the digit loop of [number] for the label, at 0x13088: a3 the value, a1 the bytes left; a non-digit goes by
   0x13078 (a3 = -1) *)
Lemma dig2_loop : forall m (A : Z) (ls : list byte) k (v : Z) (ra a0 a4 a5 s2 s7 t5 t6 : word) (v3 v1 v2 : Z),
  bytes_at rsegs m A ls -> length ls = S k -> (length ls <= 18)%nat -> 0 <= v < 10 ^ Z.of_nat (18 - length ls) ->
  v3 = v -> v1 = Z.of_nat (length ls) -> v2 = A -> A + Z.of_nat (length ls) < 2^64 ->
  (forall (a1' a2' a4' a5' : word) (w : Z), w = dig_go ls v ->
     evt rsegs Q (ST 0x130ac ra a0 a1' a2' (Z_to_bv 64 w) a4' a5' s2 s7 (Z_to_bv 64 (-10)) t5 t6 m)) ->
  evt rsegs Q (ST 0x13088 ra a0 (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 v3) a4 a5 s2 s7 (Z_to_bv 64 (-10)) t5 t6 m).
Proof.
  intros m A ls k. revert A ls. induction k as [|k IH];
    intros A ls v ra a0 a4 a5 s2 s7 t5 t6 v3 v1 v2 BL Hl H18 Hv -> -> -> HA K.
  all: destruct ls as [|b r]; [discriminate|]. all: cbn [length] in Hl; injection Hl as Hl.
  all: pose proof (rd0 m A b r BL) as R. all: pose proof (byte_range b) as Rb.
  all: assert (P10 : 10 ^ Z.of_nat (18 - length (b :: r)) * 10 <= 1000000000000000000)
         by (change 1000000000000000000 with (10 ^ 18); rewrite Z.mul_comm, <- Z.pow_succ_r by lia;
             apply Z.pow_le_mono_r; cbn [length] in *; lia).
  all: stp; step; step; rewrite dig_cond; destruct ((48 <=? bz b) && (bz b <=? 57)) eqn:D; cbn [negb]; cbv iota.
  2, 4: (step; step; apply K; cbn [dig_go]; rewrite D; reflexivity).
  all: do 6 step; rewrite eqb_u by (cbn [length] in *; lia).
  - replace (Z.of_nat (length (b :: r)) + -1 =? 0) with true by (cbn [length]; zb_true). cbn [negb]; cbv iota.
    apply K. cbn [dig_go]. rewrite D. destruct r; [|cbn in Hl; discriminate Hl]. cbn [dig_go].
    rewrite unsigned_lit by lia. rewrite dig_val by exact D. reflexivity.
  - replace (Z.of_nat (length (b :: r)) + -1 =? 0) with false by (cbn [length]; zb_false). cbn [negb]; cbv iota.
    pose proof (bytes_tl m A b r BL) as BR.
    eapply (IH (A + 1) r (v * 10 + (bz b - 48))); [exact BR | exact Hl | cbn [length] in H18; lia | | | | reflexivity | | ].
    + apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1, D2.
      cbn [length] in Hv, H18. replace (Z.of_nat (18 - S (length r))) with (Z.of_nat (18 - length r) - 1) in Hv by lia.
      assert (E : 10 ^ Z.of_nat (18 - length r) = 10 * 10 ^ (Z.of_nat (18 - length r) - 1))
        by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      rewrite E. unfold bz in *. lia.
    + rewrite unsigned_lit by lia. rewrite dig_val by exact D. reflexivity.
    + cbn [length]. lia.
    + cbn [length] in HA. lia.
    + intros a1' a2' a4' a5' w Hw. apply K. cbn [dig_go]. rewrite D. exact Hw.
Qed.

(** ** The frame: the scratch slots sp..sp+0x48 of check_lookup's frame. *)
Variable m0 : word -> option byte.
Hypothesis BC : bcmp_contract.

(* the line loop's memory: t3/t2 spills at sp, k at sp+0x10, fl[3] at sp+0x18, fs[3] at sp+0x30 *)
Definition Inv (m : word -> option byte) : Prop :=
  munch [(sp, sp + 72)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  bytes_at rsegs m tx T /\ bytes_at rsegs m pa PP /\
  (exists j0, rw_cells rsegs m sp [CB 16 j0]) /\ rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] /\
  (exists j1, rw_cells rsegs m (sp + 24) [CB 24 j1]) /\ (exists j2, rw_cells rsegs m (sp + 48) [CB 24 j2]).

Lemma inv_intro : forall m c0 c1 c2,
  munch [(sp, sp + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa PP ->
  rw_cells rsegs m sp c0 -> cells_size c0 = 16%nat ->
  rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] ->
  rw_cells rsegs m (sp + 24) c1 -> cells_size c1 = 24%nat ->
  rw_cells rsegs m (sp + 48) c2 -> cells_size c2 = 24%nat -> Inv m.
Proof.
  intros m c0 c1 c2 MU WM MI BT BP C0 S0 CK C1 S1 C2 S2.
  destruct (rw_cells_forget rsegs m sp c0 C0) as [j0 J0]. rewrite S0 in J0.
  destruct (rw_cells_forget rsegs m (sp + 24) c1 C1) as [j1 J1]. rewrite S1 in J1.
  destruct (rw_cells_forget rsegs m (sp + 48) c2 C2) as [j2 J2]. rewrite S2 in J2.
  exact (conj MU (conj WM (conj MI (conj BT (conj BP (conj (ex_intro _ j0 J0) (conj CK
          (conj (ex_intro _ j1 J1) (ex_intro _ j2 J2))))))))).
Qed.

Ltac inv_tac := eapply inv_intro;
  [ eassumption | eassumption | eassumption | eassumption | eassumption
  | eassumption | first [reflexivity | eassumption] | eassumption | eassumption | first [reflexivity | eassumption]
  | eassumption | first [reflexivity | eassumption] ].

(* the end of a line, 0x12ffc: s2 = the line's end, s7 = the period found so far *)
Definition Kont (e f : Z) : Prop :=
  forall (ra a0 a1 a2 a3 a4 a5 t4 t5 t6 : word) (m : word -> option byte),
    Inv m -> evt rsegs Q (ST 0x12ffc ra a0 a1 a2 a3 a4 a5 (Z_to_bv 64 e) (Z_to_bv 64 f) t4 t5 t6 m).

(** ** One line: the bytes LN of T from i, len bytes long. *)
Section Line.
Variables (i len : nat) (found : Z).
Hypothesis HIL : (i + len <= length T)%nat.
Local Notation LN := (firstn len (skipn i T)).
Local Notation EE := (Z.of_nat (i + len)).
Hypothesis KB : Kont EE (upd P rate LN found).

Lemma LN_len : length LN = len.
Proof. rewrite length_firstn, length_skipn. lia. Qed.

Lemma cont_found : forall m (ra a0 a1 a2 a3 a4 a5 t4 t5 t6 : word),
  upd P rate LN found = found -> Inv m ->
  evt rsegs Q (ST 0x12ffc ra a0 a1 a2 a3 a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a0 a1 a2 a3 a4 a5 t4 t5 t6 U INV. pose proof (KB ra a0 a1 a2 a3 a4 a5 t4 t5 t6 m INV) as K.
  rewrite U in K. exact K.
Qed.

Lemma cont_val : forall m (ra a0 a1 a2 a3 a4 a5 t4 t5 t6 : word) v,
  line_val P rate LN = Some v -> Inv m ->
  evt rsegs Q (ST 0x12ffc ra a0 a1 a2 a3 a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 v) t4 t5 t6 m).
Proof.
  intros m ra a0 a1 a2 a3 a4 a5 t4 t5 t6 v LV INV. pose proof (KB ra a0 a1 a2 a3 a4 a5 t4 t5 t6 m INV) as K.
  rewrite (upd_some P rate LN found v LV) in K. exact K.
Qed.

(* the 5% band and the store of found, 0x130ac-0x130c8 (fuzz_lock.c:111-115) *)
Lemma st_band : forall m (ra a1 a2 a4 a5 t4 t5 t6 : word) s1 l1 s2 l2 s3 l3 (per lab : Z),
  Inv m ->
  fld LN 0 = (s1, l1) -> fld LN (s1 + l1) = (s2, l2) -> fld LN (s2 + l2) = (s3, l3) ->
  find_byte 0 LN = None -> l1 <> 0%nat -> bz (nth s1 LN (Z_to_bv 8 0)) <> 35 -> l1 = length P ->
  memcmp_model (slice LN s1 l1) P l1 = Some 0 ->
  per = digits (slice LN s2 l2) -> lab = digits (slice LN s3 l3) ->
  evt rsegs Q (ST 0x130ac ra (Z_to_bv 64 per) a1 a2 (Z_to_bv 64 lab) a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a1 a2 a4 a5 t4 t5 t6 s1 l1 s2 l2 s3 l3 per lab INV E1 E2 E3 F0 L1 NH LP M -> ->.
  pose proof (digits_range (slice LN s2 l2)) as R2. pose proof (digits_range (slice LN s3 l3)) as R3.
  change (10 ^ 18) with 1000000000000000000 in R2, R3.
  pose proof rate_rng as RR.
  assert (NONE : forall v, line_val P rate LN = Some v -> 0 <= v /\ digits (slice LN s3 l3) = rate /\ lo <= v <= hi /\
                   v = digits (slice LN s2 l2)).
  { intros v LV. destruct (line_val_inv P rate LN s1 l1 s2 l2 s3 l3 v E1 E2 E3 LV) as (_ & _ & _ & _ & _ & _ & V & P0 & L & B).
    rewrite HLO, HHI. lia. }
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (digits (slice LN s2 l2)) 0) as [Hn|Hn]; cbv iota.
  { apply cont_found; [|exact INV]. apply upd_none. intros v LV. destruct (NONE v LV) as (A & _ & _ & ->). lia. }
  step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (digits (slice LN s3 l3)) rate) as [Hl|Hl]; cbn [negb]; cbv iota.
  2: { apply cont_found; [|exact INV]. apply upd_none. intros v LV. destruct (NONE v LV) as (_ & A & _). lia. }
  do 4 step. rewrite ?alu_slt. rewrite band_cond by lia.
  destruct ((digits (slice LN s2 l2) <? lo) || (hi <? digits (slice LN s2 l2))) eqn:B; cbv iota.
  { apply cont_found; [|exact INV]. apply upd_none. intros v LV. destruct (NONE v LV) as (_ & _ & A & ->).
    apply orb_true_iff in B. destruct B as [B|B]; apply Z.ltb_lt in B; lia. }
  step. step. apply cont_val; [|exact INV].
  apply orb_false_iff in B. destruct B as [B1 B2]. apply Z.ltb_ge in B1, B2.
  apply (line_val_some P rate LN s1 l1 s2 l2 s3 l3 E1 E2 E3 F0 L1 NH); try assumption; try lia.
Qed.

Lemma num_bad : forall l s n, (s + n <= length l)%nat -> ~ (1 <= Z.of_nat n <= 18) -> digits (slice l s n) = -1.
Proof.
  intros l s n H N. apply digits_bad_len. unfold slice. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma num_good : forall l s n, (s + n <= length l)%nat -> 1 <= Z.of_nat n <= 18 ->
  digits (slice l s n) = dig_go (slice l s n) 0.
Proof.
  intros l s n H N. apply digits_good_len. unfold slice. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma slice_len : forall l s n, (s + n <= length l)%nat -> length (slice l s n) = n.
Proof. intros l s n H. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

(* the label, 0x1306c-0x130a8 (fuzz_lock.c:110, number(fs[2], fl[2])) *)
Lemma st_num2 : forall m (ra a1 a2 a3 a4 t5 t6 : word) c0 s1 l1 s2 l2 s3 l3 per,
  munch [(sp, sp + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa PP ->
  rw_cells rsegs m sp c0 -> cells_size c0 = 16%nat ->
  rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] ->
  rw_cells rsegs m (sp + 24) [C8 (Z_to_bv 64 (Z.of_nat l1)); C8 (Z_to_bv 64 (Z.of_nat l2)); C8 (Z_to_bv 64 (Z.of_nat l3))] ->
  rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s1))); C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s2)));
                             C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s3)))] ->
  fld LN 0 = (s1, l1) -> fld LN (s1 + l1) = (s2, l2) -> fld LN (s2 + l2) = (s3, l3) ->
  find_byte 0 LN = None -> l1 <> 0%nat -> bz (nth s1 LN (Z_to_bv 8 0)) <> 35 -> l1 = length P ->
  memcmp_model (slice LN s1 l1) P l1 = Some 0 -> per = digits (slice LN s2 l2) ->
  evt rsegs Q (ST 0x1306c ra (Z_to_bv 64 per) a1 a2 a3 a4 (Z_to_bv 64 (-18)) (Z_to_bv 64 EE) (Z_to_bv 64 found)
                 (Z_to_bv 64 (-10)) t5 t6 m).
Proof.
  intros m ra a1 a2 a3 a4 t5 t6 c0 s1 l1 s2 l2 s3 l3 per MU WM MI BT BP C0 S0 CK CL CS E1 E2 E3 F0 L1 NH LP M Hper.
  pose proof LN_len as LL.
  pose proof (fld_bound LN (s2 + l2)) as B3. rewrite E3 in B3. cbn [fst snd] in B3.
  pose proof (fld_bound LN (s1 + l1)) as B2. rewrite E2 in B2. cbn [fst snd] in B2.
  pose proof (fld_bound LN 0) as B1. rewrite E1 in B1. cbn [fst snd] in B1.
  specialize (B1 ltac:(lia)). specialize (B2 ltac:(lia)). specialize (B3 ltac:(lia)).
  assert (INV : Inv m) by inv_tac.
  pose proof (bytes_sub m tx T i len BT HIL) as BL.
  step. step. step. rewrite len_cond by lia.
  destruct ((1 <=? Z.of_nat l3) && (Z.of_nat l3 <=? 18)) eqn:LR; cbn [negb]; cbv iota.
  - apply andb_true_iff in LR as [LR1 LR2]. apply Z.leb_le in LR1, LR2.
    step. step.
    pose proof (bytes_sub m (tx + Z.of_nat i) LN s3 l3 BL ltac:(lia)) as LS.
    eapply (dig2_loop m (tx + Z.of_nat i + Z.of_nat s3) (slice LN s3 l3) (l3 - 1) 0);
      [ exact LS | rewrite slice_len by lia; lia | rewrite slice_len by lia; lia
      | rewrite slice_len by lia; split; [lia | apply Z.pow_pos_nonneg; lia] | reflexivity
      | rewrite slice_len by lia; reflexivity | lia | rewrite slice_len by lia; lia | ].
    intros a1' a2' a4' a5' w Hw.
    eapply (st_band m ra a1' a2' a4' a5' (Z_to_bv 64 (-10)) t5 t6 s1 l1 s2 l2 s3 l3); try eassumption.
    rewrite Hw. symmetry. apply num_good; lia.
  - step. step.
    eapply (st_band m ra _ _ _ _ (Z_to_bv 64 (-10)) t5 t6 s1 l1 s2 l2 s3 l3); try eassumption.
    symmetry. apply num_bad; [lia|]. intros [A B]. apply andb_false_iff in LR.
    destruct LR as [LR|LR]; apply Z.leb_gt in LR; lia.
Qed.

(* the three fields are read: the checks of fuzz_lock.c:106-110, 0x12fb0-0x1306c, with the call of bcmp *)
Lemma st_checks : forall m (ra a0 a3 a4 a5 t4 t5 t6 : word) (j0 : list byte) s1 l1 s2 l2 s3 l3,
  munch [(sp, sp + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa PP ->
  rw_cells rsegs m sp [CB 16 j0] -> rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] ->
  rw_cells rsegs m (sp + 24) [C8 (Z_to_bv 64 (Z.of_nat l1)); C8 (Z_to_bv 64 (Z.of_nat l2)); C8 (Z_to_bv 64 (Z.of_nat l3))] ->
  rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s1))); C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s2)));
                             C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s3)))] ->
  fld LN 0 = (s1, l1) -> fld LN (s1 + l1) = (s2, l2) -> fld LN (s2 + l2) = (s3, l3) -> (s1 < length LN)%nat ->
  evt rsegs Q (ST 0x12fb0 ra a0 (Z_to_bv 64 (Z.b2z (nulb LN))) (Z_to_bv 64 2) a3 a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a0 a3 a4 a5 t4 t5 t6 j0 s1 l1 s2 l2 s3 l3 MU WM MI BT BP C0 CK CL CS E1 E2 E3 S1.
  pose proof LN_len as LL.
  pose proof (fld_bound LN (s2 + l2)) as B3. rewrite E3 in B3. cbn [fst snd] in B3.
  pose proof (fld_bound LN (s1 + l1)) as B2. rewrite E2 in B2. cbn [fst snd] in B2.
  pose proof (fld_bound LN 0) as B1. rewrite E1 in B1. cbn [fst snd] in B1.
  specialize (B1 ltac:(lia)). specialize (B2 ltac:(lia)). specialize (B3 ltac:(lia)).
  pose proof rate_rng as RR.
  assert (L1 : l1 <> 0%nat).
  { pose proof (sep_run_stop LN 0 ltac:(rewrite fld_eq in E1; injection E1 as <- _; lia)) as A.
    rewrite fld_eq in E1. injection E1 as <- <-. exact A. }
  pose proof (bytes_sub m tx T i len BT HIL) as BL.
  destruct (byte_at' LN s1 S1) as [b1 N1]. pose proof (byte_range b1) as Rb1.
  pose proof (rd_at' m tx (Z.of_nat i) LN s1 b1 BL N1) as R1.
  (* nul: fuzz_lock.c:106 *)
  step. rewrite nul_cond.
  destruct (nulb LN) eqn:NB; cbv iota.
  { apply cont_found; [|inv_tac]. apply upd_none. intros v LV.
    destruct (line_val_inv P rate LN s1 l1 s2 l2 s3 l3 v E1 E2 E3 LV) as (F0 & _).
    rewrite <- nulb_find, F0 in NB. discriminate NB. }
  assert (F0 : find_byte 0 LN = None).
  { rewrite <- nulb_find in NB. destruct (find_byte 0 LN); [discriminate NB | reflexivity]. }
  (* nf < 3 *)
  step. setc false; [|vm_compute; reflexivity].
  (* fs[0][0] == '#' *)
  step. stp. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (bv_unsigned b1) 35) as [H35|H35]; cbv iota.
  { apply cont_found; [|inv_tac]. apply upd_none. intros v LV.
    destruct (line_val_inv P rate LN s1 l1 s2 l2 s3 l3 v E1 E2 E3 LV) as (_ & _ & NH & _).
    apply NH. rewrite (nth_error_nth LN s1 _ N1). exact H35. }
  assert (NH : bz (nth s1 LN (Z_to_bv 8 0)) <> 35) by (rewrite (nth_error_nth LN s1 _ N1); exact H35).
  (* fl[0] != k *)
  step. step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (Z.of_nat l1) (Z.of_nat (length P))) as [HLP|HLP]; cbn [negb]; cbv iota.
  2: { apply cont_found; [|inv_tac]. apply upd_none. intros v LV.
       destruct (line_val_inv P rate LN s1 l1 s2 l2 s3 l3 v E1 E2 E3 LV) as (_ & _ & _ & _ & LP & _). lia. }
  apply Nat2Z.inj in HLP.
  (* memcmp(fs[0], port, k) *)
  remember (slice LN s1 l1) as ls eqn:ELS.
  assert (HLS : length ls = l1) by (subst ls; apply slice_len; lia).
  pose proof (bytes_sub m (tx + Z.of_nat i) LN s1 l1 BL ltac:(lia)) as LS. fold (slice LN s1 l1) in LS. rewrite <- ELS in LS.
  destruct (memcmp_model_total ls PP (length P)) as [v Hv]; [lia | rewrite length_app; cbn [length]; lia |].
  pose proof (memcmp_model_range _ _ _ _ Hv) as Rv.
  assert (HPL : length PP = (length P + 1 + length SL)%nat) by (rewrite length_app; cbn [length]; lia).
  step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply BC;
      [ rewrite unsigned_lit by lia; replace (tx + (Z.of_nat i + Z.of_nat s1)) with (tx + Z.of_nat i + Z.of_nat s1) by lia;
        exact LS
      | rewrite unsigned_lit by lia; exact BP
      | rewrite unsigned_lit by lia; rewrite Nat2Z.id; exact Hv
      | assumption ]
    | post_call segs mm ] end.
  step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  2: { do 6 step. apply cont_found; [|inv_tac]. apply upd_none. intros v' LV.
       destruct (line_val_inv P rate LN s1 l1 s2 l2 s3 l3 v' E1 E2 E3 LV) as (_ & _ & _ & _ & LP & MC & _).
       rewrite <- ELS, HLP in MC. rewrite memcmp_model_app_r in Hv by lia. rewrite Hv in MC. injection MC. lia. }
  subst v.
  assert (MC : memcmp_model (slice LN s1 l1) P l1 = Some 0).
  { rewrite <- ELS, HLP. rewrite memcmp_model_app_r in Hv by lia. exact Hv. }
  (* per = number(fs[1], fl[1]) *)
  do 12 step. rewrite len_cond by lia.
  destruct ((1 <=? Z.of_nat l2) && (Z.of_nat l2 <=? 18)) eqn:LR; cbn [negb]; cbv iota.
  - apply andb_true_iff in LR as [LR1 LR2]. apply Z.leb_le in LR1, LR2.
    step. step.
    pose proof (bytes_sub _ (tx + Z.of_nat i) LN s2 l2 BL ltac:(lia)) as LS2.
    eapply (dig1_loop _ (tx + Z.of_nat i + Z.of_nat s2) (slice LN s2 l2) (l2 - 1) 0);
      [ exact LS2 | rewrite slice_len by lia; lia | rewrite slice_len by lia; lia
      | rewrite slice_len by lia; split; [lia | apply Z.pow_pos_nonneg; lia] | reflexivity
      | rewrite slice_len by lia; reflexivity | lia | rewrite slice_len by lia; lia | ].
    intros a1' a2' a3' a4' w Hw.
    eapply st_num2; try eassumption; try reflexivity.
    rewrite Hw. symmetry. apply num_good; lia.
  - eapply st_num2; try eassumption; try reflexivity.
    symmetry. apply num_bad; [lia|]. intros [A B]. apply andb_false_iff in LR.
    destruct LR as [LR|LR]; apply Z.leb_gt in LR; lia.
Qed.

(* the third field, from 0x12f30 with nf = 2 *)
Lemma st_f2 : forall m (ra a2 a4 a5 t4 t5 t6 : word) (j0 : list byte) s1 l1 s2 l2,
  munch [(sp, sp + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa PP ->
  rw_cells rsegs m sp [CB 16 j0] -> rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] ->
  rw_cells rsegs m (sp + 24) [C8 (Z_to_bv 64 (Z.of_nat l1)); C8 (Z_to_bv 64 (Z.of_nat l2)); C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s1))); C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s2)));
                             C8 (Z_to_bv 64 0)] ->
  fld LN 0 = (s1, l1) -> fld LN (s1 + l1) = (s2, l2) -> (s1 < length LN)%nat -> (s2 + l2 < length LN)%nat ->
  evt rsegs Q (ST 0x12f30 ra (Z_to_bv 64 (Z.of_nat i + Z.of_nat (s2 + l2))) (Z_to_bv 64 (Z.b2z (nulb LN))) a2 (Z_to_bv 64 2)
                 a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a2 a4 a5 t4 t5 t6 j0 s1 l1 s2 l2 MU WM MI BT BP C0 CK CL CS E1 E2 S1 S2.
  pose proof LN_len as LL. pose proof rate_rng as RR.
  pose proof (bytes_sub m tx T i len BT HIL) as BL.
  step. step.
  eapply (sep_loop m LN (Z.of_nat i) (s2 + l2) (length LN - (s2 + l2) - 1) 0);
    [ exact BL | lia | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | | ].
  - intros a0' a3' a4' HE. apply cont_found; [|inv_tac].
    apply (upd_l3 P rate LN found s1 l1 s2 l2 (length LN)); [lia | exact E1 | exact E2 |].
    apply fld_sep_end. exact HE.
  - intros a4' HS. remember (s2 + l2 + sep_run (skipn (s2 + l2) LN))%nat as s3 eqn:ES3.
    step. step. step. step. step. rewrite ltu_u by lia.
    replace (Z.of_nat i + Z.of_nat s3 <? Z.of_nat (i + len)) with true by zb_true. cbn [negb]; cbv iota.
    step.
    eapply (tok_loop _ LN (Z.of_nat i) s3 (length LN - s3 - 1) 0);
      [ exact BL | lia | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | lia | ].
    intros a5' w Hw. subst w. remember (tok_run (skipn s3 LN)) as l3 eqn:EL3.
    assert (E3 : fld LN (s2 + l2) = (s3, l3)) by (rewrite fld_eq, <- ES3, <- EL3; reflexivity).
    pose proof (fld_bound LN (s2 + l2) ltac:(lia)) as B3. rewrite E3 in B3. cbn [fst snd] in B3.
    step.
    rewrite (unsigned_lit (Z.of_nat i + Z.of_nat (s3 + l3))) by lia. rewrite (unsigned_lit (Z.of_nat i + Z.of_nat s3)) by lia.
    replace (Z.of_nat i + Z.of_nat (s3 + l3) - (Z.of_nat i + Z.of_nat s3)) with (Z.of_nat l3) by lia.
    step. step. step. rewrite ltu_u by lia.
    destruct (Z.ltb_spec (Z.of_nat i + Z.of_nat (s3 + l3)) (Z.of_nat (i + len))); cbn [negb]; cbv iota.
    + step. step. setc false; [|vm_compute; reflexivity].
      eapply st_checks; try eassumption.
    + eapply st_checks; try eassumption.
Qed.

(* the second field, from 0x12f30 with nf = 1 *)
Lemma st_f1 : forall m (ra a2 a4 a5 t4 t5 t6 : word) (j0 : list byte) s1 l1,
  munch [(sp, sp + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa PP ->
  rw_cells rsegs m sp [CB 16 j0] -> rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] ->
  rw_cells rsegs m (sp + 24) [C8 (Z_to_bv 64 (Z.of_nat l1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 (tx + (Z.of_nat i + Z.of_nat s1))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  fld LN 0 = (s1, l1) -> (s1 < length LN)%nat -> (s1 + l1 < length LN)%nat ->
  evt rsegs Q (ST 0x12f30 ra (Z_to_bv 64 (Z.of_nat i + Z.of_nat (s1 + l1))) (Z_to_bv 64 (Z.b2z (nulb LN))) a2 (Z_to_bv 64 1)
                 a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a2 a4 a5 t4 t5 t6 j0 s1 l1 MU WM MI BT BP C0 CK CL CS E1 S1 S2.
  pose proof LN_len as LL. pose proof rate_rng as RR.
  pose proof (bytes_sub m tx T i len BT HIL) as BL.
  step. step.
  eapply (sep_loop m LN (Z.of_nat i) (s1 + l1) (length LN - (s1 + l1) - 1) 0);
    [ exact BL | lia | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | | ].
  - intros a0' a3' a4' HE. apply cont_found; [|inv_tac].
    apply (upd_l2 P rate LN found s1 l1 (length LN)); [exact E1 |].
    apply fld_sep_end. exact HE.
  - intros a4' HS. remember (s1 + l1 + sep_run (skipn (s1 + l1) LN))%nat as s2 eqn:ES2.
    step. step. step. step. step. rewrite ltu_u by lia.
    replace (Z.of_nat i + Z.of_nat s2 <? Z.of_nat (i + len)) with true by zb_true. cbn [negb]; cbv iota.
    step.
    eapply (tok_loop _ LN (Z.of_nat i) s2 (length LN - s2 - 1) 0);
      [ exact BL | lia | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | lia | ].
    intros a5' w Hw. subst w. remember (tok_run (skipn s2 LN)) as l2 eqn:EL2.
    assert (E2 : fld LN (s1 + l1) = (s2, l2)) by (rewrite fld_eq, <- ES2, <- EL2; reflexivity).
    pose proof (fld_bound LN (s1 + l1) ltac:(lia)) as B2. rewrite E2 in B2. cbn [fst snd] in B2.
    step.
    rewrite (unsigned_lit (Z.of_nat i + Z.of_nat (s2 + l2))) by lia. rewrite (unsigned_lit (Z.of_nat i + Z.of_nat s2)) by lia.
    replace (Z.of_nat i + Z.of_nat (s2 + l2) - (Z.of_nat i + Z.of_nat s2)) with (Z.of_nat l2) by lia.
    step. step. step. rewrite ltu_u by lia.
    destruct (Z.ltb_spec (Z.of_nat i + Z.of_nat (s2 + l2)) (Z.of_nat (i + len))); cbn [negb]; cbv iota.
    + step. step. setc true; [|vm_compute; reflexivity].
      replace (Z.of_nat i + Z.of_nat (s2 + l2)) with (Z.of_nat i + Z.of_nat (s2 + l2)) by reflexivity.
      eapply st_f2; try eassumption; lia.
    + (* the line ends inside the second field: no third field *)
      assert (U : upd P rate LN found = found).
      { apply (upd_l3 P rate LN found s1 l1 s2 l2 (s2 + l2)); [lia | exact E1 | exact E2 | apply fld_end; lia]. }
      step. rewrite nul_cond. destruct (nulb LN); cbv iota.
      * apply cont_found; [exact U | inv_tac].
      * step. setc true; [|vm_compute; reflexivity]. apply cont_found; [exact U | inv_tac].
Qed.

(* the first field, from 0x12f2c (nf = 0) *)
Lemma st_f0 : forall m (ra a2 a3 a4 a5 t4 t5 t6 : word) (j0 : list byte),
  munch [(sp, sp + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa PP ->
  rw_cells rsegs m sp [CB 16 j0] -> rw_cells rsegs m (sp + 16) [C8 (Z_to_bv 64 (Z.of_nat (length P)))] ->
  rw_cells rsegs m (sp + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  (0 < len)%nat ->
  evt rsegs Q (ST 0x12f2c ra (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.b2z (nulb LN))) a2 a3 a4 a5
                 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a2 a3 a4 a5 t4 t5 t6 j0 MU WM MI BT BP C0 CK CL CS L0.
  pose proof LN_len as LL. pose proof rate_rng as RR.
  pose proof (bytes_sub m tx T i len BT HIL) as BL.
  step. step. step.
  eapply (sep_loop m LN (Z.of_nat i) 0 (length LN - 1) 0);
    [ exact BL | lia | lia | lia | reflexivity | lia | lia | | ].
  - intros a0' a3' a4' HE. apply cont_found; [|inv_tac].
    apply (upd_l1 P rate LN found (length LN)).
    apply fld_sep_end. exact HE.
  - intros a4' HS. remember (0 + sep_run (skipn 0 LN))%nat as s1 eqn:ES1.
    step. step. step. step. step. rewrite ltu_u by lia.
    replace (Z.of_nat i + Z.of_nat s1 <? Z.of_nat (i + len)) with true by zb_true. cbn [negb]; cbv iota.
    step.
    eapply (tok_loop _ LN (Z.of_nat i) s1 (length LN - s1 - 1) 0);
      [ exact BL | lia | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | lia | ].
    intros a5' w Hw. subst w. remember (tok_run (skipn s1 LN)) as l1 eqn:EL1.
    assert (E1 : fld LN 0 = (s1, l1)) by (rewrite fld_eq, <- ES1, <- EL1; reflexivity).
    pose proof (fld_bound LN 0 ltac:(lia)) as B1. rewrite E1 in B1. cbn [fst snd] in B1.
    step.
    rewrite (unsigned_lit (Z.of_nat i + Z.of_nat (s1 + l1))) by lia. rewrite (unsigned_lit (Z.of_nat i + Z.of_nat s1)) by lia.
    replace (Z.of_nat i + Z.of_nat (s1 + l1) - (Z.of_nat i + Z.of_nat s1)) with (Z.of_nat l1) by lia.
    step. step. step. rewrite ltu_u by lia.
    destruct (Z.ltb_spec (Z.of_nat i + Z.of_nat (s1 + l1)) (Z.of_nat (i + len))); cbn [negb]; cbv iota.
    + step. step. setc true; [|vm_compute; reflexivity].
      eapply st_f1; try eassumption; lia.
    + (* the line ends inside the first field: no second field *)
      assert (U : upd P rate LN found = found).
      { apply (upd_l2 P rate LN found s1 l1 (s1 + l1)); [exact E1 | apply fld_end; lia]. }
      step. rewrite nul_cond. destruct (nulb LN); cbv iota.
      * apply cont_found; [exact U | inv_tac].
      * step. setc true; [|vm_compute; reflexivity]. apply cont_found; [exact U | inv_tac].
Qed.

(* a line, from 0x12ef0 (its end found): fs/fl cleared, the NUL scan, the fields *)
Lemma st_line : forall m (ra a1 a2 a3 a4 a5 t4 t5 t6 : word),
  Inv m ->
  evt rsegs Q (ST 0x12ef0 ra (Z_to_bv 64 (Z.of_nat i)) a1 a2 a3 a4 a5 (Z_to_bv 64 EE) (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m ra a1 a2 a3 a4 a5 t4 t5 t6 INV.
  destruct INV as (MU & WM & MI & BT & BP & [j0 C0] & CK & [j1 CL] & [j2 CS]).
  pose proof LN_len as LL. pose proof rate_rng as RR.
  pose proof (rw_cells_bound rsegs _ _ _ CS) as BS. cbn [cells_size csize Nat.add] in BS.
  do 6 step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat (i + len))); cbn [negb]; cbv iota.
  - pose proof (bytes_sub _ tx T i len BT HIL) as BL.
    step. step. step.
    eapply (nul_loop _ LN (Z.of_nat i) (len - 1) 0);
      [ exact BL | lia | lia | lia | reflexivity | lia | lia | ].
    intros a2' a3' a4' w1 Hw1. subst w1.
    eapply st_f0; try eassumption; lia.
  - apply cont_found; [|inv_tac].
    apply (upd_l1 P rate LN found 0). apply fld_end. lia.
Qed.

End Line.

(** ** The line loop of fuzz_lock.c:84-116, from 0x12ec4 (i < n) *)

Lemma body : forall m (i : nat) (found : Z) (ra a1 a2 a3 a4 a5 t4 t5 t6 s2 : word),
  (i < length T)%nat -> Inv m ->
  Kont (Z.of_nat (i + line_len (skipn i T))) (upd P rate (firstn (line_len (skipn i T)) (skipn i T)) found) ->
  evt rsegs Q (ST 0x12ec4 ra (Z_to_bv 64 (Z.of_nat i)) a1 a2 a3 a4 a5 s2 (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros m i found ra a1 a2 a3 a4 a5 t4 t5 t6 s2 Hi INV KB.
  pose proof (line_len_le (skipn i T)) as LL. rewrite length_skipn in LL.
  pose proof INV as (_ & _ & _ & BT & _).
  step. step. step. rewrite ltu_u by lia.
  assert (EOL : forall a1v : Z, a1v = Z.of_nat (length T) ->
            evt rsegs Q (ST 0x12ed4 ra (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 a1v) (Z_to_bv 64 (Z.of_nat i + 1)) a3 a4 a5 s2
                           (Z_to_bv 64 found) t4 t5 t6 m)).
  { intros a1v ->. step.
    eapply (eol_loop m i (length (skipn i T) - 1) 0); [exact BT | rewrite length_skipn; lia | reflexivity | lia |].
    intros a2'. apply (st_line i (line_len (skipn i T)) found); [lia | exact KB | exact INV]. }
  destruct (Z.ltb_spec (Z.of_nat i + 1) (Z.of_nat (length T))); cbv iota.
  - apply EOL. reflexivity.
  - step. apply EOL. lia.
Qed.

Lemma outer : forall (W : Z),
  (forall (ra a0 a1 a2 a3 a4 a5 t4 t5 t6 s2 : word) (m : word -> option byte), Inv m ->
     evt rsegs Q (ST 0x130d0 ra a0 a1 a2 a3 a4 a5 s2 (Z_to_bv 64 W) t4 t5 t6 m)) ->
  forall fuel (i : nat) found m (ra a1 a2 a3 a4 a5 t4 t5 t6 s2 : word),
  (i < length T)%nat -> (length T - i <= fuel)%nat -> Inv m ->
  W = lk (length (skipn i T)) P rate (skipn i T) found ->
  evt rsegs Q (ST 0x12ec4 ra (Z_to_bv 64 (Z.of_nat i)) a1 a2 a3 a4 a5 s2 (Z_to_bv 64 found) t4 t5 t6 m).
Proof.
  intros W KF fuel. induction fuel as [|fuel IH]; intros i found m ra a1 a2 a3 a4 a5 t4 t5 t6 s2 Hi Hf INV HW; [lia|].
  apply body; [exact Hi | exact INV |].
  intros ra' a0' a1' a2' a3' a4' a5' t4' t5' t6' m' INV'.
  set (t := skipn i T) in *. set (len := line_len t) in *.
  assert (Ht : t <> []) by (subst t; intros E; pose proof (length_skipn i T) as L; rewrite E in L; cbn in L; lia).
  assert (Lt : length t = (length T - i)%nat) by (subst t; apply length_skipn).
  pose proof (line_len_le t) as LL. fold len in LL.
  step. step. rewrite ltu_u by lia.
  destruct (find_byte 10 t) as [j|] eqn:FB.
  - assert (Ej : len = j) by (subst len; unfold line_len; rewrite FB; reflexivity).
    pose proof (find_byte_Some 10 t j FB) as (Jl & _).
    rewrite (lk_line_lf P rate t found j FB) in HW. fold len in HW.
    destruct (Z.ltb_spec (Z.of_nat (i + len) + 1) (Z.of_nat (length T))); cbv iota.
    + replace (Z.of_nat (i + len) + 1) with (Z.of_nat (S (i + len))) by lia.
      apply (IH (S (i + len))); [lia | lia | exact INV' |].
      rewrite HW. subst t. rewrite skipn_skipn. replace (S j + i)%nat with (S (i + len)) by lia. reflexivity.
    + step. replace (upd P rate (firstn len t) found) with W; [apply KF; exact INV'|].
      rewrite HW. replace (skipn (S j) t) with (@nil byte); [apply lk_nil|].
      symmetry. apply skipn_all2. lia.
  - assert (Ej : len = length t) by (subst len; unfold line_len; rewrite FB; reflexivity).
    rewrite (lk_line_end P rate t found Ht FB) in HW. fold len in HW.
    replace (Z.of_nat (i + len) + 1 <? Z.of_nat (length T)) with false by zb_false. cbv iota.
    step. rewrite <- HW. apply KF. exact INV'.
Qed.

End Walk.

(** * The frame and the entry, 0x12e28-0x12ec4. *)

Lemma wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros j Hj. apply H. lia.
  - split; [lia|]. split; [lia|]. intros j Hj. replace (A + n1 + j) with (A + (n1 + j)) by lia. apply H. lia.
Qed.

Lemma wr_join : forall m A n1 n2, wr_at rsegs m A n1 -> wr_at rsegs m (A + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2).
Proof.
  intros m A n1 n2 (H1 & H2 & H) (G1 & G2 & G) P1 P2. split; [lia|]. split; [lia|].
  intros j Hj. destruct (Z.ltb_spec0 j n1); [apply H; lia|].
  replace (A + j) with (A + n1 + (j - n1)) by lia. apply G. lia.
Qed.

Lemma rw_split : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] Hw] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma rw_app : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] V1] [[W2 B2] V2] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply wr_join; [exact V1 | exact V2 | lia | lia].
Qed.

(* the scratch slots after [sd s2, 0x10(sp)] at 0x12e5c, as the line loop holds them *)
Lemma frame_split : forall m sp a v b,
  rw_cells rsegs m sp [CB 16 a; C8 v; CB 48 b] ->
  rw_cells rsegs m sp [CB 16 a] /\ rw_cells rsegs m (sp + 16) [C8 v] /\
  (exists j1, rw_cells rsegs m (sp + 24) [CB 24 j1]) /\ (exists j2, rw_cells rsegs m (sp + 48) [CB 24 j2]).
Proof.
  intros m sp a v b H.
  destruct (rw_split m sp (sp + 16) [CB 16 a] [C8 v; CB 48 b] H ltac:(reflexivity)) as [H0 H1].
  destruct (rw_split m (sp + 16) (sp + 24) [C8 v] [CB 48 b] H1 ltac:(cbn; lia)) as [H2 H3].
  apply (rw_cells_split_CB rsegs m (sp + 24) [] 48 b [] [24; 24]%nat) in H3; [|reflexivity].
  cbn [app mk_CB_cells] in H3.
  destruct (rw_split m (sp + 24) (sp + 48) [CB 24 (firstn 24 b)] [CB 24 (firstn 24 (skipn 24 b))] H3 ltac:(cbn; lia))
    as [H4 H5].
  split; [exact H0|]. split; [exact H2|]. split; eexists; eassumption.
Qed.

Lemma frame_join : forall m sp j0 v j1 j2,
  rw_cells rsegs m sp [CB 16 j0] -> rw_cells rsegs m (sp + 16) [C8 v] ->
  rw_cells rsegs m (sp + 24) [CB 24 j1] -> rw_cells rsegs m (sp + 48) [CB 24 j2] ->
  exists J', rw_cells rsegs m sp [CB 72 J'].
Proof.
  intros m sp j0 v j1 j2 H0 H1 H2 H3.
  pose proof (rw_app m (sp + 24) (sp + 48) [CB 24 j1] [CB 24 j2] H2 H3 ltac:(cbn; lia)) as A.
  pose proof (rw_app m (sp + 16) (sp + 24) [C8 v] _ H1 A ltac:(cbn; lia)) as B.
  pose proof (rw_app m sp (sp + 16) [CB 16 j0] _ H0 B ltac:(cbn; lia)) as C.
  destruct (rw_cells_forget rsegs m sp _ C) as [J' HJ]. cbn [app cells_size csize Nat.add] in HJ.
  exists J'. exact HJ.
Qed.

(* the size test of fuzz_lock.c:81 at 0x12e50-0x12e58 *)
Lemma size_cond : forall n, 0 <= n < 2^64 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (n + -1))) 16)) (Z_to_bv 64 0)) =
  negb ((1 <=? n) && (n <=? 65536)).
Proof.
  intros n Hn. rewrite unsigned_lit_wrap.
  assert (R : 0 <= Z.shiftr ((n + -1) mod 2^64) 16 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (n + -1) (2^64) ltac:(lia)) as M.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite eqb_u by lia. replace (n + -1) with (n - 1) by lia. rewrite size_test by lia. reflexivity.
Qed.

Lemma size_zero : forall n, 1 <= n <= 65536 -> Z.shiftr (bv_unsigned (Z_to_bv 64 (n + -1))) 16 = Z.of_nat 0.
Proof.
  intros n Hn. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.

(* closed register values (the standard period and its 5%, fuzz_lock.c:60 and :113) to literals *)
Ltac norm_closed :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
      lazymatch e with
      | Zpos _ => fail | Zneg _ => fail | Z0 => fail
      | _ => let v := eval vm_compute in e in
             lazymatch v with Zpos _ => change e with v | Zneg _ => change e with v | Z0 => change e with v end
      end
  end.

Definition EXP_IN : Z := 0x12e28.
Definition EXP_OUT : Z := 0x130d0.

(** check_lookup's reading of the lock, [expected] (fuzz_lock.c:147, the body of fuzz_lock.c:78-118 inlined):
    from 0x12e28, just after [jal rp_lock_lookup] returned got in a0, to 0x130d0 ([bne s6, s7]), where s6 = got and
    s7 = want = lock_lookup T P rate. sp is check_lookup's frame (sp at entry - 0xb0); the walk writes only its
    scratch slots [sp, sp + 0x48): the spills of t3/t2 at 0/8, k at 0x10, fl[3] at 0x18, fs[3] at 0x30. *)
Theorem check_lookup_exp_holds : bcmp_contract ->
  forall (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (sp tx pa rate : Z) (T P SL J : list byte) (Q : machine_state -> Prop),
    (* the harness fact this walk uses (fuzz_lock.c:188-200): the port name has k = data[1] % 16 <= 15 bytes *)
    forall (HARN_k : (length P <= 15)%nat)
    (* register and memory shape at 0x12e28 *)
           (W_rate : 0 <= rate < 2^64)
           (W_tx : 0 <= tx) (W_txn : tx + Z.of_nat (length T) < 2^64) (M_text : bytes_at rsegs m tx T)
           (W_pa : 0 <= pa) (M_port : bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL))
           (M_frame : rw_cells rsegs m sp [CB 72 J])
           (D_text : tx + Z.of_nat (length T) <= sp \/ sp + 72 <= tx)
           (D_port : pa + Z.of_nat (length P + 1 + length SL) <= sp \/ sp + 72 <= pa)
           (M_inv : mem_inv rsegs m),
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s8' s9' s10' s11' t3' t4' t5' t6' : word)
            (m' : word -> option byte) (J' : list byte),
       munch [(sp, sp + 72)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> rw_cells rsegs m' sp [CB 72 J'] ->
       evt rsegs Q (MS (mkR ra' (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 (Z_to_bv 64 rate) a0' a1' a2' a3' a4' a5' a6' a7'
                            s2' (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx) a0
                            (Z_to_bv 64 (lock_lookup T P rate)) s8' s9' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 EXP_OUT) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate) a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T)))
                         (Z_to_bv 64 tx) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 EXP_IN) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp tx pa rate T P SL J Q
    HK HRATE HTX HTE BT HPA BP FR DT DP MI K.
  unfold EXP_IN. unfold EXP_OUT in K.
  pose proof (rw_cells_bound rsegs m sp [CB 72 J] FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_len m pa _ BP) as PB.
  pose proof (length_app P (Z_to_bv 8 0 :: SL)) as HPL. cbn [length] in HPL.
  (* want = 0: 0x130cc, s7 := 0 *)
  assert (EXIT0 : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s8' s9' s10' s11' t3' t4' t5' t6' : word),
            lock_lookup T P rate = 0 ->
            evt rsegs Q (MS (mkR ra' (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 (Z_to_bv 64 rate) a0' a1' a2' a3' a4' a5' a6' a7'
                                 s2' (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx) a0 (Z_to_bv 64 0)
                                 s8' s9' s10' s11' t3' t4' t5' t6') F (Z_to_bv 64 0x130d0) fc None m (seg_rom rsegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s8' s9' s10' s11' t3' t4' t5' t6' H0.
    pose proof (K ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s8' s9' s10' s11' t3' t4' t5' t6' m J
                  (munch_refl _ m) (wmono_refl rsegs m) MI FR) as KK.
    rewrite H0 in KK. exact KK. }
  (* the rate's standard period (fuzz_lock.c:80-82), then the line loop *)
  assert (COMMON : forall (r lo hi : Z) (a0' a1' a2' a3' a4' a5' s7' : word), r = rate ->
            (r = 44100 /\ lo = 258504 /\ hi = 285714) \/ (r = 48000 /\ lo = 237500 /\ hi = 262500) \/
            (r = 96000 /\ lo = 118750 /\ hi = 131250) ->
            evt rsegs Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 r) a0' a1' a2' a3' a4' a5' a6 a7
                                 (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T)))
                                 (Z_to_bv 64 tx) a0 s7' s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x12e50) fc None m (seg_rom rsegs))).
  { intros r lo hi a0' a1' a2' a3' a4' a5' s7' Er RV.
    pose proof (munch_refl [(sp, sp + 72)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. step. step. rewrite (size_cond (Z.of_nat (length T))) by lia.
    destruct ((1 <=? Z.of_nat (length T)) && (Z.of_nat (length T) <=? 65536)) eqn:SZ; cbn [negb]; cbv iota.
    2: { step. subst r. apply EXIT0. apply lock_lookup_0. right.
         apply andb_false_iff in SZ. destruct SZ as [S|S]; apply Z.leb_gt in S; [right | left; lia].
         destruct T; [reflexivity | cbn in S; lia]. }
    apply andb_true_iff in SZ as [SZ1 SZ2]. apply Z.leb_le in SZ1, SZ2.
    step. do 25 step.
    rewrite (size_zero (Z.of_nat (length T))) by lia.
    destruct RV as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]; norm_closed.
    all: lazymatch goal with H : rw_cells rsegs ?mm ?A [CB 16 _; C8 _; CB 48 _] |- _ =>
           destruct (frame_split mm A _ _ _ H) as (C0 & CK & [j1 C1] & [j2 C2]); clear H end.
    all: eapply outer with (got := a0) (m0 := m) (T := T) (P := P) (SL := SL) (W := lock_lookup T P rate)
                           (fuel := length T) (i := 0%nat) (found := 0).
    all: lazymatch goal with
         | |- forall _, _ =>
             intros xra xa0 xa1 xa2 xa3 xa4 xa5 xt4 xt5 xt6 xs2 m' INV;
             destruct INV as (MU' & WM' & MI' & _ & _ & [j0' C0'] & CK' & [j1' C1'] & [j2' C2']);
             destruct (frame_join m' sp _ _ _ _ C0' CK' C1' C2') as [J' FJ];
             subst rate; apply K with (J' := J'); assumption
         | |- context [Inv] => eapply inv_intro; first [eassumption | reflexivity]
         | |- lock_lookup _ _ _ = lk _ _ _ _ _ =>
             change (skipn 0 T) with T; subst rate; apply lock_lookup_lk; [vm_compute; discriminate | lia]
         | |- std_period _ <> 0 => vm_compute; discriminate
         | |- bcmp_contract => exact BC
         | |- _ = _ => vm_compute; reflexivity
         | _ => first [assumption | lia]
         end. }
  step. step. step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec rate 44100) as [R1|R1]; cbv iota.
  { eapply COMMON; [reflexivity | left; repeat split; exact R1]. }
  step. step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec rate 96000) as [R2|R2]; cbv iota.
  { eapply COMMON; [reflexivity | right; right; repeat split; exact R2]. }
  step. step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec rate 48000) as [R3|R3]; cbn [negb]; cbv iota.
  { eapply COMMON; [reflexivity | right; left; repeat split; exact R3]. }
  step. apply EXIT0. apply lock_lookup_0. left. unfold std_period.
  rewrite (proj2 (Z.eqb_neq _ _) R1), (proj2 (Z.eqb_neq _ _) R2), (proj2 (Z.eqb_neq _ _) R3). reflexivity.
Qed.
