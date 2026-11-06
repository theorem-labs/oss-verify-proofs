(* Walk of the harness's own reading of the lock in check_lookup ([expected] of fuzz_lock.c:78-118,
   inlined at fuzz_lock.c:147) in fuzz_lock.ubsan: from 0x12ebc, the instruction after
   [jal rp_lock_lookup], to 0x1317c, the [bne s6, s8] that compares got with want.
   number() is not inlined and is called twice (0x13100, 0x13118); bcmp once (0x130b8).

   The UBSan trap [unimp] at 0x131c8 is reached from eight branches and none is taken:
   - 0x12f94 [bltu s9, s11], 0x12fd4 [bltu s9, a2], 0x12ffc [bltu s9, a3], 0x1303c [bltu s9, a0],
     0x13064 [bltu s9, a0]: s9 = ~t, so each is "t + index overflows"; the index is at most n
     and t + n < 2^64 (HTE);
   - 0x1308c [beqz a0], a0 = fs[0] = t + j: 0 < t (HTX) and t + j < 2^64;
   - 0x130f4 [bnez a0], a0 = the spill of a6 = seqz(&fs[1]) | seqz(&fl[1]): sp + 88 and sp + 64
     are not 0 (0 <= sp, sp + 104 <= 2^64);
   - 0x1310c [bnez a0], a0 = the spill of t3 = xori(sltu(&fs[0], -16) & sltu(&fl[0], -16), 1):
     sp + 80 and sp + 56 are below 2^64 - 16 (sp + 104 <= 2^64).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec LockSpecExp.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import bcmp_c number_c field.
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

Lemma flatCB : forall m A cs n, rw_cells rsegs m A cs -> cells_size cs = n -> exists J, rw_cells rsegs m A [CB n J].
Proof.
  intros m A cs n H <-. exists (cells_bytes cs).
  pose proof (rw_cells_merge rsegs m A [] cs []) as M. cbn [app] in M. rewrite app_nil_r in M.
  apply M. exact H.
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

(* the 5% band test of fuzz_lock.c:113 at 0x1313c-0x13158 *)
Lemma band_cond : forall per lo hi, -2^63 <= per < 2^63 -> -2^63 <= lo < 2^63 -> -2^63 <= hi < 2^63 ->
  negb (bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (v_slt (Z_to_bv 64 per) (Z_to_bv 64 lo)))
                                  (bv_unsigned (v_slt (Z_to_bv 64 hi) (Z_to_bv 64 per)))))
               (Z_to_bv 64 0)) = (per <? lo) || (hi <? per).
Proof.
  intros per lo hi H1 H2 H3. rewrite !slt_lit by lia.
  destruct (per <? lo), (hi <? per); vm_compute; reflexivity.
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

(* s9 = not(t): the UBSan "t + index does not wrap" register *)
Lemma not64 : forall t, 0 <= t < 2^64 -> Z.lxor (bv_unsigned (Z_to_bv 64 t)) 18446744073709551615 = 2^64 - 1 - t.
Proof.
  intros t Ht. rewrite unsigned_lit by lia. rewrite lnot_mod64 by lia.
  replace (Z.lnot t) with ((2^64 - 1 - t) + (-1) * 2^64) by (unfold Z.lnot; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* seqz of a frame address: it is not 0 *)
Lemma sltiu1_nz : forall z, 0 < z < 2^64 -> bv_unsigned (v_sltiu (Z_to_bv 64 z) 1) = 0.
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit by lia.
  change (bv_wrap 64 1) with 1. replace (z <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* sltu of a frame address against -16: it is below 2^64 - 16 *)
Lemma sltiu_m16 : forall z, 0 <= z < 2^64 - 16 -> bv_unsigned (v_sltiu (Z_to_bv 64 z) (-16)) = 1.
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit by lia.
  change (bv_wrap 64 (-16)) with (2^64 - 16). replace (z <? 2^64 - 16) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** * Bytes and lists. *)

Lemma nth_firstn : forall {X} (l : list X) n j, (j < n)%nat -> nth_error (firstn n l) j = nth_error l j.
Proof.
  intros X l; induction l as [|x l IH]; intros [|n] [|j] H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_skipn : forall {X} (l : list X) i j, nth_error (skipn i l) j = nth_error l (i + j).
Proof.
  intros X l i; revert l; induction i as [|i IH]; intros l j; [reflexivity|].
  destruct l as [|x l]; [destruct j; reflexivity|]. cbn. apply IH.
Qed.

Lemma byte_at' : forall {X} (l : list X) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros X l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia. Qed.

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

Lemma firstn_snoc : forall {X} (l : list X) o b, nth_error l o = Some b -> firstn (S o) l = firstn o l ++ [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|o] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - f_equal. apply IH. exact N.
Qed.

(* a window of T, read at absolute offsets *)
Lemma win_nth : forall (T : list byte) (i n x : nat), (x < n)%nat ->
  nth_error (firstn n (skipn i T)) x = nth_error T (i + x).
Proof. intros T i n x H. rewrite nth_firstn by lia. apply nth_skipn. Qed.

Lemma win_slice : forall (T : list byte) (i n o len : nat), (o + len <= n)%nat ->
  slice (firstn n (skipn i T)) o len = firstn len (skipn (i + o) T).
Proof.
  intros T i n o len H. unfold slice.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Init.Nat.min len (n - o)) with len by lia. f_equal. f_equal. lia.
Qed.

Lemma win_len : forall (T : list byte) (i n : nat), (i + n <= length T)%nat ->
  length (firstn n (skipn i T)) = n.
Proof. intros T i n H. rewrite length_firstn, length_skipn. lia. Qed.

(** * The walk. *)

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac brf := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
Ltac brt := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
Ltac zb_true := symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; lia.
Ltac zb_false := symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; lia.
Ltac stp := step; try unfold zxb.

(* the first byte after a separator run, when the run stops inside the line, is not a separator *)
Lemma sep_run_stop : forall l, (sep_run l < length l)%nat -> (1 <= tok_run (skipn (sep_run l) l))%nat.
Proof.
  induction l as [|b r IH]; cbn [sep_run length]; intros H; [lia|].
  destruct (is_sep (bz b)) eqn:SB; cbn [skipn tok_run].
  - apply IH. lia.
  - rewrite SB. lia.
Qed.

Lemma sep_run_stop' : forall l o, (o + sep_run (skipn o l) < length l)%nat ->
  (1 <= tok_run (skipn (o + sep_run (skipn o l)) l))%nat.
Proof.
  intros l o H. pose proof (sep_run_stop (skipn o l)) as HS.
  rewrite length_skipn in HS. rewrite skipn_skipn in HS.
  replace (sep_run (skipn o l) + o)%nat with (o + sep_run (skipn o l))%nat in HS by lia.
  apply HS. lia.
Qed.

Section W.
Variables (gp tp s0 got : word) (F : bvmap 5 word) (fc : bv 32).
Variables (sp tx pa rate k nt lo hi : Z) (T P : list byte) (Q : machine_state -> Prop).
Variable (m0 : word -> option byte).

Local Notation N := (Z.of_nat (length T)).

Hypothesis HSP : 0 <= sp.
Hypothesis HSPE : sp + 104 <= 2^64.
Hypothesis HTX : 0 < tx.
Hypothesis HTE : tx + N < 2^64.
Hypothesis HNT : nt = 2^64 - 1 - tx.
Hypothesis BCC : bcmp_contract.
Hypothesis NCC : number_contract.
Hypothesis HRR : 0 <= rate < 2^63.
Hypothesis HK : k = Z.of_nat (length P).
Hypothesis HKL : (length P <= 15)%nat.
Hypothesis HLO : lo = std_period rate - std_period rate / 20.
Hypothesis HHI : hi = std_period rate + std_period rate / 20.
Hypothesis HPA : 0 < pa.
Hypothesis HPE : pa + Z.of_nat (length P) <= 2^64.
Hypothesis DTS : tx + N <= sp \/ sp + 104 <= tx.
Hypothesis DPS : pa + Z.of_nat (length P) <= sp \/ sp + 104 <= pa.

(* the line loop's registers; a6 = 0 and t3 = 0 are the two UBSan flags the prologue computes.
   [ra] is a parameter: the three calls overwrite it, and check_lookup's own return address
   was saved to the frame by the prologue, before this segment. *)
Local Notation ST pc ra a0 a1 a2 a3 a4 a5 s8 s11 m :=
  (MS (mkR ra (Z_to_bv 64 sp) gp tp (Z_to_bv 64 (sp + 56)) (Z_to_bv 64 1) (Z_to_bv 64 2) s0 (Z_to_bv 64 rate)
           a0 a1 a2 a3 a4 a5 (Z_to_bv 64 0) (Z_to_bv 64 (sp + 80))
           (Z_to_bv 64 32) (Z_to_bv 64 pa) (Z_to_bv 64 N) (Z_to_bv 64 tx) got (Z_to_bv 64 10)
           s8 (Z_to_bv 64 nt) (Z_to_bv 64 4294976000) s11
           (Z_to_bv 64 0) (Z_to_bv 64 lo) (Z_to_bv 64 hi) (Z_to_bv 64 35))
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* the LF scan of fuzz_lock.c:86-87, at 0x12f94: s11 runs from the line start i to the LF, else to n.
   0x12f94 [bltu s9, s11] is the UBSan trap branch; s11 <= n and t + n < 2^64 refute it. *)
Lemma eol_loop : forall m (i : nat) kk (o : nat) (ra a0 a2 a3 a4 a5 s8 : word) (v11 : Z),
  bytes_at rsegs m tx T ->
  (i + o + S kk = length T)%nat -> find_byte 10 (firstn o (skipn i T)) = None ->
  v11 = Z.of_nat (i + o) ->
  (forall a2' : word,
     evt rsegs Q (ST 0x12fb0 ra a0 (Z_to_bv 64 N) a2' a3 a4 a5 s8
                    (Z_to_bv 64 (Z.of_nat (i + line_len (skipn i T)))) m)) ->
  evt rsegs Q (ST 0x12f94 ra a0 (Z_to_bv 64 N) a2 a3 a4 a5 s8 (Z_to_bv 64 v11) m).
Proof.
  intros m i kk. induction kk as [|kk IH]; intros o ra a0 a2 a3 a4 a5 s8 v11 BT Hk HF -> K.
  all: destruct (byte_at' (skipn i T) o ltac:(rewrite length_skipn; lia)) as [b Nb].
  all: pose proof Nb as NbT; rewrite nth_skipn in NbT.
  all: pose proof (rd_at m tx T (i + o) b BT NbT) as R.
  all: pose proof (byte_range b) as Rb.
  all: step; brf.
  all: step; stp; step.
  all: rewrite eqb_u by lia.
  all: destruct (Z.eqb_spec (bv_unsigned b) 10) as [E|E]; cbv iota.
  1, 3: (replace (line_len (skipn i T)) with o in K; [apply K|];
         unfold line_len; rewrite (find_byte_at 10 (skipn i T) o b HF Nb E); reflexivity).
  - step. step. rewrite eqb_u by lia.
    replace (N =? Z.of_nat (i + o) + 1) with true by zb_true. cbn [negb]; cbv iota.
    step.
    replace (line_len (skipn i T)) with (length (skipn i T)) in K;
      [rewrite length_skipn in K; replace (Z.of_nat (i + (length T - i))) with N in K by lia; apply K|].
    unfold line_len. rewrite (find_byte_all 10 (skipn i T)); [reflexivity|].
    replace (length (skipn i T)) with (S o) by (rewrite length_skipn; lia).
    rewrite (firstn_snoc _ o b Nb). apply find_byte_snoc_none; assumption.
  - step. step. rewrite eqb_u by lia.
    replace (N =? Z.of_nat (i + o) + 1) with false by zb_false. cbn [negb]; cbv iota.
    eapply (IH (S o)); [exact BT | lia | | lia | exact K].
    rewrite (firstn_snoc _ o b Nb). apply find_byte_snoc_none; assumption.
Qed.

(* a byte of the line L, which starts at t + i *)
Lemma rdL : forall m (i : nat) (L : list byte) (x : nat) b, bytes_at rsegs m (tx + Z.of_nat i) L ->
  nth_error L x = Some b -> ov_read_bytes rsegs m (Z_to_bv 64 (tx + Z.of_nat (i + x))) 1 = Some [b].
Proof.
  intros m i L x b BL N. replace (tx + Z.of_nat (i + x)) with (tx + Z.of_nat i + Z.of_nat x) by lia.
  exact (rdb m (tx + Z.of_nat i) L x b BL N).
Qed.

(* the NUL scan of fuzz_lock.c:92-93, at 0x12fd4. 0x12fd4 [bltu s9, a2] is the UBSan trap branch. *)
Lemma nul_loop : forall m (i : nat) (L : list byte) kk (o : nat) (ra a0 a3 a4 a5 s8 : word) (v1 v2 ve : Z),
  bytes_at rsegs m (tx + Z.of_nat i) L -> (o + S kk = length L)%nat ->
  tx + Z.of_nat (i + length L) < 2^64 ->
  v1 = Z.b2z (nulb (firstn o L)) -> v2 = Z.of_nat (i + o) -> ve = Z.of_nat (i + length L) ->
  (forall (a2' a3' : word) (w1 : Z), w1 = Z.b2z (nulb L) ->
     evt rsegs Q (ST 0x12ff0 ra a0 (Z_to_bv 64 w1) a2' a3' a4 a5 s8 (Z_to_bv 64 ve) m)) ->
  evt rsegs Q (ST 0x12fd4 ra a0 (Z_to_bv 64 v1) (Z_to_bv 64 v2) a3 a4 a5 s8 (Z_to_bv 64 ve) m).
Proof.
  intros m i L kk. induction kk as [|kk IH]; intros o ra a0 a3 a4 a5 s8 v1 v2 ve BL Hk He -> -> -> K.
  all: destruct (byte_at' L o ltac:(lia)) as [b Nb].
  all: pose proof (rdL m i L o b BL Nb) as R.
  all: pose proof (byte_range b) as Rb. all: pose proof (b2z_range (nulb (firstn o L))) as Rn.
  all: step; brf.
  all: step; stp; step; step; step; step.
  all: rewrite eqb_u by lia.
  - replace (Z.of_nat (i + length L) =? Z.of_nat (i + o) + 1) with true by zb_true. cbn [negb]; cbv iota.
    apply K. rewrite unsigned_lit by lia. rewrite seqz_byte, lor_b2z, <- nulb_snoc, <- (firstn_snoc _ o b Nb).
    rewrite firstn_all2 by lia. reflexivity.
  - replace (Z.of_nat (i + length L) =? Z.of_nat (i + o) + 1) with false by zb_false. cbn [negb]; cbv iota.
    eapply (IH (S o)); [exact BL | lia | lia | | lia | lia | exact K].
    rewrite unsigned_lit by lia. rewrite seqz_byte, lor_b2z, <- nulb_snoc, <- (firstn_snoc _ o b Nb). reflexivity.
Qed.

(* the separator skip of fuzz_lock.c:95-98, at 0x12ffc. 0x12ffc [bltu s9, a3] is the UBSan trap branch. *)
Lemma sep_loop : forall m (i : nat) (L : list byte) (o : nat) kk (d : nat) (ra a0 a1 a2 a4 a5 s8 : word) (v3 ve : Z),
  bytes_at rsegs m (tx + Z.of_nat i) L -> (o + d + S kk = length L)%nat ->
  tx + Z.of_nat (i + length L) < 2^64 ->
  sep_run (skipn o L) = (d + sep_run (skipn (o + d) L))%nat ->
  v3 = Z.of_nat (i + o + d) -> ve = Z.of_nat (i + length L) ->
  (forall (a0' a3' a4' : word), (o + sep_run (skipn o L) = length L)%nat ->
     evt rsegs Q (ST 0x130e4 ra a0' a1 a2 a3' a4' a5 s8 (Z_to_bv 64 ve) m)) ->
  (forall (a4' : word) (w0 w3 : Z), w0 = tx + Z.of_nat (i + o + sep_run (skipn o L)) ->
     w3 = Z.of_nat (i + o + sep_run (skipn o L)) -> (o + sep_run (skipn o L) < length L)%nat ->
     evt rsegs Q (ST 0x13024 ra (Z_to_bv 64 w0) a1 a2 (Z_to_bv 64 w3) a4' a5 s8 (Z_to_bv 64 ve) m)) ->
  evt rsegs Q (ST 0x12ffc ra a0 a1 a2 (Z_to_bv 64 v3) a4 a5 s8 (Z_to_bv 64 ve) m).
Proof.
  intros m i L o kk. induction kk as [|kk IH]; intros d ra a0 a1 a2 a4 a5 s8 v3 ve BL Hk He Hsr -> -> K1 K2.
  all: destruct (byte_at' L (o + d) ltac:(lia)) as [b Nb].
  all: pose proof (rdL m i L (o + d) b BL Nb) as R.
  all: rewrite (skipn_nth L (o + d) b Nb) in Hsr; cbn [sep_run] in Hsr.
  all: pose proof (byte_range b) as Rb.
  all: replace (tx + Z.of_nat (i + (o + d))) with (tx + Z.of_nat (i + o + d)) in R by lia.
  all: step; brf.
  all: step; stp; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota.
  1, 3: (pose proof (sep_hi b C1) as NS; rewrite NS in Hsr; apply K2; lia).
  all: step; step; step; rewrite (sep_lo b C1).
  all: destruct (is_sep (bz b)) eqn:SB; cbn [negb]; cbv iota.
  2, 4: (apply K2; lia).
  - step. step. rewrite ltu_u by lia.
    replace (Z.of_nat (i + o + d) + 1 <? Z.of_nat (i + length L)) with false by zb_false. cbv iota.
    step. apply K1.
    assert (skipn (S (o + d)) L = []) by (apply skipn_all2; lia). rewrite H in Hsr. cbn in Hsr. lia.
  - step. step. rewrite ltu_u by lia.
    replace (Z.of_nat (i + o + d) + 1 <? Z.of_nat (i + length L)) with true by zb_true. cbv iota.
    eapply (IH (S d)); [exact BL | lia | lia | | lia | lia | exact K1 | exact K2].
    rewrite Hsr. replace (o + S d)%nat with (S (o + d)) by lia. lia.
Qed.

(* the field's run of fuzz_lock.c:100-101, at 0x1303c. 0x1303c [bltu s9, a0] is the UBSan trap branch. *)
Lemma tok_loop : forall m (i : nat) (L : list byte) (o : nat) kk (j : nat) (ra a1 a2 a3 a4 a5 s8 : word) (v0 ve : Z),
  bytes_at rsegs m (tx + Z.of_nat i) L -> (o + j + S kk = length L)%nat ->
  tx + Z.of_nat (i + length L) < 2^64 ->
  tok_run (skipn o L) = (j + tok_run (skipn (o + j) L))%nat ->
  v0 = Z.of_nat (i + o + j) -> ve = Z.of_nat (i + length L) ->
  (forall (a5' : word) (w0 : Z), w0 = Z.of_nat (i + o + tok_run (skipn o L)) ->
     evt rsegs Q (ST 0x13064 ra (Z_to_bv 64 w0) a1 a2 a3 a4 a5' s8 (Z_to_bv 64 ve) m)) ->
  evt rsegs Q (ST 0x1303c ra (Z_to_bv 64 v0) a1 a2 a3 a4 a5 s8 (Z_to_bv 64 ve) m).
Proof.
  intros m i L o kk. induction kk as [|kk IH]; intros j ra a1 a2 a3 a4 a5 s8 v0 ve BL Hk He Htr -> -> K.
  all: destruct (byte_at' L (o + j) ltac:(lia)) as [b Nb].
  all: pose proof (rdL m i L (o + j) b BL Nb) as R.
  all: rewrite (skipn_nth L (o + j) b Nb) in Htr; cbn [tok_run] in Htr.
  all: pose proof (byte_range b) as Rb.
  all: replace (tx + Z.of_nat (i + (o + j))) with (tx + Z.of_nat (i + o + j)) in R by lia.
  all: step; brf.
  all: step; stp; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota.
  1, 3: pose proof (sep_hi b C1) as NS; rewrite NS in Htr.
  3, 4: step; step; step; rewrite (sep_lo b C1); destruct (is_sep (bz b)) eqn:SB; cbn [negb]; cbv iota.
  - step. step. rewrite eqb_u by lia.
    replace (Z.of_nat (i + length L) =? Z.of_nat (i + o + j) + 1) with true by zb_true. cbn [negb]; cbv iota.
    step. apply K.
    assert (skipn (S (o + j)) L = []) by (apply skipn_all2; lia). rewrite H in Htr. cbn in Htr. lia.
  - step. step. rewrite eqb_u by lia.
    replace (Z.of_nat (i + length L) =? Z.of_nat (i + o + j) + 1) with false by zb_false. cbn [negb]; cbv iota.
    eapply (IH (S j)); [exact BL | lia | lia | | lia | lia | exact K].
    rewrite Htr. replace (o + S j)%nat with (S (o + j)) by lia. lia.
  - apply K. lia.
  - step. step. rewrite eqb_u by lia.
    replace (Z.of_nat (i + length L) =? Z.of_nat (i + o + j) + 1) with true by zb_true. cbn [negb]; cbv iota.
    step. apply K.
    assert (skipn (S (o + j)) L = []) by (apply skipn_all2; lia). rewrite H in Htr. cbn in Htr. lia.
  - apply K. lia.
  - step. step. rewrite eqb_u by lia.
    replace (Z.of_nat (i + length L) =? Z.of_nat (i + o + j) + 1) with false by zb_false. cbn [negb]; cbv iota.
    eapply (IH (S j)); [exact BL | lia | lia | | lia | lia | exact K].
    rewrite Htr. replace (o + S j)%nat with (S (o + j)) by lia. lia.
Qed.

(* The record check of fuzz_lock.c:106-115, at 0x13080, with the three calls:
   bcmp at 0x130b8 and number at 0x13100 and 0x13118. Its answer is [upd], the spec's
   "what this line restores".
   0x1308c [beqz a0]: a0 = fs[0] = t + i + s1 and 0 < t.
   0x130f4 [bnez a0]: a0 is the spill of a6 = 0.
   0x1310c [bnez a0]: a0 is the spill of t3 = 0.
   Every frame cell holds an opaque Z (the equations below), because the cell machinery's
   [cbn [Nat.add]] would otherwise unfold a nat addition into its fixpoint. *)
Lemma record : forall (m : word -> option byte) (J1 : list byte) (i : nat) (L : list byte) (found : Z)
    (s1 l1 s2 l2 s3 l3 : nat) (ra a0 a3 a4 a5 : word) (ve nb ln1 ln2 ln3 f1 f2 f3 : Z),
  tx + Z.of_nat i + Z.of_nat (length L) < 2^64 -> (0 < length L)%nat ->
  tx + Z.of_nat i + Z.of_nat (length L) <= sp \/ sp + 104 <= tx + Z.of_nat i ->
  pa + Z.of_nat (length P) <= sp \/ sp + 104 <= pa ->
  fld L 0 = (s1, l1) -> fld L (s1 + l1) = (s2, l2) -> fld L (s2 + l2) = (s3, l3) ->
  (1 <= l1)%nat -> (s1 + l1 <= s2)%nat -> (1 <= l2)%nat -> (s2 + l2 <= s3)%nat -> (1 <= l3)%nat ->
  (s3 + l3 <= length L)%nat ->
  ve = Z.of_nat i + Z.of_nat (length L) -> nb = Z.b2z (nulb L) ->
  ln1 = Z.of_nat l1 -> ln2 = Z.of_nat l2 -> ln3 = Z.of_nat l3 ->
  f1 = tx + Z.of_nat i + Z.of_nat s1 -> f2 = tx + Z.of_nat i + Z.of_nat s2 ->
  f3 = tx + Z.of_nat i + Z.of_nat s3 ->
  bytes_at rsegs m (tx + Z.of_nat i) L -> bytes_at rsegs m tx T -> bytes_at rsegs m pa P ->
  munch [(sp + 8, sp + 104)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (sp + 8) [CB 40 J1] -> rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 k)] ->
  rw_cells rsegs m (sp + 56)
    [C8 (Z_to_bv 64 ln1); C8 (Z_to_bv 64 ln2); C8 (Z_to_bv 64 ln3);
     C8 (Z_to_bv 64 f1); C8 (Z_to_bv 64 f2); C8 (Z_to_bv 64 f3)] ->
  (forall (m' : word -> option byte) (J1' J2' : list byte) (ra' a0' a1' a2' a3' a4' a5' : word) (fv : Z),
     fv = upd P rate L found ->
     munch [(sp + 8, sp + 104)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' (sp + 8) [CB 40 J1'] -> rw_cells rsegs m' (sp + 48) [C8 (Z_to_bv 64 k)] ->
     rw_cells rsegs m' (sp + 56) [CB 48 J2'] ->
     bytes_at rsegs m' (tx + Z.of_nat i) L -> bytes_at rsegs m' tx T -> bytes_at rsegs m' pa P ->
     evt rsegs Q (ST 0x130e4 ra' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 fv) (Z_to_bv 64 ve) m')) ->
  evt rsegs Q (ST 0x13080 ra a0 (Z_to_bv 64 nb) (Z_to_bv 64 2) a3 a4 a5
                 (Z_to_bv 64 found) (Z_to_bv 64 ve) m).
Proof.
  intros m J1 i L found s1 l1 s2 l2 s3 l3 ra a0 a3 a4 a5 ve nb ln1 ln2 ln3 f1 f2 f3
    HTE0 HL0 DT DP E1 E2 E3 Hl1 Hs2 Hl2 Hs3 Hl3 Hs3e Eve -> Eln1 Eln2 Eln3 Ef1 Ef2 Ef3 BL BT BP MU WM MI C1 C2 C3 K.
  pose proof BCC as BC. unfold bcmp_contract in BC.
  pose proof NCC as NC. unfold number_contract in NC.
  pose proof (std_period_cases rate) as SPC.
  assert (HSTD : 0 <= std_period rate <= 272109) by (destruct SPC as [->|[[_ ->]|[[_ ->]|[_ ->]]]]; lia).
  assert (RLO : -2^63 <= lo < 2^63) by lia.
  assert (RHI : -2^63 <= hi < 2^63) by lia.
  assert (HB1 : Z.of_nat s1 <= Z.of_nat (length L)) by (apply Nat2Z.inj_le; lia).
  assert (HB2 : Z.of_nat s2 <= Z.of_nat (length L)) by (apply Nat2Z.inj_le; lia).
  assert (HB3 : Z.of_nat s3 <= Z.of_nat (length L)) by (apply Nat2Z.inj_le; lia).
  assert (HB4 : Z.of_nat l1 <= Z.of_nat (length L)) by (apply Nat2Z.inj_le; lia).
  assert (HB5 : Z.of_nat l2 <= Z.of_nat (length L)) by (apply Nat2Z.inj_le; lia).
  assert (HB6 : Z.of_nat l3 <= Z.of_nat (length L)) by (apply Nat2Z.inj_le; lia).
  assert (HB7 : 0 <= Z.of_nat s1 /\ 0 <= Z.of_nat s2 /\ 0 <= Z.of_nat s3) by lia.
  (* the junk shapes we hand back to the caller *)
  assert (FL : forall (m' : word -> option byte) cs1 cs3,
            rw_cells rsegs m' (sp + 8) cs1 -> cells_size cs1 = 40%nat ->
            rw_cells rsegs m' (sp + 56) cs3 -> cells_size cs3 = 48%nat ->
            rw_cells rsegs m' (sp + 48) [C8 (Z_to_bv 64 k)] ->
            munch [(sp + 8, sp + 104)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
            bytes_at rsegs m' (tx + Z.of_nat i) L -> bytes_at rsegs m' tx T -> bytes_at rsegs m' pa P ->
            forall (ra' a0' a1' a2' a3' a4' a5' : word) (fv : Z), fv = upd P rate L found ->
            evt rsegs Q (ST 0x130e4 ra' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 fv) (Z_to_bv 64 ve) m')).
  { intros m' cs1 cs3 Ca Cb Cc Cd Ce Cf Cg Ch Ci Cj Ck ra' a0' a1' a2' a3' a4' a5' fv Hfv.
    destruct (flatCB m' (sp + 8) cs1 40%nat Ca Cb) as [Ja Ha].
    destruct (flatCB m' (sp + 56) cs3 48%nat Cc Cd) as [Jb Hb].
    eapply K; eassumption. }
  (* 0x13080 [bnez a1]: a line with a NUL restores nothing *)
  step. rewrite nul_cond. destruct (nulb L) eqn:NUL; cbv iota.
  { eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply upd_none. intros v HV.
    destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (F0 & _).
    rewrite <- nulb_find, F0 in NUL. cbn in NUL. discriminate. }
  assert (NF : find_byte 0 L = None)
    by (pose proof (nulb_find L) as HN; rewrite NUL in HN; destruct (find_byte 0 L); [discriminate HN|reflexivity]).
  (* 0x13084 [bltu a2, t2]: nf = 2, so three fields were read *)
  step. rewrite ltu_u by lia. replace (2 <? 2) with false by zb_false. cbv iota.
  (* 0x13088 ld a0, 0x50(sp) = fs[0]; 0x1308c [beqz a0] is a UBSan trap branch *)
  step. step. rewrite eqb_u by lia. replace (f1 =? 0) with false by zb_false. cbv iota.
  (* 0x13090 lbu a1, 0(a0): the field's first byte *)
  destruct (byte_at' L s1 ltac:(lia)) as [b0 Nb0].
  pose proof (rdL m i L s1 b0 BL Nb0) as R0. pose proof (byte_range b0) as Rb0.
  replace (tx + Z.of_nat (i + s1)) with f1 in R0 by lia.
  stp. step.
  assert (NTH : bz (nth s1 L (Z_to_bv 8 0)) = bv_unsigned b0)
    by (unfold bz; f_equal; apply (nth_error_nth _ _ _ Nb0)).
  rewrite eqb_u by lia. destruct (Z.eqb_spec (bv_unsigned b0) 35) as [E35|E35]; cbv iota.
  { eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply upd_none. intros v HV.
    destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (_ & _ & NC35 & _). lia. }
  (* 0x13098 ld a1 = fl[0]; 0x1309c ld a2 = k; 0x130a0 [bne a1, a2] *)
  step. step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec ln1 k) as [EK|EK]; cbn [negb]; cbv iota.
  2: { eapply FL; try eassumption; [reflexivity|reflexivity|].
       symmetry. apply upd_none. intros v HV.
       destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (_ & _ & _ & _ & EQ & _). lia. }
  assert (EKN : l1 = length P) by lia.
  (* the spills 0x130a4-0x130b0 and the bcmp call 0x130b8 *)
  do 4 step. step. step.
  pose proof (bytes_sub _ _ L s1 l1 BL ltac:(lia)) as BS.
  replace (tx + Z.of_nat i + Z.of_nat s1) with f1 in BS by lia.
  destruct (memcmp_model_total (firstn l1 (skipn s1 L)) P (length P)
              ltac:(rewrite length_firstn, length_skipn; lia) ltac:(lia)) as [vcmp Hvcmp].
  pose proof (memcmp_model_range (length P) (firstn l1 (skipn s1 L)) P vcmp Hvcmp) as RVC.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply BC with (ls := firstn l1 (skipn s1 L)) (rs := P) (v := vcmp);
                      [ rewrite unsigned_lit by lia; exact BS
                      | rewrite unsigned_lit by lia; exact BP
                      | rewrite unsigned_lit by lia; rewrite HK, Nat2Z.id; exact Hvcmp
                      | exact MI ]
                    | post_call segs mm ] end.
  (* 0x130bc [beqz a0] *)
  step. rewrite eqb_s by lia. destruct (Z.eqb_spec vcmp 0) as [EV|EV]; cbv iota.
  2: { do 9 step.
       eapply FL; try eassumption; [reflexivity|reflexivity|].
       symmetry. apply upd_none. intros v HV.
       destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (_ & _ & _ & _ & _ & MM & _).
       unfold slice in MM. rewrite <- EKN in Hvcmp. rewrite Hvcmp in MM. injection MM as MM. lia. }
  (* 0x130f0 ld a0 = the a6 spill; 0x130f4 [bnez a0] is a UBSan trap branch *)
  step. step. rewrite eqb_u by lia. replace (0 =? 0) with true by zb_true. cbn [negb]; cbv iota.
  (* 0x130f8 ld a0 = fs[1]; 0x130fc ld a1 = fl[1]; 0x13100 jal number *)
  step. step. step.
  pose proof (bytes_sub _ _ L s2 l2 BL ltac:(lia)) as BS2.
  replace (tx + Z.of_nat i + Z.of_nat s2) with f2 in BS2 by lia.
  replace (Z_to_bv 64 ln2) with (Z_to_bv 64 (Z.of_nat (length (firstn l2 (skipn s2 L)))))
    by (f_equal; rewrite length_firstn, length_skipn; lia).
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply NC with (s := f2) (l := firstn l2 (skipn s2 L));
                      [lia | exact BS2 | assumption]
                    | post_call segs mm ] end.
  (* 0x13104 sd a0, 8(sp); 0x13108 ld a0 = the t3 spill; 0x1310c [bnez a0] is a UBSan trap branch *)
  step. step. step. rewrite eqb_u by lia. replace (0 =? 0) with true by zb_true. cbn [negb]; cbv iota.
  (* 0x13110 ld a0 = fs[2]; 0x13114 ld a1 = fl[2]; 0x13118 jal number *)
  step. step. step.
  pose proof (bytes_sub _ _ L s3 l3 BL ltac:(lia)) as BS3.
  replace (tx + Z.of_nat i + Z.of_nat s3) with f3 in BS3 by lia.
  replace (Z_to_bv 64 ln3) with (Z_to_bv 64 (Z.of_nat (length (firstn l3 (skipn s3 L)))))
    by (f_equal; rewrite length_firstn, length_skipn; lia).
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply NC with (s := f3) (l := firstn l3 (skipn s3 L));
                      [lia | exact BS3 | assumption]
                    | post_call segs mm ] end.
  (* 0x1311c ld a2 = per; 0x13120 [bltz a2] *)
  pose proof (digits_range (firstn l2 (skipn s2 L))) as RP.
  pose proof (digits_range (firstn l3 (skipn s3 L))) as RL.
  assert (P18 : 10 ^ 18 < 2^63) by (vm_compute; reflexivity).
  step. step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (digits (firstn l2 (skipn s2 L))) 0) as [PN|PN]; cbv iota.
  { do 9 step.
    eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply upd_none. intros v HV.
    destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (_ & _ & _ & _ & _ & _ & VV & VP & _).
    unfold slice in VV. lia. }
  (* the restores 0x13124-0x13134; 0x13138 [bne a0, s1] *)
  do 5 step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (digits (firstn l3 (skipn s3 L))) rate) as [EL|EL]; cbn [negb]; cbv iota.
  2: { do 5 step.
       eapply FL; try eassumption; [reflexivity|reflexivity|].
       symmetry. apply upd_none. intros v HV.
       destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (_ & _ & _ & _ & _ & _ & _ & _ & LL & _).
       unfold slice in LL. lia. }
  (* 0x1313c-0x13158: the 5% band *)
  step. step. step. do 4 step. step. rewrite band_cond by lia.
  destruct ((digits (firstn l2 (skipn s2 L)) <? lo) || (hi <? digits (firstn l2 (skipn s2 L)))) eqn:BND; cbv iota.
  { eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply upd_none. intros v HV.
    destruct (line_val_inv P rate L s1 l1 s2 l2 s3 l3 v E1 E2 E3 HV) as (_ & _ & _ & _ & _ & _ & VV & _ & _ & BB).
    unfold slice in VV. apply orb_true_iff in BND.
    destruct BND as [BB1|BB1]; apply Z.ltb_lt in BB1; lia. }
  (* the record restores its period *)
  step. step.
  eapply FL; try eassumption; [reflexivity|reflexivity|].
  apply orb_false_iff in BND. destruct BND as [BB1 BB2]. apply Z.ltb_ge in BB1. apply Z.ltb_ge in BB2.
  symmetry. unfold upd.
  rewrite (line_val_some P rate L s1 l1 s2 l2 s3 l3 E1 E2 E3 NF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
            ltac:(unfold slice; rewrite <- EKN in Hvcmp; rewrite <- EV; exact Hvcmp)
            ltac:(unfold slice; lia) ltac:(unfold slice; lia) ltac:(unfold slice; lia)).
  unfold slice. reflexivity.
Qed.

(* One line, from 0x12fc8 (the "is the line empty?" test) to 0x130e4: the NUL scan of fuzz_lock.c:92-93,
   the three fields of fuzz_lock.c:94-104 (the loop of at most three passes, unrolled, because the frame
   slot each pass writes is fs + 8*nf) and the record check. Its answer is [upd]. *)
Lemma body : forall (m : word -> option byte) (J1 : list byte) (i : nat) (L : list byte) (found : Z)
    (s1 l1 s2 l2 s3 l3 : nat) (ra a1 a2 a3 a4 a5 : word) (v0 ve : Z),
  tx + Z.of_nat i + Z.of_nat (length L) < 2^64 ->
  Z.of_nat i + Z.of_nat (length L) <= N ->
  s1 = sep_run L -> l1 = tok_run (skipn s1 L) ->
  s2 = (s1 + l1 + sep_run (skipn (s1 + l1) L))%nat -> l2 = tok_run (skipn s2 L) ->
  s3 = (s2 + l2 + sep_run (skipn (s2 + l2) L))%nat -> l3 = tok_run (skipn s3 L) ->
  v0 = Z.of_nat i -> ve = Z.of_nat i + Z.of_nat (length L) ->
  bytes_at rsegs m (tx + Z.of_nat i) L -> bytes_at rsegs m tx T -> bytes_at rsegs m pa P ->
  munch [(sp + 8, sp + 104)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (sp + 8) [CB 40 J1] -> rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 k)] ->
  rw_cells rsegs m (sp + 56)
    [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  (forall (m2 : word -> option byte) (Ja Jb : list byte) (rb b0 b1 b2 b3 b4 b5 : word) (fv : Z),
     fv = upd P rate L found ->
     munch [(sp + 8, sp + 104)] m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 ->
     rw_cells rsegs m2 (sp + 8) [CB 40 Ja] -> rw_cells rsegs m2 (sp + 48) [C8 (Z_to_bv 64 k)] ->
     rw_cells rsegs m2 (sp + 56) [CB 48 Jb] ->
     bytes_at rsegs m2 (tx + Z.of_nat i) L -> bytes_at rsegs m2 tx T -> bytes_at rsegs m2 pa P ->
     evt rsegs Q (ST 0x130e4 rb b0 b1 b2 b3 b4 b5 (Z_to_bv 64 fv) (Z_to_bv 64 ve) m2)) ->
  evt rsegs Q (ST 0x12fc8 ra (Z_to_bv 64 v0) a1 a2 a3 a4 a5 (Z_to_bv 64 found) (Z_to_bv 64 ve) m).
Proof.
  intros m J1 i L found s1 l1 s2 l2 s3 l3 ra a1 a2 a3 a4 a5 v0 ve HTE0 HIL Hs1 Hl1 Hs2 Hl2 Hs3 Hl3
    -> Eve BL BT BP MU WM MI C1 C2 C3 K.
  assert (DT : tx + Z.of_nat i + Z.of_nat (length L) <= sp \/ sp + 104 <= tx + Z.of_nat i) by lia.
  assert (E1 : fld L 0 = (s1, l1)).
  { unfold fld. cbv zeta. change (skipn 0 L) with L. rewrite Nat.add_0_l, <- Hs1, <- Hl1. reflexivity. }
  assert (E2 : fld L (s1 + l1) = (s2, l2)) by (unfold fld; cbv zeta; rewrite <- Hs2, <- Hl2; reflexivity).
  assert (E3 : fld L (s2 + l2) = (s3, l3)) by (unfold fld; cbv zeta; rewrite <- Hs3, <- Hl3; reflexivity).
  pose proof (sep_run_le L) as B1.
  pose proof (tok_run_le (skipn s1 L)) as B2. rewrite length_skipn in B2.
  pose proof (sep_run_le (skipn (s1 + l1) L)) as B3. rewrite length_skipn in B3.
  pose proof (tok_run_le (skipn s2 L)) as B4. rewrite length_skipn in B4.
  pose proof (sep_run_le (skipn (s2 + l2) L)) as B5. rewrite length_skipn in B5.
  pose proof (tok_run_le (skipn s3 L)) as B6. rewrite length_skipn in B6.
  assert (FL : forall (m2 : word -> option byte) cs1 cs3,
            rw_cells rsegs m2 (sp + 8) cs1 -> cells_size cs1 = 40%nat ->
            rw_cells rsegs m2 (sp + 56) cs3 -> cells_size cs3 = 48%nat ->
            rw_cells rsegs m2 (sp + 48) [C8 (Z_to_bv 64 k)] ->
            munch [(sp + 8, sp + 104)] m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 ->
            bytes_at rsegs m2 (tx + Z.of_nat i) L -> bytes_at rsegs m2 tx T -> bytes_at rsegs m2 pa P ->
            forall (rb b0 b1 b2 b3 b4 b5 : word) (fv : Z), fv = upd P rate L found ->
            evt rsegs Q (ST 0x130e4 rb b0 b1 b2 b3 b4 b5 (Z_to_bv 64 fv) (Z_to_bv 64 ve) m2)).
  { intros m2 cs1 cs3 Ca Cb Cc Cd Ce Cf Cg Ch Ci Cj Ck rb b0 b1 b2 b3 b4 b5 fv Hfv.
    destruct (flatCB m2 (sp + 8) cs1 40%nat Ca Cb) as [Ja Ha].
    destruct (flatCB m2 (sp + 56) cs3 48%nat Cc Cd) as [Jb Hb].
    eapply K; eassumption. }
  destruct (Nat.eq_dec (length L) 0) as [L0|L0].
  { (* an empty line reads no field *)
    assert (HZ : l1 = 0%nat) by (rewrite Hl1, Hs1; destruct L; cbn in *; [reflexivity|lia]).
    step. brt.
    eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply (upd_l1 P rate L found s1). rewrite E1, HZ. reflexivity. }
  step. brf. step. step.
  (* the NUL scan *)
  eapply nul_loop with (i := i) (L := L) (o := 0%nat) (kk := (length L - 1)%nat);
    [exact BL | lia | lia | reflexivity | lia | lia |].
  intros aN2 aN3 w1 Hw1.
  (* 0x12ff0 mv a3, zero: nf = 0 *)
  step.
  (* ---------------- the first field ---------------- *)
  step. step.
  eapply sep_loop with (i := i) (L := L) (o := 0%nat) (d := 0%nat) (kk := (length L - 1)%nat);
    [exact BL | lia | lia | reflexivity | lia | lia | |].
  { intros c0 c3 c4 Hend. change (skipn 0 L) with L in Hend.
    assert (HZ : l1 = 0%nat) by (rewrite Hl1, Hs1, skipn_all2 by lia; reflexivity).
    eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply (upd_l1 P rate L found s1). rewrite E1, HZ. reflexivity. }
  intros c4 w0 w3 Hw0 Hw3 Hlt. change (skipn 0 L) with L in Hw0, Hw3, Hlt.
  assert (Hl1p : (1 <= l1)%nat) by (rewrite Hl1, Hs1; apply sep_run_stop; lia).
  (* 0x13024-0x1302c: fs[0] = t + j *)
  step. step. step.
  (* 0x13030 mv a0, a3; 0x13034 bgeu a3, s11 *)
  step. step. brf. step.
  eapply tok_loop with (i := i) (L := L) (o := s1) (j := 0%nat) (kk := (length L - s1 - 1)%nat);
    [assumption | lia | lia | rewrite Nat.add_0_r; lia | lia | lia |].
  intros d5 w0a Hw0a.
  (* 0x13064 [bltu s9, a0] is a UBSan trap branch; 0x13068-0x13070: fl[0] *)
  step. brf. step. step. step.
  (* 0x13074 bgeu a0, s11 *)
  destruct (Nat.eq_dec (s1 + l1) (length L)) as [Q1|Q1].
  { step. brt.
    assert (Hs2v : s2 = length L) by (rewrite Hs2, Q1, skipn_all2 by lia; cbn [sep_run]; lia).
    assert (HZ : l2 = 0%nat) by (rewrite Hl2, Hs2v, skipn_all2 by lia; reflexivity).
    step. rewrite Hw1, nul_cond. destruct (nulb L); cbv iota;
      [ | step; rewrite ltu_u by lia; replace (0 <? 2) with true by zb_true; cbv iota ].
    all: (eapply FL; try eassumption; [reflexivity|reflexivity|]).
    all: symmetry; apply (upd_l2 P rate L found s1 l1 s2); [exact E1 | rewrite E2, HZ; reflexivity]. }
  step. brf. step. step. brt.
  (* ---------------- the second field ---------------- *)
  step. step.
  eapply sep_loop with (i := i) (L := L) (o := (s1 + l1)%nat) (d := 0%nat)
                       (kk := (length L - (s1 + l1) - 1)%nat);
    [assumption | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | |].
  { intros e0 e3 e4 Hend.
    assert (Hs2v : s2 = length L) by lia.
    assert (HZ : l2 = 0%nat) by (rewrite Hl2, Hs2v, skipn_all2 by lia; reflexivity).
    eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply (upd_l2 P rate L found s1 l1 s2); [exact E1 | rewrite E2, HZ; reflexivity]. }
  intros e4 w0b w3b Hw0b Hw3b Hltb.
  assert (Hl2p : (1 <= l2)%nat) by (rewrite Hl2, Hs2; apply sep_run_stop'; lia).
  step. step. step. step. step. brf. step.
  eapply tok_loop with (i := i) (L := L) (o := s2) (j := 0%nat) (kk := (length L - s2 - 1)%nat);
    [assumption | lia | lia | rewrite Nat.add_0_r; lia | lia | lia |].
  intros f5 w0bb Hw0bb.
  step. brf. step. step. step.
  destruct (Nat.eq_dec (s2 + l2) (length L)) as [Q2|Q2].
  { step. brt.
    assert (Hs3v : s3 = length L) by (rewrite Hs3, Q2, skipn_all2 by lia; cbn [sep_run]; lia).
    assert (HZ : l3 = 0%nat) by (rewrite Hl3, Hs3v, skipn_all2 by lia; reflexivity).
    step. rewrite Hw1, nul_cond. destruct (nulb L); cbv iota;
      [ | step; rewrite ltu_u by lia; replace (1 <? 2) with true by zb_true; cbv iota ].
    all: (eapply FL; try eassumption; [reflexivity|reflexivity|]).
    all: symmetry; apply (upd_l3 P rate L found s1 l1 s2 l2 s3);
      [lia | exact E1 | exact E2 | rewrite E3, HZ; reflexivity]. }
  step. brf. step. step. brt.
  (* ---------------- the third field ---------------- *)
  step. step.
  eapply sep_loop with (i := i) (L := L) (o := (s2 + l2)%nat) (d := 0%nat)
                       (kk := (length L - (s2 + l2) - 1)%nat);
    [assumption | lia | lia | rewrite Nat.add_0_r; reflexivity | lia | lia | |].
  { intros g0 g3 g4 Hend.
    assert (Hs3v : s3 = length L) by lia.
    assert (HZ : l3 = 0%nat) by (rewrite Hl3, Hs3v, skipn_all2 by lia; reflexivity).
    eapply FL; try eassumption; [reflexivity|reflexivity|].
    symmetry. apply (upd_l3 P rate L found s1 l1 s2 l2 s3);
      [lia | exact E1 | exact E2 | rewrite E3, HZ; reflexivity]. }
  intros g4 w0c w3c Hw0c Hw3c Hltc.
  assert (Hl3p : (1 <= l3)%nat) by (rewrite Hl3, Hs3; apply sep_run_stop'; lia).
  step. step. step. step. step. brf. step.
  eapply tok_loop with (i := i) (L := L) (o := s3) (j := 0%nat) (kk := (length L - s3 - 1)%nat);
    [assumption | lia | lia | rewrite Nat.add_0_r; lia | lia | lia |].
  intros h5 w0cc Hw0cc.
  step. brf. step. step. step.
  (* three fields: 0x13074 either way reaches 0x13080 with nf = 2 *)
  destruct (Nat.eq_dec (s3 + l3) (length L)) as [Q3|Q3].
  { step. brt.
    eapply record with (i := i) (L := L) (s1 := s1) (l1 := l1) (s2 := s2) (l2 := l2) (s3 := s3) (l3 := l3);
      try eassumption; try lia; try reflexivity.
    all: rewrite !unsigned_lit by lia; lia. }
  step. brf. step. step. brf.
  eapply record with (i := i) (L := L) (s1 := s1) (l1 := l1) (s2 := s2) (l2 := l2) (s3 := s3) (l3 := l3);
    try eassumption; try lia; try reflexivity.
  all: rewrite !unsigned_lit by lia; lia.
Qed.

(* the line loop of fuzz_lock.c:84-116, at 0x12f80; [fuel] bounds the lines still to read *)
Lemma lines : forall (fuel : nat) (m : word -> option byte) (J1 J2 : list byte) (i : nat) (found : Z)
    (ra a1 a2 a3 a4 a5 s11a : word) (v0 : Z),
  (i < length T)%nat -> (length T - i <= fuel)%nat -> v0 = Z.of_nat i ->
  lk (length (skipn i T)) P rate (skipn i T) found = lk (length T) P rate T 0 ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa P ->
  munch [(sp + 8, sp + 104)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (sp + 8) [CB 40 J1] -> rw_cells rsegs m (sp + 48) [C8 (Z_to_bv 64 k)] ->
  rw_cells rsegs m (sp + 56) [CB 48 J2] ->
  (forall (m2 : word -> option byte) (Ja Jb : list byte)
          (r0 r1 r2 rb b0 b1 b2 b3 b4 b5 b6 b7 u2 u7 u9 u10 u11 v3 v4 v5 v6 : word) (fv : Z),
     fv = lk (length T) P rate T 0 ->
     munch [(sp + 8, sp + 104)] m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 ->
     rw_cells rsegs m2 (sp + 8) [CB 40 Ja] -> rw_cells rsegs m2 (sp + 48) [C8 (Z_to_bv 64 k)] ->
     rw_cells rsegs m2 (sp + 56) [CB 48 Jb] ->
     bytes_at rsegs m2 tx T -> bytes_at rsegs m2 pa P ->
     evt rsegs Q (MS (mkR rb (Z_to_bv 64 sp) gp tp r0 r1 r2 s0 (Z_to_bv 64 rate)
                          b0 b1 b2 b3 b4 b5 b6 b7
                          u2 (Z_to_bv 64 pa) (Z_to_bv 64 N) (Z_to_bv 64 tx)
                          got u7 (Z_to_bv 64 fv) u9 u10 u11 v3 v4 v5 v6)
                      F (Z_to_bv 64 0x1317c) fc None m2 (seg_rom rsegs))) ->
  evt rsegs Q (ST 0x12f80 ra (Z_to_bv 64 v0) a1 a2 a3 a4 a5 (Z_to_bv 64 found) s11a m).
Proof.
  induction fuel as [|fuel IH];
    intros m J1 J2 i found ra a1 a2 a3 a4 a5 s11a v0 Hi Hf -> HINV BT BP MU WM MI C1 C2 C3 KFIN;
    [lia|].
  pose proof (line_len_le (skipn i T)) as LL. rewrite length_skipn in LL.
  set (j := line_len (skipn i T)) in *.
  assert (HJ : (i + j <= length T)%nat) by lia.
  assert (MAIN : forall (a2b : word),
            evt rsegs Q (ST 0x12f94 ra (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 N) a2b a3 a4 a5
                           (Z_to_bv 64 found) (Z_to_bv 64 (Z.of_nat i)) m)).
  { intros a2b.
    eapply eol_loop with (i := i) (o := 0%nat) (kk := (length T - i - 1)%nat);
      [exact BT | lia | reflexivity | lia |].
    intros a2c.
    (* the six zero stores of fuzz_lock.c:89-90, 0x12fb0-0x12fc4 *)
    do 6 step.
    eapply body with (i := i) (L := firstn j (skipn i T)) (found := found);
      [ rewrite win_len by lia; lia
      | rewrite win_len by lia; lia
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | rewrite win_len by lia; lia
      | apply (bytes_sub _ _ T i j BT ltac:(lia))
      | exact BT | exact BP | exact MU | exact WM | eassumption | eassumption | eassumption | eassumption | ].
    intros m2 Ja Jb rb b0 b1 b2 b3 b4 b5 fv Hfv MU2 WM2 MI2 C1b C2b C3b BL2 BT2 BP2.
    (* 0x130e4 addi a0, s11, 1; 0x130e8 bltu a0, s4 *)
    destruct (Z_lt_ge_dec (Z.of_nat i + Z.of_nat j + 1) N) as [LT|LT].
    - (* another line *)
      step. step. brt.
      eapply (IH m2 Ja Jb (i + j + 1)%nat fv); try eassumption; [lia | lia | lia | ].
      destruct (find_byte 10 (skipn i T)) as [q|] eqn:FB.
      + assert (Hq : q = j) by (unfold j, line_len; rewrite FB; reflexivity).
        rewrite <- HINV, (lk_line_lf P rate (skipn i T) found q FB).
        rewrite skipn_skipn. replace (S q + i)%nat with (i + j + 1)%nat by lia.
        rewrite Hfv. first [reflexivity | (do 2 f_equal; unfold line_len; rewrite FB, Hq; reflexivity)].
      + exfalso. assert (HX : j = length (skipn i T)) by (unfold j, line_len; rewrite FB; reflexivity).
        rewrite length_skipn in HX. lia.
    - (* the text is read: 0x130ec j 0x1317c; this line's answer is the lookup *)
      step. step. brf. step.
      eapply KFIN; try eassumption.
      rewrite <- HINV, Hfv.
      destruct (find_byte 10 (skipn i T)) as [q|] eqn:FB.
      + assert (Hq : q = j) by (unfold j, line_len; rewrite FB; reflexivity).
        rewrite (lk_line_lf P rate (skipn i T) found q FB).
        assert (HE : skipn (S q) (skipn i T) = []) by (apply skipn_all2; rewrite length_skipn; lia).
        rewrite HE, lk_nil. unfold line_len. rewrite FB, Hq. reflexivity.
      + rewrite (lk_line_end P rate (skipn i T) found); [reflexivity | | exact FB].
        intros HN. assert (HX : length (skipn i T) = 0%nat) by (rewrite HN; reflexivity).
        rewrite length_skipn in HX. lia. }
  (* 0x12f80 addi a2, a0, 1; 0x12f84 mv a1, s4; 0x12f88 bltu a2, s4 *)
  step. step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (Z.of_nat i + 1) N) as [LT|LT]; cbv iota.
  - step. apply MAIN.
  - step. replace (Z.of_nat i + 1) with N by lia. step. apply MAIN.
Qed.

End W.

(* the size test of fuzz_lock.c:81 at 0x12ee4-0x12eec: (n - 1) >> 16 is not 0 iff n = 0 or n > 65536 *)
Lemma sz_cond : forall n, 0 <= n < 2^64 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (n + -1))) 16)) (Z_to_bv 64 0))
  = negb ((1 <=? n) && (n <=? 65536)).
Proof.
  intros n Hn. f_equal. rewrite unsigned_lit_wrap.
  replace (n + -1) with (n - 1) by lia.
  pose proof (Z.mod_pos_bound (n - 1) (2^64) ltac:(lia)) as M.
  assert (HX : 0 <= Z.shiftr ((n - 1) mod 2^64) 16 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with ((n - 1) mod 2^64); [apply Z.div_le_upper_bound; lia | lia]. }
  rewrite eqb_u by lia. apply size_test. lia.
Qed.

(* lo and hi of the line loop: the machine's divu/mulhu expressions at t4 and t5, evaluated on the three
   rates the daemon detects *)
Ltac lohi HR3 rate :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    lazymatch R with
    | TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some _) TEmpty) (Some _) TEmpty) (Some _) (TNode TEmpty (Some _) TEmpty)) (Some _) (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some _) TEmpty)))
         (Some _) (TNode (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some _) TEmpty)) (Some _) (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some (Z_to_bv 64 ?e4)) TEmpty))))
        None
        (TNode (TNode (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some _) TEmpty)) (Some _) (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some _) TEmpty))) (Some _)
         (TNode (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some _) TEmpty)) (Some _) (TNode (TNode TEmpty (Some _) TEmpty) (Some _) (TNode TEmpty (Some (Z_to_bv 64 ?e5)) TEmpty))))
      => let E4 := fresh "E4" in let E5 := fresh "E5" in
         assert (E4 : e4 = std_period rate - std_period rate / 20)
           by (destruct HR3 as [->|[->| ->]]; vm_compute; reflexivity);
         assert (E5 : e5 = std_period rate + std_period rate / 20)
           by (destruct HR3 as [->|[->| ->]]; vm_compute; reflexivity);
         rewrite E4, E5; clear E4 E5
    end
  end.


(** * The segment: from 0x12ebc (rp_lock_lookup has returned got in a0) to 0x1317c ([bne s6, s8]),
    where s6 = got and s8 = want = LockSpec.lock_lookup T P rate. *)
Theorem check_lookup_exp_seg :
  bcmp_contract -> number_contract ->
  forall (ra gp tp t0 t1 t2 s0 got a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (sp tx pa rate k : Z) (T P J1 Jk J2 : list byte) (Q : machine_state -> Prop),
  0 <= sp -> sp + 104 <= 2^64 ->
  0 < tx -> tx + Z.of_nat (length T) < 2^64 ->
  0 < pa -> pa + Z.of_nat (length P) <= 2^64 ->
  tx + Z.of_nat (length T) <= sp \/ sp + 104 <= tx ->
  pa + Z.of_nat (length P) <= sp \/ sp + 104 <= pa ->
  (length P <= 15)%nat -> k = Z.of_nat (length P) ->
  0 <= rate < 2^64 ->
  bytes_at rsegs m tx T -> bytes_at rsegs m pa P ->
  rw_cells rsegs m (sp + 8) [CB 40 J1] -> rw_cells rsegs m (sp + 48) [CB 8 Jk] ->
  rw_cells rsegs m (sp + 56) [CB 48 J2] ->
  mem_inv rsegs m ->
  (forall (t0' t1' t2' ra' a0' a1' a2' a3' a4' a5' a6' a7' s2' s7' s9' s10' s11' t3' t4' t5' t6' : word)
          (m' : word -> option byte) (J1' Jk' J2' : list byte),
     munch [(sp + 8, sp + 104)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' (sp + 8) [CB 40 J1'] -> rw_cells rsegs m' (sp + 48) [CB 8 Jk'] ->
     rw_cells rsegs m' (sp + 56) [CB 48 J2'] ->
     bytes_at rsegs m' tx T -> bytes_at rsegs m' pa P ->
     evt rsegs Q (MS (mkR ra' (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 (Z_to_bv 64 rate)
                          a0' a1' a2' a3' a4' a5' a6' a7'
                          s2' (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx)
                          got s7' (Z_to_bv 64 (lock_lookup T P rate)) s9' s10' s11' t3' t4' t5' t6')
                     F (Z_to_bv 64 0x1317c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate)
                       got a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx)
                       s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12ebc) fc None m (seg_rom rsegs)).
Proof.
  intros BCC NCC ra gp tp t0 t1 t2 s0 got a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    sp tx pa rate k T P J1 Jk J2 Q HSP HSPE HTX HTE HPA HPE DTS DPS HKL HK HRR BT BP C1 C2 C3 MI K.
  pose proof (munch_refl [(sp + 8, sp + 104)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* the exit with want = 0, at 0x13178 [mv s8, zero] *)
  assert (EXIT0 : forall (r0 r1 r2 rb b0 b1 b2 b3 b4 b5 b6 b7 u7 u8 u9 u10 u11 v3 v4 v5 v6 : word),
            lock_lookup T P rate = 0 ->
            evt rsegs Q (MS (mkR rb (Z_to_bv 64 sp) gp tp r0 r1 r2 s0 (Z_to_bv 64 rate)
                                 b0 b1 b2 b3 b4 b5 b6 b7
                                 (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx)
                                 got u7 u8 u9 u10 u11 v3 v4 v5 v6)
                             F (Z_to_bv 64 0x13178) fc None m (seg_rom rsegs))).
  { intros r0 r1 r2 rb b0 b1 b2 b3 b4 b5 b6 b7 u7 u8 u9 u10 u11 v3 v4 v5 v6 L0.
    step. rewrite <- L0. eapply K; eassumption. }
  (* the three rates the daemon detects run the line loop *)
  assert (MAIN : forall x0 x1 : word, rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
            evt rsegs Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate)
                                 x0 x1 a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 tx)
                                 got s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x12ee4) fc None m (seg_rom rsegs))).
  { intros x0 x1 HR3.
    assert (HSN : std_period rate <> 0) by (destruct HR3 as [->|[->| ->]]; vm_compute; discriminate).
    (* 0x12ee4 addi a0, s4, -1; 0x12ee8 srli a0, a0, 16; 0x12eec bnez a0 *)
    step. step. step. rewrite sz_cond by lia.
    destruct ((1 <=? Z.of_nat (length T)) && (Z.of_nat (length T) <=? 65536)) eqn:SZ; cbn [negb]; cbv iota.
    2: { apply EXIT0. apply lock_lookup_0.
         apply andb_false_iff in SZ. destruct SZ as [SZ|SZ]; [apply Z.leb_gt in SZ | apply Z.leb_gt in SZ].
         - right; right. destruct T; [reflexivity | cbn in SZ; lia].
         - right; left. lia. }
    apply andb_true_iff in SZ. destruct SZ as [SZ1 SZ2]. apply Z.leb_le in SZ1. apply Z.leb_le in SZ2.
    replace (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.of_nat (length T) + -1))) 16) with 0.
    2: { rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.div_small.
         change (2^16) with 65536. lia. }
    (* 0x12ef0 sd s2, 0x30(sp): the k slot *)
    step.
    (* 0x12ef4-0x12f7c: found = 0 and the loop's constants; std = (12e9 + rate/2) / rate by divu at
       0x12f64, std / 20 by mulhu at 0x12f6c, lo and hi at 0x12f74 and 0x12f78 *)
    do 35 step.
    (* the two UBSan flags: a6 = seqz(sp + 88) | seqz(sp + 64) = 0, t3 = xori(sltu(sp + 80, -16) &
       sltu(sp + 56, -16), 1) = 0; and s9 = not t *)
    repeat match goal with
    | |- context [bv_unsigned (v_sltiu (Z_to_bv 64 ?z) 1)] => rewrite (sltiu1_nz z) by lia
    | |- context [bv_unsigned (v_sltiu (Z_to_bv 64 ?z) (-16))] => rewrite (sltiu_m16 z) by lia
    end.
    rewrite (not64 tx) by lia.
    fold_closed_in_goal.
    lohi HR3 rate.
    eapply lines with (m0 := m) (nt := 2^64 - 1 - tx) (lo := std_period rate - std_period rate / 20)
                      (hi := std_period rate + std_period rate / 20) (fuel := length T) (i := 0%nat) (found := 0).
    all: try first [ eassumption | lia | (destruct HR3 as [->|[->| ->]]; lia) | reflexivity ].
    intros m2 Ja Jb r0 r1 r2 rb b0 b1 b2 b3 b4 b5 b6 b7 u2 u7 u9 u10 u11 v3 v4 v5 v6 fv Hfv MU2 WM2 MI2 C1b C2b C3b BT2 BP2.
    destruct (flatCB m2 (sp + 48) [C8 (Z_to_bv 64 k)] 8%nat C2b eq_refl) as [Jk2 Hk2].
    rewrite Hfv, <- lock_lookup_lk by first [lia | exact HSN].
    eapply K; eassumption. }
  (* 0x12ebc lui a1; 0x12ec0 addiw a1 = 44100; 0x12ec4 mv s6, a0 *)
  step. step. step.
  (* 0x12ec8 beq s1, 44100 *)
  step. rewrite eqb_u by lia. destruct (Z.eqb_spec rate 44100) as [R1|R1]; cbv iota.
  { apply MAIN. left. exact R1. }
  (* 0x12ecc lui a0; 0x12ed0 addiw a0 = 96000; 0x12ed4 beq s1, 96000 *)
  step. step. step. rewrite eqb_u by lia. destruct (Z.eqb_spec rate 96000) as [R2|R2]; cbv iota.
  { apply MAIN. right. right. exact R2. }
  (* 0x12ed8 lui a0; 0x12edc addiw a0 = 48000; 0x12ee0 bne s1, 48000 *)
  step. step. step. rewrite eqb_u by lia. destruct (Z.eqb_spec rate 48000) as [R3|R3]; cbn [negb]; cbv iota.
  { apply MAIN. right. left. exact R3. }
  (* any other rate: the daemon never detects it, and the grammar restores nothing *)
  apply EXIT0. apply lock_lookup_0. left. unfold std_period.
  rewrite (proj2 (Z.eqb_neq _ _) R1), (proj2 (Z.eqb_neq _ _) R3), (proj2 (Z.eqb_neq _ _) R2). reflexivity.
Qed.
