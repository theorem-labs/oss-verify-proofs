(* The helper lemmas of the plain walk of io_send (lib/Prog/T/io_send.v), and the walk's DATA arm from 0x146e8
   (fuzz/fuzz_transport.c:857-889) as one lemma, io_send_data: check_inflight_new, the inlined command count loop of
   :858-862 (tagged_of inlined), check_latest_frame, M.host_counter and g_last_counter, then check_keepalive_due and
   M.next_ka, or check_latest_sent and check_latest_display, then the frame in flight (io_send.v's FLY). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract io_send_keep
  check_inflight_new_c check_latest_frame_c check_keepalive_due_c check_latest_sent_c check_latest_display_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the frame cell of the walk, split into its four regions ---- *)

Lemma rwc_split : forall m A A2 (bs : list byte) (n n1 n2 : nat),
  rw_cells rsegs m A [CB n bs] -> (n = n1 + n2)%nat -> A2 = A + Z.of_nat n1 ->
  exists b1 b2, rw_cells rsegs m A [CB n1 b1] /\ rw_cells rsegs m A2 [CB n2 b2].
Proof.
  intros m A A2 bs n n1 n2 [[Hwf Hb] Hw] Hn ->.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hw as (HA & HE & HW). cbn [cells_size csize] in HE, HW. rewrite Nat.add_0_r in HE, HW.
  exists (firstn n1 bs), (skipn n1 bs).
  rewrite <- (firstn_skipn n1 bs) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite firstn_length in B2. rewrite Nat.min_l in B2 by lia.
  split.
  - split.
    + split.
      * cbn [cells_wf cell_wf]. split; [rewrite firstn_length; lia | exact I].
      * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
    + split; [lia|]. split; [cbn [cells_size csize]; rewrite Nat.add_0_r; lia|].
      intros i Hi. apply HW. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r in Hi. lia.
  - split.
    + split.
      * cbn [cells_wf cell_wf]. split; [rewrite skipn_length; lia | exact I].
      * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
    + split; [lia|]. split; [cbn [cells_size csize]; rewrite Nat.add_0_r; lia|].
      intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r in Hi.
      replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply HW. lia.
Qed.

(* ---- reading the frame buffer and the branch conditions (after another unit's frame-table lemmas, renamed
   where TWorldLemmas already has the name) ---- *)

Lemma rd_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

Lemma nth_firstn : forall {X} n (l : list X) i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X n. induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma bytes_at_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn. unfold sub.
  assert (Ln : length (firstn n (skipn (Z.to_nat k) bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi.
  rewrite nth_firstn by lia. rewrite nth_skipn.
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma lw_val : forall bs, length bs = 4%nat ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs)).
Proof.
  intros bs L. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. f_equal.
  pose proof (ble_range bs) as H. rewrite L in H. apply bv_wrap_small. unfold bv_modulus. cbn in H. lia.
Qed.

Lemma lbu_val : forall bs, length bs = 1%nat ->
  zext 64 (bv_extract 0 8 (le_bytes_to_word bs)) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (ble_range bs) as H. rewrite L in H. cbn in H.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). apply Z.mod_small. cbn. lia.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 (z + 1)).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  - replace (z mod 2^64) with (z + 2^64).
    + destruct (Z.ltb_spec (z + 2^64) (2^63)); lia.
    + symmetry. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit by assumption. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma ble_one : forall x : byte, bytes_le_to_Z [x] = bv_unsigned x.
Proof. intros x. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. lia. Qed.

Lemma sub1_nth : forall (l : list byte) (k : Z), 0 <= k < Z.of_nat (length l) ->
  sub l k 1 = [nth (Z.to_nat k) l (b8 0)].
Proof.
  intros l k Hk. unfold sub.
  assert (E : nth_error (skipn (Z.to_nat k) l) 0 = Some (nth (Z.to_nat k) l (b8 0))).
  { rewrite nth_skipn, Nat.add_0_r. apply nth_error_nth'. lia. }
  destruct (skipn (Z.to_nat k) l) as [|x rr] eqn:S; cbn [nth_error] in E; [discriminate|].
  cbn [firstn]. inversion E. reflexivity.
Qed.

Lemma bytes_at_sub' : forall m a bs k n a', bytes_at rsegs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> a' = a + k -> bytes_at rsegs m a' (sub bs k n).
Proof. intros m a bs k n a' H Hk Hn ->. apply bytes_at_sub; assumption. Qed.

(* the stack region across a call that writes one span: inside the span the callee's cell gives the byte back,
   outside it the footprint does (the kit's stk_transport_disjoint wants the span off the region, which the
   memcpy into M.fly.frame is not when the slot's stack floor lies below the world) *)
Lemma stk_after_copy : forall (m1 m2 : word -> option byte) (lo hi X n : Z) (src : list byte),
  stk rsegs m1 lo hi -> munch [(X, X + n)] m1 m2 -> wmono rsegs m1 m2 ->
  rw_cells rsegs m2 X [CB (Z.to_nat n) src] -> 0 <= n -> 0 <= X -> X + n <= 2 ^ 64 ->
  stk rsegs m2 lo hi.
Proof.
  intros m1 m2 lo hi X n src (S1 & S2 & S3) MU WM D Hn HX HXn.
  split; [exact S1|]. split; [exact S2|].
  intros a Ha. destruct (S3 a Ha) as [Hw Hr].
  assert (Ra : 0 <= a < 2 ^ 64) by lia.
  split.
  - apply WM. exact Hw.
  - destruct (Z_le_gt_dec X a) as [L1|L1]; [destruct (Z_lt_le_dec a (X + n)) as [L2|L2]|].
    + destruct D as [[Hwf Hb] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hlen _].
      cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      destruct Hb as (Hb1 & Hb2 & Hb3).
      specialize (Hb3 (Z.to_nat (a - X)) ltac:(rewrite Hlen; lia)).
      replace (X + Z.of_nat (Z.to_nat (a - X))) with a in Hb3 by lia.
      rewrite Hb3. destruct (nth_error src (Z.to_nat (a - X))) eqn:E; [eexists; reflexivity|].
      exfalso. apply nth_error_None in E. rewrite Hlen in E. lia.
    + unfold mrd. rewrite (MU (wa a)) by
        (unfold wa; rewrite unsigned_lit by lia; cbn; split; [lia | exact I]).
      exact Hr.
    + unfold mrd. rewrite (MU (wa a)) by
        (unfold wa; rewrite unsigned_lit by lia; cbn; split; [lia | exact I]).
      exact Hr.
Qed.
(* a one-byte read of the frame is the model's at8 *)
Lemma ble_sub1 : forall (l : list byte) (k : Z) (i : nat), i = Z.to_nat k -> 0 <= k < Z.of_nat (length l) ->
  bytes_le_to_Z (sub l k 1) = at8 l i.
Proof. intros l k i -> Hk. rewrite sub1_nth by lia. rewrite ble_one. reflexivity. Qed.

(* the byte assembly of the inlined parse: `slli x,k ; or x,y` is x * 2^k + y *)
Lemma lor_sh : forall x y k, 0 <= k -> 0 <= y < 2 ^ k -> Z.lor (Z.shiftl x k) y = x * 2 ^ k + y.
Proof. intros x y k Hk Hy. rewrite Z.shiftl_mul_pow2 by lia. apply lk_lor_mul_pow2; lia. Qed.

(* every [bv_unsigned (Z_to_bv 64 v)] of a frame byte (or of a shifted frame byte) is v *)
Ltac cleanz :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 (at8 ?l ?i))] => rewrite (unsigned_lit (at8 l i)) by lia
  | |- context [bv_unsigned (Z_to_bv 64 (Z.shiftl (at8 ?l ?i) ?k))] =>
        rewrite (unsigned_lit (Z.shiftl (at8 l i) k)) by (rewrite Z.shiftl_mul_pow2 by lia; lia)
  | |- context [bv_unsigned (Z_to_bv 64 (at8 ?l ?i * 2 ^ ?a + at8 ?l ?j * 2 ^ ?b))] =>
        rewrite (unsigned_lit (at8 l i * 2 ^ a + at8 l j * 2 ^ b)) by lia
  | |- context [bv_unsigned (Z_to_bv 64 (at8 ?l ?i * 2 ^ ?a + at8 ?l ?j))] =>
        rewrite (unsigned_lit (at8 l i * 2 ^ a + at8 l j)) by lia
  end.

(* the body sum of the inlined parse fits in a register *)
Lemma sum_bytes_bound : forall l : list byte, 0 <= sum_bytes l <= 255 * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; cbn [sum_bytes length]; [lia|].
  pose proof (bz_range x). lia.
Qed.

(* the bytes of a cell list at its base *)
Lemma rwc_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

(* a two-byte store keeps only the low 16 bits (the body sum of the inlined parse) *)
Lemma put2_mod : forall v, put 2 (v mod 2 ^ 16) = put 2 v.
Proof. intros v. unfold put. apply Z_to_le_bytes_mod. lia. Qed.

Lemma put4_mod : forall v, put 4 (v mod 2 ^ 32) = put 4 v.
Proof. intros v. unfold put. apply Z_to_le_bytes_mod. lia. Qed.

Lemma put4_cong : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> put 4 x = put 4 y.
Proof. intros x y H. rewrite <- (put4_mod x), <- (put4_mod y), H. reflexivity. Qed.

Lemma mod64_32 : forall y, (y mod 2 ^ 64) mod 2 ^ 32 = y mod 2 ^ 32.
Proof.
  intros y. rewrite (Z.mod_eq y (2 ^ 64)) by lia.
  replace (y - 2 ^ 64 * (y / 2 ^ 64)) with (y + (- (2 ^ 32 * (y / 2 ^ 64))) * 2 ^ 32) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma swrap32_mod : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* the `lw ; addi 1 ; sw` of a counter: the stored word is the model's x + 1 (u32 (x + 1) for an unsigned one) *)
Lemma put4_wrap1 : forall v, put 4 (bv_unsigned (Z_to_bv 64 v) + 1) = put 4 (v + 1).
Proof.
  intros v. apply put4_cong. rewrite unsigned_lit_wrap.
  rewrite (Zplus_mod (v mod 2 ^ 64) 1), mod64_32, <- Zplus_mod. reflexivity.
Qed.

Lemma put4_swrap_inc : forall x, put 4 (bv_swrap 32 x + 1) = put 4 (u32 (x + 1)).
Proof.
  intros x. apply put4_cong. unfold u32. rewrite Z.mod_mod by lia.
  rewrite (Zplus_mod (bv_swrap 32 x) 1), swrap32_mod, <- Zplus_mod. reflexivity.
Qed.

Lemma put4_s32_inc : forall x, put 4 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) + 1) = put 4 (u32 (x + 1)).
Proof.
  intros x. apply put4_cong. rewrite unsigned_lit_wrap. unfold u32.
  rewrite (Zplus_mod (bv_swrap 32 x mod 2 ^ 64) 1), mod64_32, swrap32_mod, <- Zplus_mod.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* a branch condition as arithmetic: the kit's zify_cond, then the register literals *)
Ltac zc H :=
  zify_cond H;
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?v)] => rewrite (signed_lit v) in H by lia
  end;
  rewrite ?unsigned_lit_wrap in H.


(* two register literals that agree mod 2^64 are the same word *)
Lemma zbv_cong : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !unsigned_lit_wrap. exact H. Qed.

(* the byte an sb of a byte-valued register writes: the kit's cell machinery (Lib/Step.v cell_of_bytes) takes
   a one-element list, so a stack sb is rewritten to it and then absorbed by mem_after_store *)
Lemma le1_b8 : forall x, 0 <= x < 256 -> le1 (Z_to_bv 64 x) = [b8 x].
Proof.
  intros x Hx. unfold le1. rewrite unsigned_lit by lia.
  cbn [Z_to_le_bytes]. unfold b8.
  first [ reflexivity
        | f_equal; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
          change (bv_modulus 8) with 256; rewrite ?Z.mod_mod by lia; try reflexivity;
          Z.div_mod_to_equations; lia ].
Qed.

(* a byte of the frame buffer: pose the read, step the lbu, and name the value at8 l i *)
Ltac lbuf H k i :=
  lazymatch type of H with
  | bytes_at rsegs ?mm ?pp ?fr =>
      let R := fresh "RD" in
      pose proof (rd_sub mm pp fr k 1 H ltac:(lia) ltac:(lia)) as R;
      step; rewrite lbu_val by (apply length_sub; lia);
      rewrite (ble_sub1 fr k i eq_refl ltac:(lia)); clear R
  end.

Lemma at8_skipn0 : forall (l : list byte) (n : nat), at8 (skipn n l) 0 = at8 l n.
Proof.
  intros l n. unfold at8. f_equal.
  destruct (nth_error l n) as [x|] eqn:E.
  - assert (E2 : nth_error (skipn n l) 0 = Some x) by (rewrite nth_skipn, Nat.add_0_r; exact E).
    rewrite (nth_error_nth _ _ _ E), (nth_error_nth _ _ _ E2). reflexivity.
  - apply nth_error_None in E.
    rewrite (nth_overflow l) by lia.
    rewrite (nth_overflow (skipn n l)) by (rewrite length_skipn; lia). reflexivity.
Qed.

(* the keepalive test of :854, as the binary forms it: body[0] | ((ncmds & 0xff) ^ 1) is zero *)
Lemma ka_bits : forall b nc, 0 <= b < 256 -> 0 <= nc < 256 ->
  (Z.lor b (Z.lxor (Z.land nc 255) 1) =? 0) = (b =? 0) && (nc =? 1).
Proof.
  intros b nc Hb Hnc.
  replace (Z.land nc 255) with nc
    by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  destruct (Z.eqb_spec (Z.lor b (Z.lxor nc 1)) 0) as [E|E]; symmetry.
  - apply Z.lor_eq_0_iff in E. destruct E as [E1 E2]. apply (proj1 (Z.lxor_eq_0_iff _ _)) in E2.
    rewrite E1, E2. reflexivity.
  - apply andb_false_iff.
    destruct (Z.eqb_spec b 0) as [Eb|Nb]; [right | left; reflexivity].
    apply (proj2 (Z.eqb_neq _ _)). intros Enc. apply E. rewrite Eb, Enc, Z.lor_0_l. apply Z.lxor_nilpotent.
Qed.

(* ---- the keepalive flag as the binary forms it, 0x14904-0x14914: seqz of body[0] | ((ncmds & 0xff) ^ 1) ---- *)

Lemma io_lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
  intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
  assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  lia.
Qed.

Lemma io_ka_seqz : forall b nc, 0 <= b < 256 -> 0 <= nc < 256 ->
  v_sltiu (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 b))
             (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 nc)) 255)))
                                              1))))) 1
  = Z_to_bv 64 (b2z ((b =? 0) && (nc =? 1))).
Proof.
  intros b nc Hb Hnc.
  rewrite (unsigned_lit nc), (unsigned_lit b) by lia.
  pose proof (land_lt_pow2 nc 255 8 ltac:(lia) ltac:(lia)) as L1.
  rewrite (unsigned_lit (Z.land nc 255)) by lia.
  pose proof (io_lxor_lt_256 (Z.land nc 255) 1 ltac:(lia) ltac:(lia)) as L2.
  rewrite (unsigned_lit (Z.lxor (Z.land nc 255) 1)) by lia.
  pose proof (lor_lt_pow2 b (Z.lxor (Z.land nc 255) 1) 8 ltac:(lia) ltac:(lia)) as L3.
  rewrite v_sltiu_b2z, (unsigned_lit (Z.lor b (Z.lxor (Z.land nc 255) 1))) by lia.
  change (bv_wrap 64 1) with 1.
  rewrite <- (ka_bits b nc Hb Hnc).
  f_equal. destruct (Z.eqb_spec (Z.lor b (Z.lxor (Z.land nc 255) 1)) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (Z.lor b (Z.lxor (Z.land nc 255) 1) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Z.lor b (Z.lxor (Z.land nc 255) 1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E).
    reflexivity.
Qed.

(* ---- register literals: signed equality, a sign-extended uint32, an addiw counter ---- *)

Lemma io_eqb_slit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb.
  assert (K : forall z, -2^63 <= z < 2^63 -> bv_unsigned (Z_to_bv 64 z) = if z <? 0 then z + 2^64 else z).
  { intros z Hz. rewrite unsigned_lit_wrap. destruct (Z.ltb_spec z 0).
    - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
    - apply Z.mod_small. lia. }
  rewrite !K by assumption.
  destruct (Z.eqb_spec a b) as [->|N].
  - destruct (Z.ltb_spec b 0); rewrite !Z.eqb_refl; reflexivity.
  - replace (a =? b) with false by (symmetry; apply Z.eqb_neq; exact N).
    apply Z.eqb_neq. destruct (Z.ltb_spec a 0); destruct (Z.ltb_spec b 0); lia.
Qed.

Lemma io_swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma io_swrap32_mod64 : forall x, bv_swrap 32 (x mod 2^64) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite (Z.mod_eq x (2^64)) by lia.
  replace (x - 2^64 * (x / 2^64) + bv_half_modulus 32)
    with ((x + bv_half_modulus 32) + (- (2^32 * (x / 2^64))) * 2^32) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma io_sx32_small : forall d, -2^31 <= d < 2^31 -> sx32 (Z_to_bv 64 d) = Z_to_bv 64 d.
Proof.
  intros d Hd. unfold sx32. f_equal. rewrite unsigned_lit_wrap, io_swrap32_mod64.
  apply io_swrap32_small. exact Hd.
Qed.

(* 0x14740: bgeu a7,a1 with a1 = g_ncmd, an unsigned loaded by lw (sign-extended) *)
Lemma io_ltu_ncmd : forall s n, 0 <= s < 2^31 -> 0 <= n < 2^32 ->
  bv_ltu (Z_to_bv 64 s) (Z_to_bv 64 (bv_swrap 32 n)) = (s <? n).
Proof.
  intros s n Hs Hn. unfold bv_ltu. rewrite (unsigned_lit s) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  destruct (Z.ltb_spec s n) as [L|L]; [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

Lemma io_b2z_range : forall b, 0 <= b2z b <= 1.
Proof. intros []; cbn; lia. Qed.

(* 0x14778-0x1477c: seqz a1,a0; and a1,a1,s9 with a0 = g_raw, s9 = the keepalive flag *)
Lemma io_seqz_and : forall g (k : bool), -2^63 <= g < 2^63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 g) 1)) (bv_unsigned (Z_to_bv 64 (b2z k))))
  = Z_to_bv 64 (b2z (negb (truth g) && k)).
Proof.
  intros g k Hg. rewrite v_sltiu_b2z. f_equal.
  assert (E : (bv_unsigned (Z_to_bv 64 g) <? bv_wrap 64 1) = (g =? 0)).
  { rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    destruct (Z.eqb_spec g 0) as [->|N]; [reflexivity|].
    apply Z.ltb_ge. destruct (Z_lt_le_dec g 0).
    - rewrite <- (Z.mod_add g 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite E. unfold truth. rewrite negb_involutive.
  destruct (g =? 0); destruct k; reflexivity.
Qed.

(* 0x14754: addiw s4,s4,1 with s4 = the command count as the sign extension of a uint32 *)
Lemma io_addiw_sw : forall c,
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 c)) + 1)) = Z_to_bv 64 (bv_swrap 32 (u32 (c + 1))).
Proof.
  intros c. f_equal. unfold u32, bv_swrap, bv_wrap. rewrite unsigned_lit_wrap.
  change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma io_put8_congr : forall x y, x mod 2^64 = y mod 2^64 -> put 8 x = put 8 y.
Proof.
  intros x y H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 8 x 64) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 8 y 64) by (cbn; lia).
  rewrite H. reflexivity.
Qed.

(* ---- the command count loop of :859-862 (TCb.v cmds_loop) and the inlined tagged_of (:609-615) ---- *)

Lemma io_tof_keep : forall B b n B' t, tagged_of_m B b n = Some (B', t) ->
  B' = B /\ match t with Some s => 0 <= s < CMDS_MAX | None => True end.
Proof.
  intros B b n B' t H. unfold tagged_of_m in H.
  destruct (n <? 3); [inversion H; subst; split; [reflexivity | exact I]|].
  destruct (length b <? 1)%nat; [discriminate|].
  destruct (negb (at8 b 0 =? TAG)); [inversion H; subst; split; [reflexivity | exact I]|].
  destruct (length b <? 3)%nat; [discriminate|].
  destruct (Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) <? g_ncmd B) eqn:E5.
  - destruct (CMDS_MAX <=? Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7)) eqn:E6; [discriminate|].
    inversion H; subst. split; [reflexivity|].
    apply Z.leb_gt in E6. split; [|exact E6].
    apply (proj2 (Z.lor_nonneg _ _)). split; [apply at8_range|].
    rewrite Z.shiftl_nonneg. apply at8_range.
  - inversion H; subst. split; [reflexivity | exact I].
Qed.

Lemma io_tof_short : forall B b n, n < 3 -> tagged_of_m B b n = Some (B, None).
Proof. intros B b n H. unfold tagged_of_m. replace (n <? 3) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma io_tof_notag : forall B b n, 3 <= n -> (1 <= length b)%nat -> at8 b 0 <> TAG ->
  tagged_of_m B b n = Some (B, None).
Proof.
  intros B b n H L T. unfold tagged_of_m.
  replace (n <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (length b <? 1)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (at8 b 0 =? TAG) with false by (symmetry; apply Z.eqb_neq; exact T).
  reflexivity.
Qed.

Lemma io_tof_tag : forall B b n, 3 <= n -> (3 <= length b)%nat -> at8 b 0 = TAG ->
  tagged_of_m B b n =
    (if Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) <? g_ncmd B then
       (if CMDS_MAX <=? Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) then None
        else Some (B, Some (Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7))))
     else Some (B, None)).
Proof.
  intros B b n H L T. unfold tagged_of_m.
  replace (n <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (length b <? 1)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (at8 b 0 =? TAG) with true by (symmetry; apply Z.eqb_eq; exact T).
  replace (length b <? 3)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Lemma io_cl_range : forall fuel B body blen pos cmds c, 0 <= cmds < 2^32 ->
  cmds_loop fuel B body blen pos cmds = Some c -> 0 <= c < 2^32.
Proof.
  induction fuel as [|fuel IH]; intros B body blen pos cmds c Hc H; cbn in H; [discriminate|].
  destruct (pos <? blen); [|injection H as <-; exact Hc].
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos)) as [[B0 t]|]; [|discriminate].
  destruct t as [s|]; cbv beta iota in H;
    [ destruct (Cmd_len B s =? 0) | destruct (blen - pos =? 0) ]; try discriminate;
    (eapply IH; [|exact H]; unfold u32; apply Z.mod_pos_bound; lia).
Qed.

(* one round of the command count loop *)
Lemma io_cl_step : forall fuel B body blen pos cmds r, pos < blen ->
  cmds_loop (S fuel) B body blen pos cmds = Some r ->
  exists B0 t, tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos) = Some (B0, t) /\
    (match t with Some s => Cmd_len B s | None => blen - pos end) <> 0 /\
    cmds_loop fuel B body blen (pos + match t with Some s => Cmd_len B s | None => blen - pos end)
      (u32 (cmds + 1)) = Some r.
Proof.
  intros fuel B body blen pos cmds r Hp H. cbn [cmds_loop] in H.
  rewrite (proj2 (Z.ltb_lt pos blen) Hp) in H. cbv beta iota zeta in H.
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos)) as [[B0 t]|] eqn:E;
    cbv beta iota zeta in H; [|discriminate H].
  exists B0, t. split; [reflexivity|].
  destruct t as [s|]; cbv beta iota in H |- *;
    [ destruct (Cmd_len B s =? 0) eqn:Z0 | destruct (blen - pos =? 0) eqn:Z0 ]; try discriminate H;
    (split; [apply Z.eqb_neq; exact Z0 | exact H]).
Qed.

Lemma io_cl_end : forall fuel B body blen pos cmds r, blen <= pos ->
  cmds_loop fuel B body blen pos cmds = Some r -> r = cmds.
Proof.
  intros fuel B body blen pos cmds r Hp H. destruct fuel as [|fuel]; cbn [cmds_loop] in H; [discriminate H|].
  rewrite (proj2 (Z.ltb_ge pos blen) Hp) in H. injection H as <-. reflexivity.
Qed.

(* ---- check_latest_sent's display flag is an int (TCb.v latest_sent_loop, :641-642) ---- *)

Lemma io_land_pow2 : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= Z.land x y < 2 ^ n.
Proof.
  intros n x y Hn Hx.
  assert (NN : 0 <= Z.land x y) by (apply Z.land_nonneg; left; lia).
  assert (E : Z.land x y = Z.land x y mod 2 ^ n).
  { rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm x y), <- Z.land_assoc, Z.land_ones by lia.
    rewrite (Z.mod_small x) by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (Z.land x y) (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.

Lemma io_lor_neg : forall a b, a < 0 \/ b < 0 -> Z.lor a b < 0.
Proof.
  intros a b H. destruct (Z_lt_le_dec (Z.lor a b) 0) as [L|L]; [lia|].
  apply (proj1 (Z.lor_nonneg a b)) in L. lia.
Qed.

Lemma io_lnot_lor : forall a b, - Z.lor a b - 1 = Z.land (- a - 1) (- b - 1).
Proof.
  intros a b. apply Z.bits_inj'. intros n Hn.
  replace (- Z.lor a b - 1) with (Z.lnot (Z.lor a b)) by (unfold Z.lnot; lia).
  replace (- a - 1) with (Z.lnot a) by (unfold Z.lnot; lia).
  replace (- b - 1) with (Z.lnot b) by (unfold Z.lnot; lia).
  rewrite Z.land_spec, !Z.lnot_spec by lia. rewrite Z.lor_spec. apply negb_orb.
Qed.

Lemma io_lor_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 -> -2^31 <= Z.lor a b < 2^31.
Proof.
  intros a b Ha Hb.
  destruct (Z_le_gt_dec 0 a) as [A|A]; destruct (Z_le_gt_dec 0 b) as [B|B].
  - pose proof (lor_lt_pow2 a b 31 ltac:(lia) ltac:(lia)). lia.
  - pose proof (io_lor_neg a b ltac:(lia)).
    pose proof (io_lnot_lor a b) as D. rewrite Z.land_comm in D.
    pose proof (io_land_pow2 31 (- b - 1) (- a - 1) ltac:(lia) ltac:(lia)). lia.
  - pose proof (io_lor_neg a b ltac:(lia)).
    pose proof (io_lnot_lor a b) as D.
    pose proof (io_land_pow2 31 (- a - 1) (- b - 1) ltac:(lia) ltac:(lia)). lia.
  - pose proof (io_lor_neg a b ltac:(lia)).
    pose proof (io_lnot_lor a b) as D.
    pose proof (io_land_pow2 31 (- a - 1) (- b - 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma io_lsl_disp : forall fuel B body len pos disp B' d, -2^31 <= disp < 2^31 ->
  latest_sent_loop fuel B body len pos disp = Some (B', d) -> -2^31 <= d < 2^31.
Proof.
  induction fuel as [|fuel IH]; intros B body len pos disp B' d Hd H; cbn in H; [discriminate|].
  destruct (pos <? len) eqn:E1; [|inversion H; subst; exact Hd].
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (len - pos)) as [[B0 t]|] eqn:E2; [|discriminate].
  destruct t as [s|]; [|discriminate].
  destruct (negb (Cmd_st B s =? PENDING) || (len - pos <? Cmd_len B s)
            || negb (beq_bytes (firstn (Z.to_nat (Cmd_len B s)) (skipn (Z.to_nat pos) body))
                      (sub B (A_Cmd_bytes s) (Z.to_nat (Cmd_len B s))))); [discriminate|].
  destruct (q_remove_m (set_Cmd_st B s SENT) s) as [[B2 u]|] eqn:E4; [|discriminate].
  eapply IH; [|exact H]. apply io_lor_s32; [exact Hd | apply s32_range].
Qed.

Lemma io_cls_disp : forall B body len B' disp, check_latest_sent_m B body len = Some (B', disp) ->
  -2^31 <= disp < 2^31.
Proof.
  intros B body len B' disp H. unfold check_latest_sent_m in H.
  eapply io_lsl_disp; [|exact H]. lia.
Qed.

(* ---- the frame's bytes across check_latest_sent ---- *)

Lemma io_ba_skipn : forall m a bs k, 0 <= k -> (Z.to_nat k <= length bs)%nat ->
  bytes_at rsegs m a bs -> bytes_at rsegs m (a + k) (skipn (Z.to_nat k) bs).
Proof.
  intros m a bs k Hk Hl H.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  replace (a + Z.of_nat (Z.to_nat k)) with (a + k) in H by lia. exact H.
Qed.

Lemma io_ba_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. tauto.
Qed.

Lemma io_ba_det : forall m a u v, bytes_at rsegs m a u -> bytes_at rsegs m a v -> length u = length v -> u = v.
Proof.
  intros m a u v (_ & _ & Hu) (_ & _ & Hv) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length u)) as [Hi|Hi].
  - rewrite <- Hu by lia. rewrite <- Hv by lia. reflexivity.
  - rewrite (proj2 (nth_error_None u i)) by lia. rewrite (proj2 (nth_error_None v i)) by lia. reflexivity.
Qed.

(* After check_latest_sent, which writes the world at and above g_cmd: the frame's bytes are back, because they lie
   off the world and off the callee's footprint, or in g_s (io_send_frame_at), below g_cmd, which the callee keeps
   (io_send_keep.v cls_keep). *)
Lemma io_frame_back : forall (m0 m1 : word -> option byte) (B0 B1 : list byte) (p : Z) (frame : list byte)
    (W : list ivl),
  bytes_at rsegs m0 p frame -> wmem rsegs m0 B0 -> wmem rsegs m1 B1 ->
  (forall (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= OFF_g_cmd -> sub B1 k n = sub B0 k n) ->
  munch W m0 m1 ->
  ((p + Z.of_nat (length frame) <= 206736 \/ 206736 + 65616 <= p) -> disjoint_from W p (Z.of_nat (length frame))) ->
  (p + Z.of_nat (length frame) <= 206736 \/ 206736 + 65616 <= p) \/
    206736 + 1648 <= p /\ p + Z.of_nat (length frame) <= 206736 + 1648 + 18264 ->
  bytes_at rsegs m1 p frame.
Proof.
  intros m0 m1 B0 B1 p frame W BF W0 W1 KS MU DJ AT.
  destruct AT as [A|A].
  - eapply bytes_at_transport; [exact BF | exact MU | exact (DJ A)].
  - pose proof (wm_len rsegs W_BASE_PLAIN m0 B0 W0) as L0.
    set (k := p - 206736).
    assert (S0 : bytes_at rsegs m0 p (sub B0 k (length frame))).
    { apply (wm_src rsegs W_BASE_PLAIN m0 B0 k (length frame) p W0);
        [ unfold k, W_BASE_PLAIN; lia | unfold k; lia | unfold k, W_LEN; lia ]. }
    assert (E0 : frame = sub B0 k (length frame)).
    { apply (io_ba_det m0 p); [exact BF | exact S0 |].
      rewrite length_sub; [reflexivity | unfold k; lia | rewrite L0; unfold k, W_LEN; lia]. }
    assert (E1 : sub B1 k (length frame) = sub B0 k (length frame)) by (apply KS; unfold k, OFF_g_cmd; lia).
    rewrite E0, <- E1.
    apply (wm_src rsegs W_BASE_PLAIN m1 B1 k (length frame) p W1);
      [ unfold k, W_BASE_PLAIN; lia | unfold k; lia | unfold k, W_LEN; lia ].
Qed.

(* ---- tactics of the DATA arm ---- *)

(* after a callee: carry the walk's facts to the new memory, then drop the old memory's mem_inv and name *)
Ltac io_after_call MUc WMc :=
  lazymatch type of MUc with
  | munch _ ?mv ?mw =>
      transport_after_call rsegs mv mw MUc WMc; clear MUc WMc;
      try (match goal with H : mem_inv rsegs mv |- _ => clear H end);
      try clear mv
  end.

(* two register values that agree as numbers *)
Ltac io_regeq := first [ reflexivity | (f_equal; lia) | (f_equal; rewrite ?unsigned_lit by lia; lia) | word_eq_tac ].

(* reads of a world through writes elsewhere; the side conditions are offsets and lengths *)
Ltac io_lside := rewrite ?length_put; first [ lia | (rewrite length_upd; [ io_lside | lia | io_lside ]) ].
Ltac io_wread := repeat first [ rewrite s32_at_upd_out by io_lside | rewrite u_at_upd_out by io_lside ].

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

(* ---- the DATA arm from 0x146e8 (fuzz_transport.c:857-889), with the keepalive flag of :854 in s9 ---- *)
Lemma io_send_data :
  forall (CIN : check_inflight_new_contract) (CLF : check_latest_frame_contract)
         (CKD : check_keepalive_due_contract) (CLS : check_latest_sent_contract)
         (CLD : check_latest_display_contract) (QQ : machine_state -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m mU : word -> option byte) (lo : Z) (B B' : list byte) (p : Z) (frame j0 jD : list byte)
         (cs : list cell) (kaV : bool),
    0 < p -> bytes_at rsegs mU p frame ->
    (p + Z.of_nat (length frame) <= 206736 \/ 206736 + 65616 <= p) \/
      206736 + 1648 <= p /\ p + Z.of_nat (length frame) <= 206736 + 1648 + 18264 ->
    p + Z.of_nat (length frame) <= bv_unsigned sp - 304 \/ bv_unsigned sp <= p ->
    bv_unsigned sp mod 16 = 0 -> 0 <= lo -> lo + 304 <= bv_unsigned sp ->
    206736 + 65616 <= bv_unsigned sp - 304 ->
    sf_send (rf frame) = fr_send frame -> sf_cmd (rf frame) = fr_cmd frame ->
    0 <= fr_ncmds frame < 256 -> 0 <= fr_body_len frame < 65536 ->
    30 + fr_body_len frame <= Z.of_nat (length frame) ->
    (let* (B3, _) := check_inflight_new_m (set_g_fail_next B 0) in
     let* cmds := (if negb (truth (g_raw B3)) && negb kaV
                   then cmds_loop (S (Z.to_nat (fr_body_len frame))) B3 (skipn (Z.to_nat 30) frame)
                          (fr_body_len frame) 0 0
                   else Some (fr_ncmds frame)) in
     let* (B4, _) := check_latest_frame_m B3 frame cmds in
     let* (B6, _) :=
       (if negb (truth (g_raw (set_g_last_counter (set_M_host_counter B4 (sf_send (rf frame)))
                                 (sf_send (rf frame))))) && kaV
        then
          (let* (Bk, _) := check_keepalive_due_m (set_g_last_counter (set_M_host_counter B4 (sf_send (rf frame)))
                                                    (sf_send (rf frame))) in
           if u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk)) <=?
              g_now (set_M_next_ka Bk (u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk))))
           then Some (set_M_next_ka (set_M_next_ka Bk (u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk))))
                        (u64 (g_now (set_M_next_ka Bk (u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk)))) +
                              h_ms_m (Cfg_keepalive_ms
                                        (set_M_next_ka Bk (u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk))))))),
                      tt)
           else Some (set_M_next_ka Bk (u64 (M_next_ka Bk + h_ms_m (Cfg_keepalive_ms Bk))), tt))
        else if negb (truth (g_raw (set_g_last_counter (set_M_host_counter B4 (sf_send (rf frame)))
                                      (sf_send (rf frame)))))
        then
          (let* (Bs, disp) := check_latest_sent_m (set_g_last_counter (set_M_host_counter B4 (sf_send (rf frame)))
                                                     (sf_send (rf frame)))
                                (firstn (Z.to_nat (fr_body_len frame)) (skipn (Z.to_nat 30) frame))
                                (fr_body_len frame) in
           if truth disp then
             (let* (Bd, _) := check_latest_display_m Bs in
              Some (set_M_last_display (set_M_display_sent Bd 1) (g_now Bd), tt))
           else Some (Bs, tt))
        else Some (set_g_last_counter (set_M_host_counter B4 (sf_send (rf frame))) (sf_send (rf frame)), tt)) in
     Some (set_M_fly_frame
             (set_M_fly_len
                (set_M_fly_sent
                   (set_M_fly_retries
                      (set_M_fly_counter (set_M_fly_cmd (set_M_fly_on B6 1) (fr_cmd frame)) (sf_send (rf frame)))
                      0)
                   (g_now B6))
                (if Z.of_nat (length frame) <? SPEC_MAX_FRAME then Z.of_nat (length frame) else SPEC_MAX_FRAME))
             (firstn (Z.to_nat (if Z.of_nat (length frame) <? SPEC_MAX_FRAME then Z.of_nat (length frame)
                                else SPEC_MAX_FRAME)) frame),
           tt)) = Some (B', tt) ->
    munch [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mU ->
    wmono rsegs m mU -> mem_inv rsegs mU -> stk rsegs mU lo (bv_unsigned sp + -192) ->
    wmem rsegs mU (set_g_fail_next B 0) ->
    rw_cells rsegs mU (bv_unsigned sp + -192) [CB 12 j0] ->
    rw_cells rsegs mU (bv_unsigned sp + -180) [CB 4 jD] ->
    rw_cells rsegs mU (bv_unsigned sp + -176) cs -> cells_size cs = 80%nat ->
    bytes_at rsegs mU (bv_unsigned sp + -176) (sf_bytes p (rf frame)) ->
    (forall mm : word -> option byte,
       bytes_at rsegs mm (bv_unsigned sp + -176) (sf_bytes p (rf frame)) ->
       sframe_at mm (bv_unsigned sp + -176) p (rf frame)) ->
    rw_cells rsegs mU (bv_unsigned sp + -96)
      [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall (mm : word -> option byte) (cs0 : list cell) (jd Bx : list byte) (flen : Z)
            (vra vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs9 vs10 vt3 vt4 vt5 vt6 : word),
       munch [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mm ->
       wmono rsegs m mm -> mem_inv rsegs mm -> stk rsegs mm lo (bv_unsigned sp + -192) ->
       wmem rsegs mm Bx ->
       bytes_at rsegs mm p frame ->
       flen = (if Z.of_nat (length frame) <? 1514 then Z.of_nat (length frame) else 1514) ->
       B' = set_M_fly_frame
              (set_M_fly_len
                 (set_M_fly_sent
                    (set_M_fly_retries
                       (set_M_fly_counter (set_M_fly_cmd (set_M_fly_on Bx 1) (sf_cmd (rf frame)))
                          (sf_send (rf frame))) 0) (g_now Bx)) flen)
              (firstn (Z.to_nat flen) frame) ->
       rw_cells rsegs mm (bv_unsigned sp + -192) [CB 12 j0] ->
       rw_cells rsegs mm (bv_unsigned sp + -180) [CB 4 jd] ->
       rw_cells rsegs mm (bv_unsigned sp + -176) cs0 -> cells_size cs0 = 80%nat ->
       rw_cells rsegs mm (bv_unsigned sp + -96)
         [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       evt rsegs QQ
         (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp vt0 vt1 vt2
                   (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
                   va0 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4
                   (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704)
                   (Z_to_bv 64 (sf_send (rf frame))) (Z_to_bv 64 (sf_cmd (rf frame)))
                   vs9 vs10 s11 vt3 vt4 vt5 vt6)
             F (Z_to_bv 64 83944) fc None mm (seg_rom rsegs))) ->
    forall (vs9 vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 : word),
      vs9 = Z_to_bv 64 (b2z kaV) ->
      evt rsegs QQ
        (MS (mkR (Z_to_bv 64 83596) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp vt0 vt1 vt2
                  (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
                  va0 va1 va2 va3 va4 va5 va6 va7
                  (Z_to_bv 64 (p + 30)) (Z_to_bv 64 (fr_body_len frame)) (Z_to_bv 64 (fr_ncmds frame))
                  (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704) (Z_to_bv 64 (fr_send frame))
                  (Z_to_bv 64 (fr_cmd frame)) vs9 (Z_to_bv 64 (fr_cmd frame)) s11
                  vt3 vt4 vt5 vt6)
            F (Z_to_bv 64 83688) fc None mU (seg_rom rsegs)).
Proof.
  intros CIN CLF CKD CLS CLD QQ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mU lo B B' p frame
    j0 jD cs kaV Hp HFR HFA HOW Hsp Hlo0 HLO HWS' Fsend Fcmd RNC Rbl BL30 HSW
    MU WMo MIU STU WMU FR0 FRD POST FRFsz HSFB SFANY FRS FLY
    vs9 vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 Hvs9.
  subst vs9.
  unfold check_inflight_new_contract, check_inflight_new_ENTRY, check_inflight_new_FRAME in CIN.
  unfold check_latest_frame_contract, check_latest_frame_ENTRY, check_latest_frame_FRAME in CLF.
  unfold check_keepalive_due_contract, check_keepalive_due_ENTRY, check_keepalive_due_FRAME in CKD.
  unfold check_latest_sent_contract, check_latest_sent_ENTRY, check_latest_sent_FRAME in CLS.
  unfold check_latest_display_contract, check_latest_display_ENTRY, check_latest_display_FRAME in CLD.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bytes_at_bound rsegs mU p frame HFR) as Bfr.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192)
    by (rewrite unsigned_lit by lia; reflexivity).
  wk_facts.
  (* ---- 146e0: jal check_inflight_new (:857); it keeps the world ---- *)
  destruct (check_inflight_new_m (set_g_fail_next B 0)) as [[B3 []]|] eqn:CINm; [|discriminate HSW].
  cbv beta iota in HSW.
  step.
  eapply evt_cut.
  { eapply CIN;
      [ exact WMU | exact CINm
      | rewrite ESP; Z.div_mod_to_equations; lia
      | rewrite ESP; exact STU | rewrite ESP; lia
      | unfold w_off_stack; rewrite ESP; lia | exact MIU ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 &
              Eq4 & MU4 & WM4 & MI4 & ST4 & EB3 & WMEM4).
  subst ms'. rewrite ESP in MU4, ST4. subst B3. clear WMU STU.
  io_after_call MU4 WM4.
  rewrite (ret_pc_even 83692) by (first [lia | reflexivity]).
  (* the model: the command count, check_latest_frame, the world B6 that goes in flight *)
  lazymatch type of HSW with
  | match ?X with Some _ => _ | None => _ end = _ => destruct X as [cmdsM|] eqn:CMDm; [|discriminate HSW]
  end.
  cbv beta iota in HSW.
  destruct (check_latest_frame_m (set_g_fail_next B 0) frame cmdsM) as [[B4 []]|] eqn:CLFm; [|discriminate HSW].
  cbv beta iota in HSW.
  lazymatch type of HSW with
  | match ?X with Some _ => _ | None => _ end = _ => destruct X as [[B6 []]|] eqn:B6m; [|discriminate HSW]
  end.
  cbv beta iota in HSW.
  injection HSW as EB'.
  assert (CMR : 0 <= cmdsM < 2 ^ 32).
  { revert CMDm. destruct (negb (truth (g_raw (set_g_fail_next B 0))) && negb kaV); intros CMDm.
    - eapply io_cl_range; [|exact CMDm]. lia.
    - injection CMDm as <-. lia. }
  (* 146e4: lw a0,4(s6) -- g_raw *)
  step.
  change (s32_at (set_g_fail_next B 0) 64972) with (g_raw (set_g_fail_next B 0)).
  pose proof (s32_range (set_g_fail_next B 0) OFF_g_raw) as RGR.
  change (s32_at (set_g_fail_next B 0) OFF_g_raw) with (g_raw (set_g_fail_next B 0)) in RGR.
  pose proof (wm_len rsegs W_BASE_PLAIN m4 _ WMEM4) as LB0.
  assert (LB0Z : Z.of_nat (length (set_g_fail_next B 0)) = 65616) by (rewrite LB0; vm_compute; reflexivity).
  (* ---- 14754: check_latest_frame (&f, cmds) (:866), then :867-889 ---- *)
  assert (CONT : forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word),
    xs4 = Z_to_bv 64 (bv_swrap 32 cmdsM) ->
    evt rsegs QQ
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp xt0 xt1 xt2
               (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 (p + 30)) (Z_to_bv 64 (fr_body_len frame)) xs4
               (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704) (Z_to_bv 64 (fr_send frame))
               (Z_to_bv 64 (fr_cmd frame)) (Z_to_bv 64 (b2z kaV)) (Z_to_bv 64 (fr_cmd frame)) s11
               xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 83804) fc None m4 (seg_rom rsegs))).
  { intros xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 ES4. subst xs4.
    (* 14754: addi a0,sp,16 ; 14758: mv a1,s4 ; 1475c: jal check_latest_frame *)
    do 3 step.
    eapply evt_cut.
    { eapply CLF with (fp := bv_unsigned sp + -176) (fa := p) (frame := frame) (cmds := cmdsM);
        [ io_regeq | reflexivity | exact CMR | apply SFANY; exact HSFB
        | unfold off_window; rewrite ESP; lia
        | exact WMEM4 | exact CLFm
        | rewrite ESP; Z.div_mod_to_equations; lia | rewrite ESP; exact ST4 | rewrite ESP; lia
        | unfold w_off_stack; rewrite ESP; lia | exact MI4 ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
                Eq5 & MU5 & WM5 & MI5 & ST5 & EB4 & WMEM5).
    subst ms'. rewrite ESP in MU5, ST5. subst B4. clear WMEM4 ST4.
    io_after_call MU5 WM5.
    rewrite (ret_pc_even 83816) by (first [lia | reflexivity]).
    (* 14760: lw a0,4(s6) -- g_raw *)
    step.
    change (s32_at (set_g_fail_next B 0) 64972) with (g_raw (set_g_fail_next B 0)).
    (* 14764: auipc a1 ; 14768: addi s4,a1,44 -- s4 = &M *)
    do 2 step.
    (* 1476c: sw s7,84(s4) -- M.host_counter (:867) *)
    step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WH end.
    rewrite <- Fsend in WH.
    change (upd (set_g_fail_next B 0) 84 (put 4 (sf_send (rf frame))))
      with (set_M_host_counter (set_g_fail_next B 0) (sf_send (rf frame))) in WH.
    (* 14770: seqz a1,a0 ; 14774: and a1,a1,s9 *)
    do 2 step.
    rewrite io_seqz_and by lia.
    (* 14778: sw s7,8(s6) -- g_last_counter (:868) *)
    step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WC end.
    rewrite <- Fsend in WC.
    change (upd (set_M_host_counter (set_g_fail_next B 0) (sf_send (rf frame))) 64976 (put 4 (sf_send (rf frame))))
      with (set_g_last_counter (set_M_host_counter (set_g_fail_next B 0) (sf_send (rf frame))) (sf_send (rf frame)))
      in WC.
    assert (GR5 : g_raw (set_g_last_counter (set_M_host_counter (set_g_fail_next B 0) (sf_send (rf frame)))
                           (sf_send (rf frame))) = g_raw (set_g_fail_next B 0)).
    { unfold g_raw, set_g_last_counter, set_M_host_counter, OFF_g_raw, OFF_g_last_counter, A_M_host_counter, OFF_M.
      io_wread. reflexivity. }
    set (B5 := set_g_last_counter (set_M_host_counter (set_g_fail_next B 0) (sf_send (rf frame)))
                 (sf_send (rf frame))) in *.
    rewrite GR5 in B6m.
    pose proof (wm_len rsegs W_BASE_PLAIN _ _ WC) as LB5.
    assert (LB5Z : Z.of_nat (length B5) = 65616) by (rewrite LB5; vm_compute; reflexivity).
    (* 1477c: beqz a1,147b0 *)
    step.
    rewrite eqb_lit by (pose proof (io_b2z_range (negb (truth (g_raw (set_g_fail_next B 0))) && kaV)); lia).
    destruct (negb (truth (g_raw (set_g_fail_next B 0))) && kaV) eqn:KC; try rewrite KC in B6m.
    - (* ---- a keepalive (:869-873): check_keepalive_due, M.next_ka ---- *)
      change (b2z true =? 0) with false. cbv iota.
      cbv beta iota in B6m.
      destruct (check_keepalive_due_m B5) as [[Bk []]|] eqn:CKDm; [|discriminate B6m].
      cbv beta iota in B6m.
      (* 14780: jal check_keepalive_due (:870) *)
      step.
      eapply evt_cut.
      { eapply CKD;
          [ exact WC | exact CKDm | rewrite ESP; Z.div_mod_to_equations; lia | rewrite ESP; eassumption
          | rewrite ESP; lia | unfold w_off_stack; rewrite ESP; lia | eassumption ]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 &
                  Eq6 & MU6 & WM6 & MI6 & ST6 & EBk & WMEM6).
      subst ms'. rewrite ESP in MU6, ST6. subst Bk. clear WC.
      io_after_call MU6 WM6.
      rewrite (ret_pc_even 83852) by (first [lia | reflexivity]).
      (* 14784: lwu a1,80(s6) -- Cfg.keepalive_ms ; 14788: ld a2,48(s4) -- M.next_ka ; 1478c: ld a0,32(s6) *)
      step. change (u_at B5 65048 4) with (Cfg_keepalive_ms B5).
      step. change (u_at B5 48 8) with (M_next_ka B5).
      step. change (u_at B5 65000 8) with (g_now B5).
      pose proof (u_at_range B5 65048 4) as RK0. change (u_at B5 65048 4) with (Cfg_keepalive_ms B5) in RK0.
      change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RK0.
      pose proof (u_at_range B5 48 8) as RN0. change (u_at B5 48 8) with (M_next_ka B5) in RN0.
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RN0.
      pose proof (u_at_range B5 65000 8) as RG0. change (u_at B5 65000 8) with (g_now B5) in RG0.
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RG0.
      (* 14790: li a3,1000 ; 14794: mul a1,a1,a3 *)
      do 2 step.
      rewrite ?(unsigned_lit (Cfg_keepalive_ms B5)), ?(unsigned_lit 1000) by lia.
      assert (GN : forall nv, g_now (set_M_next_ka B5 nv) = g_now B5).
      { intros nv. unfold g_now, set_M_next_ka, A_M_next_ka, OFF_M, OFF_g_now.
        rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia]. }
      assert (CK : forall nv, Cfg_keepalive_ms (set_M_next_ka B5 nv) = Cfg_keepalive_ms B5).
      { intros nv. unfold Cfg_keepalive_ms, set_M_next_ka, A_M_next_ka, OFF_M, A_Cfg_keepalive_ms, OFF_g_cfg.
        rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia]. }
      rewrite GN, CK in B6m.
      set (nk := u64 (M_next_ka B5 + h_ms_m (Cfg_keepalive_ms B5))) in *.
      assert (Rnk : 0 <= nk < 2 ^ 64) by (unfold nk, u64; apply Z.mod_pos_bound; lia).
      (* 14798: add a2,a1,a2 ; 1479c: sd a2,48(s4) -- M.next_ka (:871) *)
      step. step.
      lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WK end.
      lazymatch type of WK with context [upd B5 48 (put 8 ?V)] =>
        replace (put 8 V) with (put 8 nk) in WK
          by (symmetry; apply io_put8_congr; unfold nk, h_ms_m, u64; rewrite ?unsigned_lit_wrap;
              Z.div_mod_to_equations; lia) end.
      change (upd B5 48 (put 8 nk)) with (set_M_next_ka B5 nk) in WK.
      (* 147a0: bltu a0,a2,147e0 *)
      step.
      lazymatch goal with |- context [bv_ltu (Z_to_bv 64 (g_now B5)) ?y] =>
        replace y with (Z_to_bv 64 nk)
          by (apply bv_eq; rewrite ?unsigned_lit_wrap; unfold nk, h_ms_m, u64; Z.div_mod_to_equations; lia) end.
      rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (g_now B5) nk) as [LTn|GEn]; cbv iota.
      + (* M.next_ka is ahead of g_now: the frame in flight *)
        replace (nk <=? g_now B5) with false in B6m by (symmetry; apply Z.leb_gt; lia).
        cbv beta iota in B6m. injection B6m as <-.
        rewrite <- Fsend, <- Fcmd.
        eapply FLY;
          [ exact MU | exact WMo | eassumption | eassumption | exact WK | exact HFR | reflexivity
          | rewrite <- EB', Fcmd; reflexivity
          | exact FR0 | exact FRD | exact POST | exact FRFsz | exact FRS ].
      + (* :872-873: M.next_ka = g_now + keepalive *)
        replace (nk <=? g_now B5) with true in B6m by (symmetry; apply Z.leb_le; lia).
        cbv beta iota in B6m. injection B6m as <-.
        (* 147a4: add a0,a0,a1 ; 147a8: sd a0,48(s4) *)
        step. step.
        lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WK2 end.
        lazymatch type of WK2 with context [upd (set_M_next_ka B5 nk) 48 (put 8 ?V)] =>
          replace (put 8 V) with (put 8 (u64 (g_now B5 + h_ms_m (Cfg_keepalive_ms B5)))) in WK2
            by (symmetry; apply io_put8_congr; unfold h_ms_m, u64; rewrite ?unsigned_lit_wrap;
                Z.div_mod_to_equations; lia) end.
        change (upd (set_M_next_ka B5 nk) 48 (put 8 (u64 (g_now B5 + h_ms_m (Cfg_keepalive_ms B5)))))
          with (set_M_next_ka (set_M_next_ka B5 nk) (u64 (g_now B5 + h_ms_m (Cfg_keepalive_ms B5)))) in WK2.
        (* 147ac: j 147e0 *)
        step.
        rewrite <- Fsend, <- Fcmd.
        eapply FLY;
          [ exact MU | exact WMo | eassumption | eassumption | exact WK2 | exact HFR | reflexivity
          | rewrite <- EB', Fcmd; reflexivity
          | exact FR0 | exact FRD | exact POST | exact FRFsz | exact FRS ].
    - change (b2z false =? 0) with true. cbv iota.
      cbv beta iota in B6m.
      (* 147b0: bnez a0,147e0 -- g_raw (:874) *)
      step.
      rewrite io_eqb_slit by lia.
      destruct (Z.eqb_spec (g_raw (set_g_fail_next B 0)) 0) as [G0|G1]; cbv beta iota delta [negb].
      2: { (* raw: nothing more *)
           replace (truth (g_raw (set_g_fail_next B 0))) with true in B6m
             by (unfold truth; symmetry; apply negb_true_iff, Z.eqb_neq; exact G1).
           cbv beta iota delta [negb] in B6m. injection B6m as <-.
           rewrite <- Fsend, <- Fcmd.
           eapply FLY;
             [ exact MU | exact WMo | eassumption | eassumption | exact WC | exact HFR | reflexivity
             | rewrite <- EB', Fcmd; reflexivity
             | exact FR0 | exact FRD | exact POST | exact FRFsz | exact FRS ]. }
      replace (truth (g_raw (set_g_fail_next B 0))) with false in B6m by (unfold truth; rewrite G0; reflexivity).
      cbv beta iota delta [negb] in B6m.
      destruct (check_latest_sent_m B5 (firstn (Z.to_nat (fr_body_len frame)) (skipn (Z.to_nat 30) frame))
                  (fr_body_len frame)) as [[Bs disp]|] eqn:CLSm; [|discriminate B6m].
      cbv beta iota in B6m.
      destruct (cls_keep _ _ _ _ _ CLSm LB5) as [KL KS].
      (* 147b4: addi a2,sp,12 ; 147b8: mv a0,s2 ; 147bc: mv a1,s3 ; 147c0: jal check_latest_sent (:875) *)
      do 4 step.
      eapply evt_cut.
      { eapply CLS with (bp := p + 30) (len := fr_body_len frame) (dp := bv_unsigned sp + -180)
          (body := firstn (Z.to_nat (fr_body_len frame)) (skipn (Z.to_nat 30) frame)) (junk := jD)
          (B := B5) (B' := Bs) (disp := disp);
          [ reflexivity | reflexivity | io_regeq | lia
          | apply io_ba_firstn; apply (io_ba_skipn _ p frame 30); [lia | lia | exact HFR]
          | rewrite length_firstn, length_skipn; lia
          | unfold W_BASE_PLAIN, OFF_g_cmd, W_LEN; lia
          | unfold off_window; rewrite ESP; lia
          | Z.div_mod_to_equations; lia | exact FRD | unfold off_world, W_BASE_PLAIN, W_LEN; lia
          | unfold off_window; rewrite ESP; lia | lia | exact WC | exact CLSm
          | rewrite ESP; Z.div_mod_to_equations; lia | rewrite ESP; eassumption | rewrite ESP; lia
          | unfold w_off_stack; rewrite ESP; lia | eassumption ]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 &
                  Eq6 & MU6 & WM6 & MI6 & ST6 & DSP & WMEM6).
      subst ms'. rewrite ESP in MU6, ST6.
      assert (HFR6 : bytes_at rsegs m6 p frame).
      { eapply (io_frame_back _ m6 B5 Bs p frame);
          [ exact HFR | exact WC | exact WMEM6 | exact KS | exact MU6
          | intros HA; cbn [disjoint_from]; repeat split; lia | exact HFA ]. }
      io_after_call MU6 WM6.
      rewrite (ret_pc_even 83916) by (first [lia | reflexivity]).
      (* 147c4: lw a0,12(sp) -- display *)
      step.
      pose proof (io_cls_disp _ _ _ _ _ CLSm) as RD.
      rewrite ?io_sx32_small by lia.
      (* 147c8: beqz a0,147e0 (:876) *)
      step.
      rewrite io_eqb_slit by lia.
      destruct (rw_cells_forget _ _ _ _ DSP) as [jd DSPf]. cbn [cells_size csize] in DSPf.
      destruct (Z.eqb_spec disp 0) as [D0|D1]; cbv iota.
      + (* no display flag: the frame in flight *)
        replace (truth disp) with false in B6m by (unfold truth; rewrite D0; reflexivity).
        cbv beta iota in B6m. injection B6m as <-.
        rewrite <- Fsend, <- Fcmd.
        eapply FLY;
          [ exact MU | exact WMo | eassumption | exact ST6 | exact WMEM6 | exact HFR6 | reflexivity
          | rewrite <- EB', Fcmd; reflexivity
          | exact FR0 | exact DSPf | exact POST | exact FRFsz | exact FRS ].
      + (* :877-879: check_latest_display, M.last_display, M.display_sent *)
        replace (truth disp) with true in B6m
          by (unfold truth; symmetry; apply negb_true_iff, Z.eqb_neq; exact D1).
        cbv beta iota in B6m.
        destruct (check_latest_display_m Bs) as [[Bd []]|] eqn:CLDm; [|discriminate B6m].
        cbv beta iota in B6m.
        (* 147cc: jal check_latest_display *)
        step.
        eapply evt_cut.
        { eapply CLD;
            [ exact WMEM6 | exact CLDm | rewrite ESP; Z.div_mod_to_equations; lia | rewrite ESP; exact ST6
            | rewrite ESP; lia | unfold w_off_stack; rewrite ESP; lia | eassumption ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 &
                    Eq7 & MU7 & WM7 & MI7 & ST7 & EBd & WMEM7).
        subst ms'. rewrite ESP in MU7, ST7. subst Bd. clear WMEM6 ST6.
        io_after_call MU7 WM7.
        rewrite (ret_pc_even 83928) by (first [lia | reflexivity]).
        pose proof (wm_len rsegs W_BASE_PLAIN _ _ WMEM7) as LBs.
        assert (LBsZ : Z.of_nat (length Bs) = 65616) by (rewrite LBs; vm_compute; reflexivity).
        injection B6m as <-.
        (* 147d0: ld a0,32(s6) -- g_now *)
        step. change (u_at Bs 65000 8) with (g_now Bs).
        (* 147d4: li a1,1 ; 147d8: sd a0,64(s4) -- M.last_display ; 147dc: sw a1,72(s4) -- M.display_sent *)
        step. step. step.
        lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WD end.
        replace (upd (upd Bs 64 (put 8 (g_now Bs))) 72 (put 4 1))
          with (set_M_last_display (set_M_display_sent Bs 1) (g_now Bs)) in WD
          by (unfold set_M_last_display, set_M_display_sent, A_M_last_display, A_M_display_sent, OFF_M;
              symmetry; apply upd_upd_comm; rewrite ?length_put; lia).
        rewrite <- Fsend, <- Fcmd.
        eapply FLY;
          [ exact MU | exact WMo | eassumption | eassumption | exact WD | exact HFR6 | reflexivity
          | rewrite <- EB', Fcmd; reflexivity
          | exact FR0 | exact DSPf | exact POST | exact FRFsz | exact FRS ]. }
  (* ---- 146e8: bnez a0,14754 -- g_raw: cmds = f.ncmds (:863-865) ---- *)
  step.
  rewrite io_eqb_slit by lia.
  destruct (Z.eqb_spec (g_raw (set_g_fail_next B 0)) 0) as [GR0|GR1]; cbv beta iota delta [negb].
  2: { assert (TG : truth (g_raw (set_g_fail_next B 0)) = true)
         by (unfold truth; apply negb_true_iff, Z.eqb_neq; exact GR1).
       rewrite TG in CMDm. cbv beta iota delta [negb andb] in CMDm. injection CMDm as CM.
       eapply CONT. rewrite <- CM, io_swrap32_small by lia. reflexivity. }
  assert (TG : truth (g_raw (set_g_fail_next B 0)) = false) by (unfold truth; rewrite GR0; reflexivity).
  rewrite TG in CMDm. cbv beta iota delta [negb andb] in CMDm.
  (* 146ec: bnez s9,14754 -- a keepalive: cmds = f.ncmds *)
  step.
  rewrite eqb_lit by (pose proof (io_b2z_range kaV); lia).
  destruct kaV.
  { change (b2z true =? 0) with false. cbv beta iota delta [negb].
    cbv beta iota in CMDm. injection CMDm as CM.
    eapply CONT. rewrite <- CM, io_swrap32_small by lia. reflexivity. }
  change (b2z false =? 0) with true. cbv beta iota delta [negb].
  cbv beta iota in CMDm.
  (* 146f0: li s4,0 ; 146f4: beqz s3,14754 -- no body: cmds = 0 *)
  step. step.
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (fr_body_len frame) 0) as [BL0|BLN]; cbv iota.
  { pose proof (io_cl_end (S (Z.to_nat (fr_body_len frame))) (set_g_fail_next B 0) (skipn (Z.to_nat 30) frame)
                  (fr_body_len frame) 0 0 cmdsM ltac:(lia) CMDm) as CM.
    eapply CONT. rewrite CM. reflexivity. }
  (* 146f8: li a0,0 ; 146fc: lw a1,16(s6) -- g_ncmd ; 14700-14710: a2 = 3, a3 = TAG, a4 = 40, a5 = &g_cmd *)
  step. step.
  change (s32_at (set_g_fail_next B 0) 64984) with (bv_swrap 32 (g_ncmd (set_g_fail_next B 0))).
  do 5 step.
  pose proof (u_at_range (set_g_fail_next B 0) OFF_g_ncmd 4) as RNQ.
  change (u_at (set_g_fail_next B 0) OFF_g_ncmd 4) with (g_ncmd (set_g_fail_next B 0)) in RNQ.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RNQ.
  (* ---- 14714-14750: the command count loop (:859-862), tagged_of (:609-615) inlined ---- *)
  assert (LOOP : forall (fuel : nat) (pos cmds : Z)
                   (wra wt0 wt1 wt2 wa0 wa5 wa6 wa7 ws4 wt3 wt4 wt5 wt6 : word),
    0 <= pos < fr_body_len frame -> 0 <= cmds < 2 ^ 32 ->
    wa0 = Z_to_bv 64 pos -> ws4 = Z_to_bv 64 (bv_swrap 32 cmds) -> wa5 = Z_to_bv 64 226648 ->
    cmds_loop fuel (set_g_fail_next B 0) (skipn (Z.to_nat 30) frame) (fr_body_len frame) pos cmds = Some cmdsM ->
    evt rsegs QQ
      (MS (mkR wra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp wt0 wt1 wt2
               (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
               wa0 (Z_to_bv 64 (bv_swrap 32 (g_ncmd (set_g_fail_next B 0)))) (Z_to_bv 64 3) (Z_to_bv 64 160)
               (Z_to_bv 64 40) wa5 wa6 wa7
               (Z_to_bv 64 (p + 30)) (Z_to_bv 64 (fr_body_len frame)) ws4
               (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704) (Z_to_bv 64 (fr_send frame))
               (Z_to_bv 64 (fr_cmd frame)) (Z_to_bv 64 (b2z false)) (Z_to_bv 64 (fr_cmd frame)) s11
               wt3 wt4 wt5 wt6)
          F (Z_to_bv 64 83740) fc None m4 (seg_rom rsegs))).
  { induction fuel as [|fuel IH];
      intros pos cmds wra wt0 wt1 wt2 wa0 wa5 wa6 wa7 ws4 wt3 wt4 wt5 wt6 HP HC E0 E4 E5 CL; [discriminate CL|].
    subst wa0 ws4 wa5.
    destruct (io_cl_step fuel (set_g_fail_next B 0) (skipn (Z.to_nat 30) frame) (fr_body_len frame) pos cmds cmdsM
                ltac:(lia) CL) as (Bt & t & TOm & SNZ & CL').
    pose proof (io_tof_keep _ _ _ _ _ TOm) as [EBt Ht]. subst Bt.
    set (b := skipn (Z.to_nat pos) (skipn (Z.to_nat 30) frame)) in *.
    assert (LBb : (Z.to_nat (fr_body_len frame - pos) <= length b)%nat) by (unfold b; rewrite !length_skipn; lia).
    assert (AB : forall k, at8 b k = at8 frame (Z.to_nat (30 + pos) + k)).
    { intros k. unfold b. rewrite !at8_skipn. f_equal. lia. }
    (* 14748, the end of a round: a6 = the step, the command's length or the rest of the body (:861) *)
    assert (TAIL : forall (stp : Z) (xt0 xa6 xa7 : word),
      stp = match t with Some s => Cmd_len (set_g_fail_next B 0) s | None => fr_body_len frame - pos end ->
      xa6 = Z_to_bv 64 stp ->
      evt rsegs QQ
        (MS (mkR wra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp xt0 wt1 wt2
                 (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
                 (Z_to_bv 64 pos) (Z_to_bv 64 (bv_swrap 32 (g_ncmd (set_g_fail_next B 0)))) (Z_to_bv 64 3)
                 (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 226648) xa6 xa7
                 (Z_to_bv 64 (p + 30)) (Z_to_bv 64 (fr_body_len frame)) (Z_to_bv 64 (bv_swrap 32 cmds))
                 (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704) (Z_to_bv 64 (fr_send frame))
                 (Z_to_bv 64 (fr_cmd frame)) (Z_to_bv 64 (b2z false)) (Z_to_bv 64 (fr_cmd frame)) s11
                 wt3 wt4 wt5 wt6)
            F (Z_to_bv 64 83792) fc None m4 (seg_rom rsegs))).
    { intros stp xt0 xa6 xa7 Estp E6. subst xa6.
      assert (RS : 0 < stp < 2 ^ 16).
      { destruct t as [s|]; cbv beta iota in Estp, SNZ.
        - pose proof (u_at_range (set_g_fail_next B 0) (A_Cmd_len s) 1) as RCL0.
          change (u_at (set_g_fail_next B 0) (A_Cmd_len s) 1) with (Cmd_len (set_g_fail_next B 0) s) in RCL0.
          change (2 ^ (8 * Z.of_nat 1)) with 256 in RCL0. lia.
        - lia. }
      rewrite <- Estp in CL'.
      (* 14748: add a0,a6,a0 *)
      step. rewrite ?(unsigned_lit stp), ?(unsigned_lit pos) by lia.
      (* 1474c: addiw s4,s4,1 *)
      step. rewrite io_addiw_sw.
      (* 14750: bltu a0,s3,14714 *)
      step. rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (stp + pos) (fr_body_len frame)) as [LT|GE]; cbv iota.
      - eapply (IH (pos + stp) (u32 (cmds + 1)));
          [ lia | unfold u32; apply Z.mod_pos_bound; lia | f_equal; lia | reflexivity | reflexivity | exact CL' ].
      - pose proof (io_cl_end fuel (set_g_fail_next B 0) (skipn (Z.to_nat 30) frame) (fr_body_len frame)
                      (pos + stp) (u32 (cmds + 1)) cmdsM ltac:(lia) CL') as CM.
        eapply CONT. rewrite CM. reflexivity. }
    (* 14714: sub a6,s3,a0 *)
    step. rewrite ?(unsigned_lit (fr_body_len frame)), ?(unsigned_lit pos) by lia.
    (* 14718: bltu a6,a2,14748 -- fewer than 3 bytes: tagged_of answers NULL (:611) *)
    step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (fr_body_len frame - pos) 3) as [L3|G3]; cbv iota.
    { rewrite (io_tof_short _ b _ L3) in TOm.
      assert (Et : t = None) by congruence. subst t.
      eapply (TAIL (fr_body_len frame - pos)); reflexivity. }
    (* 1471c: add a7,s2,a0 *)
    step. rewrite ?(unsigned_lit (p + 30)), ?(unsigned_lit pos) by lia.
    try replace (p + 30 + pos) with (p + (30 + pos)) by lia.
    (* 14720: lbu t0,0(a7) -- b[0] *)
    pose proof (rd_sub m4 p frame (30 + pos) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_val by (apply length_sub; lia).
    rewrite (ble_sub1 frame (30 + pos) (Z.to_nat (30 + pos) + 0) ltac:(lia) ltac:(lia)), <- (AB 0%nat).
    pose proof (at8_range b 0) as RB0. pose proof (at8_range b 1) as RB1. pose proof (at8_range b 2) as RB2.
    (* 14724: bne t0,a3,14748 -- not a tagged command: tagged_of answers NULL (:611-612) *)
    step. rewrite eqb_lit by lia.
    destruct (Z.eqb_spec (at8 b 0) 160) as [T0|T0]; cbv beta iota delta [negb].
    2: { rewrite (io_tof_notag (set_g_fail_next B 0) b (fr_body_len frame - pos) ltac:(lia) ltac:(lia)
                    ltac:(unfold TAG; lia)) in TOm.
         assert (Et : t = None) by congruence. subst t.
         eapply (TAIL (fr_body_len frame - pos)); reflexivity. }
    (* 14728: lbu t0,2(a7) ; 1472c: lbu a7,1(a7) -- b[2], b[1] *)
    pose proof (rd_sub m4 p frame (30 + pos + 2) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_val by (apply length_sub; lia).
    rewrite (ble_sub1 frame (30 + pos + 2) (Z.to_nat (30 + pos) + 2) ltac:(lia) ltac:(lia)), <- (AB 2%nat).
    pose proof (rd_sub m4 p frame (30 + pos + 1) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. clear RD. rewrite lbu_val by (apply length_sub; lia).
    rewrite (ble_sub1 frame (30 + pos + 1) (Z.to_nat (30 + pos) + 1) ltac:(lia) ltac:(lia)), <- (AB 1%nat).
    (* 14730: slli t0,t0,7 ; 14734: or a7,t0,a7 -- the serial (:613) *)
    step. rewrite ?(unsigned_lit (at8 b 2)) by lia.
    step. rewrite ?(unsigned_lit (Z.shiftl (at8 b 2) 7)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite ?(unsigned_lit (at8 b 1)) by lia.
    rewrite (Z.lor_comm (Z.shiftl (at8 b 2) 7) (at8 b 1)).
    assert (RSer : 0 <= Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) < 2 ^ 15).
    { apply lor_lt_pow2; [lia | rewrite Z.shiftl_mul_pow2 by lia; lia]. }
    rewrite (io_tof_tag (set_g_fail_next B 0) b (fr_body_len frame - pos) ltac:(lia) ltac:(lia)
               ltac:(unfold TAG; lia)) in TOm.
    set (serial := Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7)) in *.
    (* 14738: bgeu a7,a1,14748 -- serial >= g_ncmd: tagged_of answers NULL (:614) *)
    step. rewrite io_ltu_ncmd by lia.
    destruct (Z.ltb_spec serial (g_ncmd (set_g_fail_next B 0))) as [LN|GN]; cbv beta iota delta [negb].
    2: { try (replace (serial <? g_ncmd (set_g_fail_next B 0)) with false in TOm
                by (symmetry; apply Z.ltb_ge; lia)).
         cbv beta iota in TOm.
         assert (Et : t = None) by congruence. subst t.
         eapply (TAIL (fr_body_len frame - pos)); reflexivity. }
    try (replace (serial <? g_ncmd (set_g_fail_next B 0)) with true in TOm by (symmetry; apply Z.ltb_lt; lia)).
    cbv beta iota in TOm.
    destruct (CMDS_MAX <=? serial) eqn:CMX; try rewrite CMX in TOm; cbv beta iota in TOm; [discriminate TOm|].
    assert (Et : t = Some serial) by congruence. subst t.
    apply (proj1 (Z.leb_gt _ _)) in CMX. unfold CMDS_MAX in CMX.
    (* 1473c: mul a6,a7,a4 ; 14740: add a6,a5,a6 ; 14744: lbu a6,36(a6) -- t->len (:861) *)
    step. rewrite ?(unsigned_lit serial), ?(unsigned_lit 40) by lia.
    step. rewrite ?(unsigned_lit 226648), ?(unsigned_lit (serial * 40)) by lia.
    assert (RCL : ov_read_bytes rsegs m4 (Z_to_bv 64 (226648 + serial * 40 + 36)) 1
                  = Some (sub (set_g_fail_next B 0) (A_Cmd_len serial) 1)).
    { apply (wm_read rsegs W_BASE_PLAIN m4 (set_g_fail_next B 0) (A_Cmd_len serial) 1);
        [ exact WMEM4 | unfold A_Cmd_len, OFF_g_cmd; lia | unfold A_Cmd_len, OFF_g_cmd, W_LEN; lia
        | unfold A_Cmd_len, OFF_g_cmd, W_BASE_PLAIN; f_equal; lia ]. }
    step. clear RCL. rewrite ?wm_lbu.
    eapply (TAIL (Cmd_len (set_g_fail_next B 0) serial)); [ reflexivity | ].
    first [ reflexivity | (f_equal; unfold Cmd_len, A_Cmd_len, OFF_g_cmd; f_equal; lia) ]. }
  eapply (LOOP (S (Z.to_nat (fr_body_len frame))) 0 0);
    [ lia | lia | reflexivity | reflexivity | io_regeq | exact CMDm ].
Qed.
